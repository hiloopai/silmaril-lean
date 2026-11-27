module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.Defs
public import Init.Data.Vector.OfFn

/-! Ordered selected modern TIMESTAMP columns as dependent Arrow Events. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Projection

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)
open Leaf.ScalarAndDictionary.WithV1

structure Limits where
  input : Events.ToIpc.Limits := {}
  codec : ScalarAndDictionary.Limits := {}
  maxFields : Nat := 64

inductive Error where
  | fileByteLimit (maximum actual : Nat)
  | fieldLimit (maximum actual : Nat)
  | snapshot (cause : Snapshot.Error Unit)
  | groupLimit (maximum actual : Nat)
  | fileRowLimit (maximum actual : Nat)
  | bind (position ordinal : Nat) (cause : Leaf.Error)
  | groupIndex (group : Nat)
  | groupRowLimit (group maximum actual : Nat)
  | read (group position ordinal : Nat) (cause : AllCodecs.GroupError)
  | rowCount (group position ordinal expected actual : Nat)
  deriving DecidableEq, Repr

structure BoundTo (snapshot : Snapshot.Checked) where
  val : Leaf.Bound
  sameSnapshot : val.snapshot = snapshot
  modern : ∃ limits ordinal, Leaf.bind limits snapshot ordinal = .ok val

/-- Ordinals retain their original bindings into one snapshot. -/
structure Checked where
  snapshot : Snapshot.Checked
  width : Nat
  bindings : Fin width → BoundTo snapshot

def Checked.column (checked : Checked) (position : Fin checked.width) : Leaf.Bound :=
  (checked.bindings position).val

abbrev Checked.schema (checked : Checked) : Scan.Schema String Events.Kind :=
  ⟨checked.width, fun position => (Events.schema (checked.column position)).kind ⟨0, Nat.zero_lt_one⟩⟩

theorem bound_snapshot {limits : Footer.Limits} {snapshot : Snapshot.Checked} {ordinal : Nat}
    {bound : Leaf.Bound} (accepted : Leaf.bind limits snapshot ordinal = .ok bound) :
    bound.snapshot = snapshot := by
  have observed := Leaf.bind_observation limits snapshot ordinal
  rw [accepted] at observed
  cases result : Leaf.Internal.bindSelection limits snapshot ordinal with
  | error cause => simp [Except.map, result] at observed
  | ok selection =>
    simp only [Except.map, result, Except.ok.injEq] at observed
    exact congrArg Prod.fst observed

def bindAt (snapshot : Snapshot.Checked) (limits : Footer.Limits) (position ordinal : Nat) :
    Except Error (BoundTo snapshot) :=
  match result : Leaf.bind limits snapshot ordinal with
  | .ok bound => .ok ⟨bound, bound_snapshot result, ⟨limits, ordinal, result⟩⟩
  | .error cause => .error (.bind position ordinal cause)

/-- Root index zero is reserved. Repetition and empty requests are allowed. -/
def bindOrdinals (snapshot : Snapshot.Checked) (limits : Footer.Limits) (ordinals : Array Nat) :
    Except Error (Vector (BoundTo snapshot) ordinals.size) :=
  Vector.ofFnM fun position => bindAt snapshot limits position.val ordinals[position.val]

def openFile (limits : Limits) (input : Bytes) (ordinals : Array Nat) : Except Error Checked :=
  if limits.input.maxFileBytes < input.length then
    .error (.fileByteLimit limits.input.maxFileBytes input.length)
  else if limits.maxFields < ordinals.size then .error (.fieldLimit limits.maxFields ordinals.size)
  else do
    let snapshot ← (Snapshot.check limits.input.snapshot input).mapError .snapshot
    let rows := snapshot.metadata.numRows.toNat
    if limits.input.maxGroups < snapshot.groupCount then
      .error (.groupLimit limits.input.maxGroups snapshot.groupCount)
    else if limits.input.maxTotalRows < rows then .error (.fileRowLimit limits.input.maxTotalRows rows)
    else
      let columns ← bindOrdinals snapshot limits.input.snapshot.footer ordinals
      return ⟨snapshot, ordinals.size, fun position => columns[position.val]⟩

/-- Select and reorder already checked bindings. Only these positions contribute reads. -/
abbrev Checked.project (checked : Checked) (projection : Scan.Projection checked.schema) : Checked :=
  ⟨checked.snapshot, projection.width, checked.bindings ∘ projection.index⟩

/-- The logical column projection at the schema of the physically selected bindings. -/
abbrev Checked.projectBatch (checked : Checked) (projection : Scan.Projection checked.schema)
    (batch : Scan.Columns checked.schema Events.Cell) :
    Scan.Columns (checked.project projection).schema Events.Cell :=
  projection.projectColumns batch

def Checked.indices (checked : Checked) : List Nat := List.range checked.snapshot.groupCount

def Checked.groupRows (checked : Checked) (limits : Limits) (group : Nat) : Except Error Nat := do
  let some original := checked.snapshot.groupAt group | throw (.groupIndex group)
  let rows := original.numRows.toNat
  if limits.input.leaf.maxRows < rows then throw (.groupRowLimit group limits.input.leaf.maxRows rows)
  return rows

abbrev Counts (rows : Nat) := { values : List (Option Int) // values.length = rows }

/-- Read the original column with its own descriptor and check the shared footer row count. -/
def Checked.readCounts (checked : Checked) (limits : Limits) (group rows : Nat) (position : Fin checked.width) :
    Except Error (Counts rows) := do
  let bound := checked.column position
  let slots ← (AllCodecs.readGroup limits.codec limits.input.leaf bound group).mapError
    (.read group position.val bound.ordinal)
  let counts := slots.map (Option.map Ticks.ticks)
  if aligned : counts.length = rows then return ⟨counts, aligned⟩
  else throw (.rowCount group position.val bound.ordinal rows counts.length)

/-- Tag each exact signed count with the metadata at its output position. -/
def cells (kind : Events.Kind) (counts : List (Option Int)) : List (Option (Events.Cell kind)) :=
  counts.map (Option.map fun ticks => ⟨ticks⟩)

def Checked.readGroup (checked : Checked) (limits : Limits) (group : Nat) :
    Except Error (Scan.Columns checked.schema Events.Cell) := do
  let rows ← checked.groupRows limits group
  let columns ← Vector.ofFnM (checked.readCounts limits group rows)
  return
    { rowCount := rows
      values := fun position => cells (checked.schema.kind position).2 (columns[position.val]).val
      length_eq := fun position => by
        rw [cells, List.length_map]
        exact (columns[position.val]).property }

abbrev Trace (checked : Checked) := Arrow.Events.Trace checked.schema Events.Cell Error

/-- An error ends the trace after the last complete group. -/
def Checked.traceGroups (checked : Checked) (limits : Limits) : List Nat → Trace checked
  | [] => ⟨[], .eos⟩
  | group :: rest =>
    match checked.readGroup limits group with
    | .error cause => ⟨[], .readError cause⟩
    | .ok batch =>
      let tail := checked.traceGroups limits rest
      ⟨batch :: tail.batches, tail.termination⟩

def Checked.trace (checked : Checked) (limits : Limits) : Trace checked :=
  checked.traceGroups limits checked.indices

/-- A source that opens emits its schema even if its first group fails. -/
def readAll (limits : Limits) (input : Bytes) (ordinals : Array Nat) :
    Arrow.Events.EventStream String Events.Cell Error :=
  (openFile limits input ordinals).map fun checked => ⟨checked.schema, checked.trace limits⟩

end Silmaril.Formats.Parquet.Timestamp.Leaf.Projection
