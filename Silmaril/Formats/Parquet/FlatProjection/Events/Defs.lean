module

public import Silmaril.Formats.Parquet.FlatProjection.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Defs

/-! Ordered flat INT32, UTF8 and modern TIMESTAMP as typed Arrow Events. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatProjection.Events

open Silmaril.Relational
open Timestamp.Leaf.ScalarAndDictionary.WithV1

structure Limits where
  primitive : FlatProjection.Limits := {}
  timestamp : Timestamp.Leaf.Limits := {}
  codec : Timestamp.Leaf.ScalarAndDictionary.Limits := {}
  maxGroups : Nat := 4096

inductive Kind where
  | int32 (nullable : Bool)
  | utf8 (nullable : Bool)
  | timestamp (kind : Timestamp.Leaf.Events.Kind)

def Cell : Kind → Type
  | .int32 _ => Int32
  | .utf8 _ => String
  | .timestamp kind => Timestamp.Leaf.Events.Cell kind

inductive BindError where
  | primitive (cause : FlatProjection.BindError)
  | utf8 (cause : Plain.ByteArray.Utf8.Error)
  | timestamp (cause : Timestamp.Leaf.Error)
  deriving DecidableEq, Repr

inductive ColumnError where
  | int32 (cause : FlatColumn.Error FlatScan.AdapterError)
  | utf8 (cause : Plain.ByteArray.Utf8.Error)
  | timestamp (cause : AllCodecs.GroupError)
  deriving DecidableEq, Repr

inductive Error where
  | fileByteLimit (maximum actual : Nat)
  | fieldLimit (maximum actual : Nat)
  | snapshot (cause : Snapshot.Error Unit)
  | fileRowLimit (maximum actual : Nat)
  | groupLimit (maximum actual : Nat)
  | bind (position ordinal : Nat) (cause : BindError)
  | groupIndex (group : Nat)
  | groupRowLimit (group maximum actual : Nat)
  | column (group position ordinal : Nat) (cause : ColumnError)
  | rowCount (group position ordinal expected actual : Nat)
  deriving DecidableEq, Repr

inductive Bound (snapshot : Snapshot.Checked) where
  | int32 (name : String) (layout : FlatColumn.Layout)
      (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩)
  | utf8 (name : String) (layout : FlatColumn.Layout)
      (binding : FlatColumn.Binding snapshot ⟨name, .byteArray, layout⟩)
      (annotation : Plain.ByteArray.Utf8.Annotation)
  | timestamp (bound : Timestamp.Leaf.Projection.BoundTo snapshot)

def Bound.ordinal {snapshot : Snapshot.Checked} : Bound snapshot → Nat
  | .int32 name layout binding => (FlatProjection.Bound.int32 name layout binding).ordinal
  | .utf8 name layout binding _ => (FlatProjection.Bound.byteArray name layout binding).ordinal
  | .timestamp bound => bound.val.ordinal - 1

def Bound.field {snapshot : Snapshot.Checked} : Bound snapshot → String × Kind
  | .int32 name layout _ => (name, .int32 (layout.repetition == .optional))
  | .utf8 name layout _ _ => (name, .utf8 (layout.repetition == .optional))
  | .timestamp bound =>
    let field := (Timestamp.Leaf.Events.schema bound.val).kind ⟨0, Nat.zero_lt_one⟩
    (field.1, .timestamp field.2)

/-- Use the FlatProjection zero-based leaf ordinal. The TIMESTAMP binder
takes the corresponding original schema node index, with root at zero. -/
def bindOrdinal (limits : Footer.Limits) (snapshot : Snapshot.Checked) (ordinal : Nat) :
    Except BindError (Bound snapshot) :=
  if (snapshot.metadata.schema[ordinal + 1]?.bind (·.physicalType)) = some .int64 then
    match result : Timestamp.Leaf.bind limits snapshot (ordinal + 1) with
    | .error cause => .error (.timestamp cause)
    | .ok bound => .ok (.timestamp ⟨bound, Timestamp.Leaf.Projection.bound_snapshot result, ⟨limits, ordinal + 1, result⟩⟩)
  else do
    match ← (FlatProjection.bindOrdinal snapshot ordinal).mapError .primitive with
    | .int32 name layout binding => return .int32 name layout binding
    | .byteArray name layout binding =>
      let leaf ← (Footer.ColumnOrder.readFlat limits snapshot binding.columnOrdinal).mapError
        (.utf8 ∘ .footer)
      let annotation ← (Plain.ByteArray.Utf8.readAnnotation leaf).mapError .utf8
      return .utf8 name layout binding annotation

structure Checked where
  snapshot : Snapshot.Checked
  width : Nat
  bindings : Fin width → Bound snapshot

abbrev Checked.schema (checked : Checked) : Scan.Schema String Kind :=
  ⟨checked.width, Bound.field ∘ checked.bindings⟩

/-- Sequence the indexed column reads in order, retaining each result at its
own type and stopping at the first error. -/
def sequence {ε : Type} : {n : Nat} → {α : Fin n → Type} →
    ((i : Fin n) → Except ε (α i)) → Except ε ((i : Fin n) → α i)
  | 0, _, _ => .ok (fun i => i.elim0)
  | n + 1, _, read => do
    let first ← read 0
    let rest ← sequence (n := n) (fun i => read i.succ)
    return Fin.cases first rest

def bindAt (limits : Footer.Limits) (snapshot : Snapshot.Checked) (position ordinal : Nat) :
    Except Error (Bound snapshot) :=
  (bindOrdinal limits snapshot ordinal).mapError (.bind position ordinal)

/-- Repeated selections retain their positions. An empty selection still opens
the same checked file and retains its original groups and row counts. -/
def openFile (limits : Limits) (input : Bytes) (ordinals : Array Nat) : Except Error Checked := do
  let policy := limits.primitive
  if policy.column.maxFileBytes < input.length then
    throw (.fileByteLimit policy.column.maxFileBytes input.length)
  if policy.maxFields < ordinals.size then throw (.fieldLimit policy.maxFields ordinals.size)
  let snapshot ← (Snapshot.check policy.column.snapshot input).mapError .snapshot
  let rows := snapshot.metadata.numRows.toNat
  if policy.maxFileRows < rows then throw (.fileRowLimit policy.maxFileRows rows)
  if limits.maxGroups < snapshot.groupCount then throw (.groupLimit limits.maxGroups snapshot.groupCount)
  let columns ← sequence fun (i : Fin ordinals.size) =>
    bindAt policy.column.snapshot.footer snapshot i.val ordinals[i]
  return ⟨snapshot, ordinals.size, columns⟩

abbrev Checked.project (checked : Checked) (projection : Scan.Projection checked.schema) : Checked :=
  ⟨checked.snapshot, projection.width, checked.bindings ∘ projection.index⟩

abbrev Checked.projectBatch (checked : Checked) (projection : Scan.Projection checked.schema)
    (batch : Scan.Columns checked.schema Cell) : Scan.Columns (checked.project projection).schema Cell :=
  projection.projectColumns batch

/-- Each branch uses the existing selected-chunk path at its own type. UTF8
also checks each present value using the annotated STRING reader's decoder. -/
def Bound.read {snapshot : Snapshot.Checked} (limits : Limits) (group : Nat) :
    (bound : Bound snapshot) → Except ColumnError (List (Option (Cell bound.field.2)))
  | .int32 _ layout binding =>
    (FlatColumn.readColumn binding limits.primitive.column.column Plain.ByteArray.File.policy
      (Int32ByteArrayGroup.decodeInt32 limits.primitive.column layout) group).mapError .int32
  | .utf8 _ layout binding _ => do
    let raw ← (FlatColumn.readColumn binding limits.primitive.column.column Plain.ByteArray.File.policy
      (Int32ByteArrayGroup.decodeByteArray limits.primitive.column layout) group).mapError (.utf8 ∘ .physical)
    (Plain.ByteArray.Utf8.decodeSlots group raw).mapError .utf8
  | .timestamp bound =>
    (AllCodecs.readGroup limits.codec limits.timestamp bound.val group).map
      (List.map (Option.map fun ticks => ⟨ticks.ticks⟩)) |>.mapError .timestamp

def Checked.indices (checked : Checked) : List Nat := List.range checked.snapshot.groupCount

def Checked.groupRows (checked : Checked) (limits : Limits) (group : Nat) : Except Error Nat := do
  let some original := checked.snapshot.groupAt group | throw (.groupIndex group)
  let rows := original.numRows.toNat
  let maximum := limits.primitive.column.column.maxRows
  if maximum < rows then throw (.groupRowLimit group maximum rows)
  return rows

abbrev Column (kind : Kind) (rows : Nat) :=
  { values : List (Option (Cell kind)) // values.length = rows }

def Checked.readColumn (checked : Checked) (limits : Limits) (group rows : Nat)
    (position : Fin checked.width) : Except Error (Column (checked.schema.kind position).2 rows) := do
  let bound := checked.bindings position
  let values ← (bound.read limits group).mapError (.column group position.val bound.ordinal)
  if aligned : values.length = rows then return ⟨values, aligned⟩
  else throw (.rowCount group position.val bound.ordinal rows values.length)

def Checked.readGroup (checked : Checked) (limits : Limits) (group : Nat) :
    Except Error (Scan.Columns checked.schema Cell) := do
  let rows ← checked.groupRows limits group
  let columns ← sequence (checked.readColumn limits group rows)
  return ⟨rows, fun i => (columns i).val, fun i => (columns i).property⟩

abbrev Trace (checked : Checked) := Arrow.Events.Trace checked.schema Cell Error

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

def readAll (limits : Limits) (input : Bytes) (ordinals : Array Nat) :
    Arrow.Events.EventStream String Cell Error :=
  (openFile limits input ordinals).map fun checked => ⟨checked.schema, checked.trace limits⟩

end Silmaril.Formats.Parquet.FlatProjection.Events
