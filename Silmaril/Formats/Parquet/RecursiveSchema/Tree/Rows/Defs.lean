module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Projection.Defs

/-! Checked native row groups over original leading-LIST signed leaf
carriers. Binding and reading follow physical order before joining rows. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows

open Occurrences (Boundary Tape Fault)
open Arrow.RecursiveSchema.Batch.Rows (Observation)

@[expose] public section

structure Limits where
  chunk : ListPath.Chunk.Limits := {}
  maxColumns : Nat := 1024
  maxSlots : Nat := 8 * 1024 * 1024

inductive InputError where
  | group (ordinal : Nat)
  | rowCount (group : Nat) (actual : Int)
  | columns (group expected actual : Nat)
  | columnLimit (group actual : Nat)
  | rowLimit (group actual : Nat)
  | slotLimit (group actual : Nat)
  | leaf (column : Nat) (cause : LeafError)
  deriving DecidableEq, Repr

inductive Error where
  | input (cause : InputError)
  | join (cause : Fault)
  deriving DecidableEq, Repr

def declaredSlots (group : Footer.RowGroup) : Nat :=
  group.columns.foldl (fun total column => total + column.metadata.numValues.toNat) 0

structure Admitted {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled schemaLimits snapshot) (limits : Limits) (group : Nat) where
  value : Footer.RowGroup
  original : snapshot.groupAt group = some value
  width : value.columns.length = compiled.leaves.size
  columnLimit : compiled.leaves.size ≤ limits.maxColumns
  nonnegative : 0 ≤ value.numRows
  rowLimit : value.numRows.toNat ≤ limits.chunk.maxRows
  slotLimit : declaredSlots value ≤ limits.maxSlots

structure CheckedColumn {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled schemaLimits snapshot) (caps : ListPath.Chunk.Limits) (group : Nat) where
  ordinal : Nat
  binding : LeafBinding compiled group ordinal
  original : ListPath.Chunk.Observation
  read : binding.read caps = .ok original

def CheckedColumn.tape {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {caps : ListPath.Chunk.Limits} {group : Nat}
    (column : CheckedColumn compiled caps group) : Tape :=
  Tape.ofRead column.binding.carrier column.original

/-- A slot coordinate is checked by its physical column and cumulative
slot index. A terminal coordinate is the original chunk end. -/
def originalBoundary (columns : Array Tape) (boundary : Boundary) : Prop :=
  match columns[boundary.point.column.column]? with
  | none => False
  | some tape =>
    match boundary with
    | .slot point => (tape.slots[point.slot]?.map (·.point)) = some point
    | .end point => tape.finish = point

instance (columns : Array Tape) (boundary : Boundary) : Decidable (originalBoundary columns boundary) := by
  unfold originalBoundary
  split
  · infer_instance
  · split <;> infer_instance

def originalFault (columns : Array Tape) : Fault → Prop
  | .presence _ _ left right expected actual =>
    originalBoundary columns left ∧ originalBoundary columns right ∧ expected ≠ actual
  | .cardinality _ _ present absent =>
    originalBoundary columns present ∧ originalBoundary columns absent
  | .atom _ _ point => originalBoundary columns point
  | _ => True

instance (columns : Array Tape) (fault : Fault) : Decidable (originalFault columns fault) := by
  cases fault <;> unfold originalFault <;> infer_instance

def slotCount (columns : Array Tape) : Nat :=
  columns.foldl (fun total tape => total + tape.slots.size) 0

structure Joined (widths : Array Nat) (slotBudget depth : Nat) (fields : List Repeated.Field)
    (requested : Nat) (columns : Array Tape) (out : Observation) : Prop where
  bounded : slotCount columns ≤ slotBudget
  rows : out.rows.length = requested
  rowCount : out.rowCount = requested
  exact : Projection.trace widths columns.size depth fields out.rows = some (columns.map Tape.atoms)

def tapes {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked} {compiled : Compiled schemaLimits snapshot}
    {caps : ListPath.Chunk.Limits} {group : Nat} (inputs : List (CheckedColumn compiled caps group)) : Array Tape :=
  (inputs.map CheckedColumn.tape).toArray

def schemaWidths {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked} (compiled : Compiled schemaLimits snapshot) :
    Array Nat := Occurrences.widths compiled.declarations.length compiled.leaves

structure GroupResult {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled schemaLimits snapshot) (limits : Limits) (group : Nat) where
  admission : Admitted compiled limits group
  inputs : List (CheckedColumn compiled limits.chunk group)
  observation : Observation
  exact : Joined (schemaWidths compiled) limits.maxSlots schemaLimits.maxSchemaDepth compiled.schema.fields
    admission.value.numRows.toNat (tapes inputs) observation

end

private def guard (condition : Prop) [Decidable condition] (error : InputError) : Except InputError (PLift condition) :=
  if valid : condition then .ok ⟨valid⟩ else .error error

public def admit {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled schemaLimits snapshot) (limits : Limits) (group : Nat) :
    Except InputError (Admitted compiled limits group) := do
  match original : snapshot.groupAt group with
  | none => throw (.group group)
  | some value =>
    let width := compiled.leaves.size
    let ⟨columns⟩ ← guard (value.columns.length = width) (.columns group width value.columns.length)
    let ⟨columnLimit⟩ ← guard (width ≤ limits.maxColumns) (.columnLimit group width)
    let ⟨nonnegative⟩ ← guard (0 ≤ value.numRows) (.rowCount group value.numRows)
    let ⟨rowLimit⟩ ← guard (value.numRows.toNat ≤ limits.chunk.maxRows) (.rowLimit group value.numRows.toNat)
    let slots := declaredSlots value
    let ⟨slotLimit⟩ ← guard (slots ≤ limits.maxSlots) (.slotLimit group slots)
    return ⟨value, original, columns, columnLimit, nonnegative, rowLimit, slotLimit⟩

@[expose] public def OpenColumn {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled schemaLimits snapshot) (group : Nat) :=
  (column : Nat) × LeafBinding compiled group column

@[expose] public def bindOriginal {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled schemaLimits snapshot) (group column : Nat) : Except InputError (OpenColumn compiled group) := do
  return ⟨column, ← (bindLeaf compiled group column).mapError (.leaf column)⟩

@[expose] public def readOriginal {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {compiled : Compiled schemaLimits snapshot} {group : Nat}
    (caps : ListPath.Chunk.Limits) (bound : OpenColumn compiled group) : Except InputError (CheckedColumn compiled caps group) :=
  match read : bound.2.read caps with
  | .ok original => .ok ⟨bound.1, bound.2, original, read⟩
  | .error cause => .error (.leaf bound.1 (.chunk cause))

@[expose] public def readColumns {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled schemaLimits snapshot) (caps : ListPath.Chunk.Limits) (group : Nat) :
    Except InputError (List (CheckedColumn compiled caps group)) := do
  let bindings ← (List.range compiled.leaves.size).mapM (bindOriginal compiled group)
  bindings.mapM (readOriginal caps)

/-- Checked reconstruction uses equality of the full ordered atom arrays,
including repetitions, definitions, and exact signed words. -/
@[expose] public def join (widths : Array Nat) (slotBudget depth : Nat) (fields : List Repeated.Field)
    (requested : Nat) (columns : Array Tape) :
    Except {fault // originalFault columns fault} {out // Joined widths slotBudget depth fields requested columns out} :=
  if bounded : slotCount columns ≤ slotBudget then
    match Occurrences.assemble widths slotBudget depth fields requested columns with
    | .error fault =>
      if valid : originalFault columns fault then .error ⟨fault, valid⟩ else .error ⟨.provenance, trivial⟩
    | .ok rows =>
      if count : rows.length = requested then
        if exact : Projection.trace widths columns.size depth fields rows = some (columns.map Tape.atoms) then
          .ok ⟨⟨requested, rows⟩, bounded, count, rfl, exact⟩
        else .error ⟨.projection, trivial⟩
      else .error ⟨.rows requested rows.length, trivial⟩
  else .error ⟨.slots (slotCount columns), trivial⟩

@[expose] public def readGroupChecked {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled schemaLimits snapshot) (limits : Limits) (group : Nat) :
    Except Error (GroupResult compiled limits group) := do
  let admission ← (admit compiled limits group).mapError .input
  let inputs ← (readColumns compiled limits.chunk group).mapError .input
  let ⟨observation, exact⟩ ← (join (schemaWidths compiled) limits.maxSlots schemaLimits.maxSchemaDepth
    compiled.schema.fields admission.value.numRows.toNat (tapes inputs)).mapError (Error.join ∘ Subtype.val)
  return ⟨admission, inputs, observation, exact⟩

@[expose] public def readGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (compiled : Compiled schemaLimits snapshot) (limits : Limits) (group : Nat) : Except Error Observation :=
  (readGroupChecked compiled limits group).map GroupResult.observation

end Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows
