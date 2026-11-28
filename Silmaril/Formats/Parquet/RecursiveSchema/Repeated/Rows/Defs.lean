module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Projection.Defs

/-! Assemble signed recursive rows from original V1 chunks. Group admission
budgets the complete declared slot total before decoding any column. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows

open RecursiveSchema (Location)
open Repeated (Field)
open Arrow.RecursiveSchema.Batch.Rows (Cell Row RowFits CellFits Observation)

@[expose] public section

structure Limits where
  chunk : Chunk.Limits := {}
  maxColumns : Nat := 1024
  maxSlots : Nat := 8 * 1024 * 1024

structure Point where
  column : Chunk.Address
  page : Nat
  byte : Nat
  slot : Nat
  deriving DecidableEq, Repr

structure Addressed where
  point : Point
  atom : Atom
  deriving DecidableEq, Repr

structure Position where
  group : Nat
  row : Nat
  element : Option (Location × Nat) := none
  deriving DecidableEq, Repr

inductive Error where
  | groupOrdinal (group : Nat)
  | columnCount (group expected actual : Nat)
  | columnLimit (group width : Nat)
  | rowLimit (group rows : Nat)
  | slotLimit (group slots : Nat)
  | binding (original : Chunk.BindError)
  | chunk (original : Chunk.Error)
  | leadingContinuation (point : Point)
  | columnRows (column : Chunk.Address) (expected actual : Nat)
  | missingRow (position : Position) (column : Chunk.Address)
  | depth (position : Position)
  | shape (position : Position)
  | missing (position : Position) (site : Location) (column : Chunk.Address)
      (counterpart : Option Point)
  | extra (position : Position) (site : Location) (point : Point)
  | conflict (position : Position) (site : Location) (first other : Point)
  | presence (position : Position) (site : Location) (point : Point)
  | signedType (position : Position) (site : Location) (point : Point)
  | projection (position : Position)
  deriving DecidableEq, Repr

/-- Attach the local and absolute original coordinates before partitioning.
Page boundaries do not enter the row partition. -/
def addressed (column : Chunk.Address) (output : Chunk.Observation) : List Addressed :=
  output.pages.flatMap fun page =>
    (page.decoded.levels.zip page.decoded.words).zipIdx page.start.state.slot |>.map
      fun ((levels, word), slot) =>
        ⟨⟨column, page.start.page, page.frame.header.start, slot⟩, ⟨levels, word⟩⟩

def startsRow (slot : Addressed) : Bool := slot.atom.levels.startsRow

def partitionFrom : List Addressed → List (List Addressed) → List Addressed →
    Except Error (List (List Addressed))
  | [], closed, [] => .ok closed.reverse
  | [], closed, first :: rest => .ok ((first :: rest).reverse :: closed).reverse
  | slot :: tail, closed, active =>
    if startsRow slot then
      let closed := if active.isEmpty then closed else active.reverse :: closed
      partitionFrom tail closed [slot]
    else if active.isEmpty then .error (.leadingContinuation slot.point)
    else partitionFrom tail closed (slot :: active)

def partition (slots : List Addressed) : Except Error (List (List Addressed)) :=
  partitionFrom slots [] []

def RowSlice (slots : List Addressed) : Prop :=
  ∃ first rest, slots = first :: rest ∧ startsRow first = true ∧
    ∀ slot ∈ rest, startsRow slot = false

structure PartitionWire (slots : List Addressed) (rows : List (List Addressed)) : Prop where
  exact : rows.flatten = slots
  boundaries : ∀ row ∈ rows, RowSlice row

structure Column where
  address : Chunk.Address
  rows : Array (Array Addressed)

/-- A view into one original column row. An element view advances the
start by its ordinal and keeps one slot without copying the column. -/
structure Slice where
  address : Chunk.Address
  slots : Array Addressed
  start : Nat
  count : Nat

def Slice.at (slice : Slice) (index : Nat) : Option Addressed :=
  if index < slice.count then slice.slots[slice.start + index]? else none

def Slice.element (slice : Slice) (index : Nat) : Slice :=
  { slice with start := slice.start + index, count := 1 }

def Column.at (column : Column) (position : Position) : Except Error Slice :=
  match column.rows[position.row]? with
  | none => .error (.missingRow position column.address)
  | some slots => .ok ⟨column.address, slots, 0, slots.size⟩

/-- All the original atoms of a full row slice, in column slot order. -/
def Slice.atoms (slice : Slice) : List Atom :=
  (slice.slots.extract slice.start (slice.start + slice.count)).toList.map Addressed.atom

def Addressed.missingAt (slot : Addressed) (site : Location) : Bool :=
  match slot.atom.levels.classified.presence with
  | .absent (.optional original _) => decide (original = site)
  | _ => false

inductive ListState where
  | null
  | empty
  | live
  deriving DecidableEq

def Addressed.listState (slot : Addressed) (site : Location) : ListState :=
  if slot.missingAt site then .null
  else match slot.atom.levels.classified.presence with
    | .absent (.emptyList outer _) => if outer = site then .empty else .live
    | _ => .live

end

private structure CheckedCell (field : Field) where
  value : Cell
  fits : CellFits field.arrow value

private structure CheckedRow (fields : List Field) where
  value : Row
  fits : RowFits (fields.map Field.arrow) value

private def firstSlot (position : Position) (site : Location) (all : List Slice)
    (slice : Slice) : Except Error Addressed :=
  match slice.at 0 with
  | some slot => .ok slot
  | none =>
    let counterpart := all.findSome? (fun other => (other.at 0).map Addressed.point)
    .error (.missing position site slice.address counterpart)

private def agree {α : Type} [DecidableEq α] (position : Position) (site : Location)
    (meaning : Addressed → α) (inputs : List Slice) : Except Error α := do
  let first :: rest := inputs | throw (.shape position)
  let head ← firstSlot position site inputs first
  let wanted := meaning head
  for slice in rest do
    let other ← firstSlot position site inputs slice
    if meaning other ≠ wanted then
      throw (.conflict position site head.point other.point)
  return wanted

private def requireSingletons (position : Position) (site : Location) (inputs : List Slice) :
    Except Error Unit := do
  for slice in inputs do
    if let some extra := slice.at 1 then
      throw (.extra position site extra.point)

/-- Compare every common element before reporting a missing element.
Choosing the shortest slice also locates the first unmatched element
when more than two physical columns share the list. -/
private def commonLength (first : Slice) (rest : List Slice) : Nat :=
  rest.foldl (fun common slice => min common slice.count) first.count

private def requireLength (position : Position) (site : Location) (inputs : List Slice)
    (length : Nat) : Except Error Unit := do
  if let some longer := inputs.find? (fun slice => length < slice.count) then
    let some shorter := inputs.find? (fun slice => slice.count = length) | throw (.shape position)
    throw (.missing { position with element := some (site, length) } site shorter.address
      ((longer.at length).map Addressed.point))

private def assembleFields (position : Position)
    (assemble : (field : Field) → List Slice → Except Error (CheckedCell field)) :
    (fields : List Field) → List Slice → Except Error (CheckedRow fields)
  | [], [] => .ok ⟨[], .nil⟩
  | [], _ :: _ => .error (.shape position)
  | field :: rest, inputs => do
    let width := field.leaves.length
    let first ← assemble field (inputs.take width)
    let tail ← assembleFields position assemble rest (inputs.drop width)
    return ⟨first.value :: tail.value, .cons first.fits tail.fits⟩

private theorem elements_fit (field : Field) (elements : List (CheckedCell field)) :
    RowFits (List.replicate (elements.map CheckedCell.value).length field.arrow)
      (elements.map CheckedCell.value) := by
  induction elements with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.fits ih

private def assembleLeaf (position : Position) (plan : Repeated.Leaf) (inputs : List Slice) :
    Except Error (CheckedCell (.leaf plan)) := do
  let [slice] := inputs | throw (.shape position)
  let site := plan.site.location
  let slot ← firstSlot position site inputs slice
  requireSingletons position site inputs
  match slot.atom.levels.classified.presence, slot.atom.word with
  | .absent (.optional loc _), none =>
    if loc = site then
      if optional : plan.site.nullable = true then
        return ⟨none, by rw [Field.arrow, optional]; exact .null⟩
      else throw (.presence position site slot.point)
    else throw (.presence position site slot.point)
  | .value, some (.int32 word) =>
    if kind : plan.kind = .int32 then
      return ⟨some (.int32 word), by rw [Field.arrow, kind]; exact .int32⟩
    else throw (.signedType position site slot.point)
  | .value, some (.int64 word) =>
    if kind : plan.kind = .int64 then
      return ⟨some (.int64 word), by rw [Field.arrow, kind]; exact .int64⟩
    else throw (.signedType position site slot.point)
  | _, _ => throw (.presence position site slot.point)

private def assembleField :
    Nat → (position : Position) → (field : Field) → List Slice → Except Error (CheckedCell field)
  | 0, position, _, _ => .error (.depth position)
  | _ + 1, position, .leaf plan, inputs => assembleLeaf position plan inputs
  | depth + 1, position, .group site children, inputs => do
    let absent ← agree position site.location (·.missingAt site.location) inputs
    if absent then
      requireSingletons position site.location inputs
      if optional : site.nullable = true then
        return ⟨none, by rw [Field.arrow, optional]; exact .null⟩
      else
        let first :: _ := inputs | throw (.shape position)
        let slot ← firstSlot position site.location inputs first
        throw (.presence position site.location slot.point)
    else
      let row ← assembleFields position (assembleField depth position) children inputs
      return ⟨some (.struct row.value), by rw [Field.arrow]; exact .struct row.fits⟩
  | depth + 1, position, .list site _ element, inputs => do
    let state ← agree position site.location (·.listState site.location) inputs
    match state with
    | .null =>
      requireSingletons position site.location inputs
      if optional : site.nullable = true then
        return ⟨none, by rw [Field.arrow, optional]; exact .null⟩
      else
        let first :: _ := inputs | throw (.shape position)
        let slot ← firstSlot position site.location inputs first
        throw (.presence position site.location slot.point)
    | .empty =>
      requireSingletons position site.location inputs
      return ⟨some (.list []), by rw [Field.arrow]; exact .list .nil⟩
    | .live =>
      let first :: rest := inputs | throw (.shape position)
      let length := commonLength first rest
      let elements ← (List.range length).mapM fun index =>
        assembleField depth { position with element := some (site.location, index) }
          element (inputs.map (·.element index))
      requireLength position site.location inputs length
      return ⟨some (.list (elements.map CheckedCell.value)), by
        rw [Field.arrow]
        exact .list (elements_fit element elements)⟩

@[expose] public section

structure Assembled (depth : Nat) (fields : List Field) (input : List Slice) where
  row : Row
  typed : RowFits (fields.map Field.arrow) row
  projection : Projection.row depth fields row = some (input.map Slice.atoms)

end

/-- Independently check the positional inverse after assembling the row.
The inverse has no input evidence and restores the original level words. -/
public def assembleRow (depth : Nat) (position : Position) (fields : List Field) (input : List Slice) :
    Except Error (Assembled depth fields input) := do
  let assembled ← assembleFields position (assembleField depth position) fields input
  match projected : Projection.row depth fields assembled.value with
  | none => throw (.projection position)
  | some output =>
    if same : output == input.map Slice.atoms then
      return ⟨assembled.value, assembled.fits, projected.trans (congrArg some (eq_of_beq same))⟩
    else throw (.projection position)

@[expose] public section

def readColumn {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (group column : Nat) :
    Except Error Column := do
  let binding ← (Chunk.bindChunk schema group column limits).mapError .binding
  let output ← (Chunk.read limits binding).mapError .chunk
  let address : Chunk.Address := ⟨group, column, binding.leaf.site.location.path⟩
  let rows ← partition (addressed address output)
  if rows.length = binding.rowGroup.numRows.toNat then
    return ⟨address, (rows.map List.toArray).toArray⟩
  else throw (.columnRows address binding.rowGroup.numRows.toNat rows.length)

def readAt (depth group row : Nat) (fields : List Field) (columns : List Column) : Except Error Row := do
  let position : Position := ⟨group, row, none⟩
  let input ← columns.mapM (·.at position)
  return (← assembleRow depth position fields input).row

def slotTotal (rowGroup : Footer.RowGroup) : Nat :=
  rowGroup.columns.foldl (fun total column => total + column.metadata.numValues.toNat) 0

def admitGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) :
    Except Error Footer.RowGroup :=
  match snapshot.groupAt group with
  | none => .error (.groupOrdinal group)
  | some rowGroup =>
    let width := schema.leaves.size
    let rows := rowGroup.numRows.toNat
    if rowGroup.columns.length ≠ width then .error (.columnCount group width rowGroup.columns.length)
    else if width > limits.maxColumns then .error (.columnLimit group width)
    else if rows > limits.chunk.maxRows then .error (.rowLimit group rows)
    else
      let total := slotTotal rowGroup
      if total > limits.maxSlots then .error (.slotLimit group total)
      else .ok rowGroup

/-- Decode and partition every original column before aligning any row. -/
def readGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) :
    Except Error Observation := do
  let rowGroup ← admitGroup limits schema group
  let columns ← (List.range schema.leaves.size).mapM (readColumn limits.chunk schema group)
  let rows ← (List.range rowGroup.numRows.toNat).mapM
    (fun row => readAt (schemaLimits.maxSchemaDepth - 1) group row schema.fields columns)
  return ⟨rowGroup.numRows.toNat, rows⟩

def readAll {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) : Except Error (List Observation) :=
  (List.range snapshot.groupCount).mapM (readGroup limits schema)

def ColumnWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (group column : Nat)
    (result : Column) : Prop :=
  ∃ (binding : Chunk.Binding schema group column) (observed : Chunk.Observation)
    (rows : List (List Addressed)),
    Chunk.bindChunk schema group column limits = .ok binding ∧
    Chunk.read limits binding = .ok observed ∧ Chunk.Wire limits binding observed ∧
    result.address = ⟨group, column, binding.leaf.site.location.path⟩ ∧
    PartitionWire (addressed result.address observed) rows ∧
    rows.length = binding.rowGroup.numRows.toNat ∧
    result.rows = (rows.map List.toArray).toArray

def RowWire (depth : Nat) (position : Position) (fields : List Field) (columns : List Column)
    (result : Row) : Prop :=
  ∃ input, List.Forall₂ (fun column slice => column.at position = .ok slice) columns input ∧
    RowFits (fields.map Field.arrow) result ∧
    Projection.row depth fields result = some (input.map Slice.atoms)

structure GroupWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) (group : Nat)
    (result : Observation) : Prop where
  original : ∃ rowGroup columns,
    snapshot.groupAt group = some rowGroup ∧ rowGroup.columns.length = schema.leaves.size ∧
    slotTotal rowGroup ≤ limits.maxSlots ∧ result.rowCount = rowGroup.numRows.toNat ∧
    List.Forall₂ (ColumnWire limits.chunk schema group) (List.range schema.leaves.size) columns ∧
    List.Forall₂ (fun index row =>
      RowWire (schemaLimits.maxSchemaDepth - 1) ⟨group, index, none⟩ schema.fields columns row)
      (List.range rowGroup.numRows.toNat) result.rows
  count : result.rows.length = result.rowCount
  typed : ∀ row ∈ result.rows, RowFits schema.arrow.fields row

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows
