module

public import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs

/-! Checked positional row assembly of non-repeated recursive Parquet leaves.
Column pages have already been decoded from their original snapshot. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Rows

open Arrow.RecursiveSchema.Batch.Rows (Cell Row Observation CellFits RowFits)

@[expose] public section

structure Limits where
  chunk : Chunk.Limits := {}
  maxColumns : Nat := 1024
  maxSlots : Nat := 8 * 1024 * 1024

structure ColumnLocation where
  ordinal : Nat
  path : List String
  deriving DecidableEq, Repr

structure Evidence where
  column : ColumnLocation
  slot : Chunk.Slot

structure Column where
  location : ColumnLocation
  slots : Array Chunk.Slot

inductive Error where
  | groupOrdinal (group : Nat)
  | columnCount (group expected actual : Nat)
  | columnLimit (group width : Nat)
  | rowLimit (group rows : Nat)
  | slotLimit (group rows width : Nat)
  | binding (original : ChunkError)
  | chunk (original : Chunk.Error)
  | missingRow (group row : Nat) (column : ColumnLocation)
  | missingSlots (group row : Nat) (location : Location)
  | excessSlots (group row count : Nat)
  | depth (group row : Nat)
  | sibling (group row : Nat) (location : Location) (first conflicting : ColumnLocation)
  | presence (group row : Nat) (location : Location) (column : ColumnLocation)
  | type (group row : Nat) (location : Location) (column : ColumnLocation)
  deriving DecidableEq, Repr

mutual

/-- The ordered projection of a logical cell to its original leaf slots.
An absent group projects its location to every descendant position. -/
inductive CellProjection : Field → Cell → List Chunk.Slot → Prop where
  | int32 {plan word} : plan.kind = .int32 →
      CellProjection (.leaf plan) (some (.int32 word)) [.value (.int32 word)]
  | int64 {plan word} : plan.kind = .int64 →
      CellProjection (.leaf plan) (some (.int64 word)) [.value (.int64 word)]
  | nullLeaf {plan} : plan.site.nullable = true →
      CellProjection (.leaf plan) none [.absent plan.site.location]
  | nullGroup {site children slots} : site.nullable = true →
      slots.length = (children.flatMap Field.leaves).length →
      (∀ slot ∈ slots, slot = .absent site.location) →
      CellProjection (.group site children) none slots
  | struct {site children cells slots} : RowProjection children cells slots →
      CellProjection (.group site children) (some (.struct cells)) slots

inductive RowProjection : List Field → Row → List Chunk.Slot → Prop where
  | nil : RowProjection [] [] []
  | cons {field tail cell cells first rest} :
      CellProjection field cell first →
      RowProjection tail cells rest →
      RowProjection (field :: tail) (cell :: cells) (first ++ rest)

end

structure Assembled (fields : List Field) (input : List Evidence) where
  row : Row
  fits : RowFits (fields.map Field.arrow) row
  projection : RowProjection fields row (input.map Evidence.slot)

def Evidence.missingAt (location : Location) (evidence : Evidence) : Bool :=
  decide (evidence.slot = .absent location)

end

private structure CellResult (field : Field) (input : List Evidence) where
  cell : Cell
  rest : List Evidence
  fits : CellFits field.arrow cell
  wire : ∃ used, input = used ++ rest ∧ CellProjection field cell (used.map Evidence.slot)

private structure FieldsResult (fields : List Field) (input : List Evidence) where
  row : Row
  rest : List Evidence
  fits : RowFits (fields.map Field.arrow) row
  wire : ∃ used, input = used ++ rest ∧ RowProjection fields row (used.map Evidence.slot)

private def assembleFields
    (assemble : (field : Field) → (input : List Evidence) → Except Error (CellResult field input)) :
    (fields : List Field) → (input : List Evidence) → Except Error (FieldsResult fields input)
  | [], input => .ok ⟨[], input, .nil, ⟨[], rfl, .nil⟩⟩
  | field :: fields, input => do
    let first ← assemble field input
    let tail ← assembleFields assemble fields first.rest
    return ⟨first.cell :: tail.row, tail.rest, .cons first.fits tail.fits, by
      obtain ⟨front, inputSplit, firstWire⟩ := first.wire
      obtain ⟨back, restSplit, restWire⟩ := tail.wire
      refine ⟨front ++ back, ?_, ?_⟩
      · calc
          input = front ++ first.rest := inputSplit
          _ = front ++ (back ++ tail.rest) := congrArg (front ++ ·) restSplit
          _ = _ := (List.append_assoc front back tail.rest).symm
      · rw [List.map_append]
        exact .cons firstWire restWire⟩


private def assembleLeaf (group row : Nat) (plan : Leaf) :
    (input : List Evidence) → Except Error (CellResult (.leaf plan) input)
  | [] => .error (.missingSlots group row plan.site.location)
  | item :: rest =>
    match source : item.slot with
    | .absent location =>
      if absent : location = plan.site.location then
        if nullable : plan.site.nullable = true then
          .ok ⟨none, rest, by rw [Field.arrow, nullable]; exact .null, by
            refine ⟨[item], rfl, ?_⟩
            simpa [source, absent] using (CellProjection.nullLeaf (plan := plan) nullable)⟩
        else .error (.presence group row plan.site.location item.column)
      else .error (.presence group row plan.site.location item.column)
    | .value (.int32 word) =>
      if kind : plan.kind = .int32 then
        .ok ⟨some (.int32 word), rest, by rw [Field.arrow, kind]; exact .int32, by
          refine ⟨[item], rfl, ?_⟩
          simpa [source] using (CellProjection.int32 (plan := plan) (word := word) kind)⟩
      else .error (.type group row plan.site.location item.column)
    | .value (.int64 word) =>
      if kind : plan.kind = .int64 then
        .ok ⟨some (.int64 word), rest, by rw [Field.arrow, kind]; exact .int64, by
          refine ⟨[item], rfl, ?_⟩
          simpa [source] using (CellProjection.int64 (plan := plan) (word := word) kind)⟩
      else .error (.type group row plan.site.location item.column)

private def assembleField (group row : Nat) :
    Nat → (field : Field) → (input : List Evidence) → Except Error (CellResult field input)
  | 0, _, _ => .error (.depth group row)
  | _ + 1, .leaf plan, input => assembleLeaf group row plan input
  | depth + 1, .group site children, input => do
    let width := (children.flatMap Field.leaves).length
    let descendants := input.take width
    if complete : descendants.length = width then
      let first :: _ := descendants | throw (.missingSlots group row site.location)
      let different := fun item : Evidence =>
        item.missingAt site.location != first.missingAt site.location
      match agreement : descendants.find? different with
      | some conflict => throw (.sibling group row site.location first.column conflict.column)
      | none =>
        if absent : first.slot = .absent site.location then
          if nullable : site.nullable = true then
            return ⟨none, input.drop width, by rw [Field.arrow, nullable]; exact .null, by
              refine ⟨descendants, (List.take_append_drop width input).symm, ?_⟩
              apply CellProjection.nullGroup nullable (by simpa only [List.length_map] using complete)
              intro slot member
              obtain ⟨item, found, rfl⟩ := List.mem_map.mp member
              have agreed := List.find?_eq_none.mp agreement item found
              simpa [different, Evidence.missingAt, absent] using agreed⟩
          else throw (.presence group row site.location first.column)
        else
          let elements ← assembleFields (assembleField group row depth) children input
          return ⟨some (.struct elements.row), elements.rest, by
            rw [Field.arrow]
            exact .struct elements.fits, by
              obtain ⟨used, split, projected⟩ := elements.wire
              exact ⟨used, split, .struct projected⟩⟩
    else throw (.missingSlots group row site.location)

/-- Assemble exactly the supplied original leaf positions of one row. -/
public def assembleRow (depth group row : Nat) (fields : List Field) (input : List Evidence) :
    Except Error (Assembled fields input) := do
  let assembled ← assembleFields (assembleField group row depth) fields input
  if finished : assembled.rest = [] then
    return ⟨assembled.row, assembled.fits, by
      obtain ⟨used, split, projected⟩ := assembled.wire
      rw [finished, List.append_nil] at split
      exact split.symm ▸ projected⟩
  else throw (.excessSlots group row assembled.rest.length)

@[expose] public section

/-- Keep the original row ordinal while indexing each independently
decoded column only once per row. -/
def evidenceAt (group row : Nat) (columns : List Column) : Except Error (List Evidence) :=
  columns.mapM fun column =>
    match column.slots[row]? with
    | some slot => .ok ⟨column.location, slot⟩
    | none => .error (.missingRow group row column.location)

def readColumn {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (group column : Nat) :
    Except Error Column := do
  let binding ← (bindChunk schema group column).mapError .binding
  let output ← (Chunk.read limits binding).mapError .chunk
  return ⟨⟨column, binding.leaf.site.location.path⟩, output.rows.toArray⟩

def readAt (depth group row : Nat) (fields : List Field) (columns : List Column) :
    Except Error Row := do
  let input ← evidenceAt group row columns
  return (← assembleRow depth group row fields input).row

def admitGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) :
    Except Error Footer.RowGroup :=
  match snapshot.groupAt group with
  | none => .error (.groupOrdinal group)
  | some rowGroup =>
    let rows := rowGroup.numRows.toNat
    let width := schema.leaves.size
    if rowGroup.columns.length ≠ width then .error (.columnCount group width rowGroup.columns.length)
    else if width > limits.maxColumns then .error (.columnLimit group width)
    else if rows > limits.chunk.maxRows then .error (.rowLimit group rows)
    else if rows * width > limits.maxSlots then .error (.slotLimit group rows width)
    else .ok rowGroup

/-- Decode every original physical column in order, including when the
group has zero rows. Each selected chunk checks its own independent pages. -/
def readGroup {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) (group : Nat) :
    Except Error Observation := do
  let rowGroup ← admitGroup limits schema group
  let rows := rowGroup.numRows.toNat
  let width := schema.leaves.size
  let columns ← (List.range width).mapM (readColumn limits.chunk schema group)
  let observations ← (List.range rows).mapM fun row =>
    readAt (schemaLimits.maxSchemaDepth - 1) group row schema.fields columns
  return ⟨rows, observations⟩

def readAll {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) :
    Except Error (List Observation) :=
  (List.range snapshot.groupCount).mapM (readGroup limits schema)

def ColumnWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Chunk.Limits) (schema : Compiled schemaLimits snapshot) (group column : Nat)
    (result : Column) : Prop :=
  ∃ (binding : ChunkBinding schema group column) (output : Chunk.Observation),
    bindChunk schema group column = .ok binding ∧
    Chunk.read limits binding = .ok output ∧ Chunk.Wire limits binding output ∧
    result.location = ⟨column, binding.leaf.site.location.path⟩ ∧
    result.slots = output.rows.toArray

def RowWire (group row : Nat) (fields : List Field) (columns : List Column) (output : Row) :
    Prop :=
  ∃ input, evidenceAt group row columns = .ok input ∧
    RowProjection fields output (input.map Evidence.slot) ∧ RowFits (fields.map Field.arrow) output

/-- Each original column and each group-relative row are covered exactly
in the two independent ordinal ranges. -/
structure GroupWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (limits : Limits) (schema : Compiled schemaLimits snapshot) (group : Nat)
    (output : Observation) : Prop where
  original : ∃ rowGroup columns,
    snapshot.groupAt group = some rowGroup ∧ rowGroup.columns.length = schema.leaves.size ∧
    output.rowCount = rowGroup.numRows.toNat ∧
    List.Forall₂ (ColumnWire limits.chunk schema group) (List.range schema.leaves.size) columns ∧
    List.Forall₂ (fun row result => RowWire group row schema.fields columns result)
      (List.range rowGroup.numRows.toNat) output.rows
  count : output.rows.length = output.rowCount
  typed : ∀ row ∈ output.rows, RowFits schema.arrow.fields row

end

end Silmaril.Formats.Parquet.RecursiveSchema.Rows
