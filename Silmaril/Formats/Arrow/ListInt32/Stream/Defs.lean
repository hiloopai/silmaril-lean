module

public import Silmaril.Formats.Arrow.Body.Defs
public import Batteries.Data.List.Basic

/-! Bounded native Arrow IPC V5 observation of one nullable List<Int32>
with nullable children. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.ListInt32.Stream

abbrev Row := Option (List (Option Int32))

structure Limits where
  ipc : Arrow.Limits := {}
  totalRows : Nat := 1024 * 1024
  totalChildren : Nat := 8 * 1024 * 1024

inductive BatchError where
  | envelope (cause : Arrow.Error)
  | trailingBytes
  | batchLimit
  | metadata (cause : Arrow.Error)
  | expectedRecord
  | layout
  | body (cause : Arrow.Error)
  | rowLimit
  | childLimit
  | parentValidity
  | offsets
  | child (cause : Arrow.Error)
  deriving DecidableEq, Repr

inductive Error where
  | source
  | schemaEnvelope (cause : Arrow.Error)
  | expectedSchema
  | schemaMetadata (cause : Arrow.Error)
  | batch (index : Nat) (cause : BatchError)
  deriving DecidableEq, Repr

/-- Two nodes and four buffers in depth-first IPC order. -/
structure Layout where
  parent : FieldNode
  child : FieldNode
  parentValidity : Buffer
  offsets : Buffer
  childValidity : Buffer
  childValues : Buffer
  deriving DecidableEq, Repr

def Layout.buffers (layout : Layout) : List Buffer :=
  [layout.parentValidity, layout.offsets, layout.childValidity, layout.childValues]

def Layout.childBuffers (layout : Layout) (body : KBytes) : Body.ColumnBuffers :=
  .int32 (Body.sliceBuffer body layout.childValidity) (Body.sliceBuffer body layout.childValues)

def layoutOf (metadata : RecordBatch) : Except BatchError Layout :=
  match metadata.nodes, metadata.buffers with
  | [parent, child], [bitmap, offsets, childBitmap, values] =>
    if parent.length = metadata.rowCount then
      .ok ⟨parent, child, bitmap, offsets, childBitmap, values⟩
    else .error .layout
  | _, _ => .error .layout

def int32Slot : Option Value → Option Int32
  | some (.int32 value) => some value
  | _ => none

/-- Validate both offsets even for a null parent. Its child segment is
unobserved, but could be nonempty in the original wire. -/
def readRow (bitmap offsets : KBytes) (children : Array (Option Int32)) (index : Nat) :
    Except BatchError Row := do
  let some left := Body.offsetAt offsets index | throw .offsets
  let some right := Body.offsetAt offsets (index + 1) | throw .offsets
  if ¬ (left ≤ right ∧ right ≤ children.size) then throw .offsets
  let some valid := Body.validAt bitmap index | throw .parentValidity
  pure (if valid then some (children.extract left right).toList else none)

/-- Require normalized offset endpoints and one explicit offset even for
a zero-row batch. The materialized bitmaps may include padding. -/
def readRows (layout : Layout) (body : KBytes) : Except BatchError (List Row) := do
  if ¬ BuffersFit body.len 0 layout.buffers then throw .layout
  let bitmap := Body.sliceBuffer body layout.parentValidity
  let offsets := Body.sliceBuffer body layout.offsets
  if ¬ Body.BitmapExtent bitmap layout.parent.length then throw .parentValidity
  if offsets.len ≠ 4 * (layout.parent.length + 1) ||
      Body.offsetAt offsets 0 != some 0 ||
      Body.offsetAt offsets layout.parent.length != some layout.child.length then
    throw .offsets
  let physical ← (Body.readColumn layout.child (layout.childBuffers body)).mapError .child
  let children := (physical.map int32Slot).toArray
  let rows ← (List.range layout.parent.length).mapM (readRow bitmap offsets children)
  if rows.countP Option.isNone ≠ layout.parent.nullCount then throw .parentValidity
  pure rows

structure Batch where
  offset : Nat
  metadataSize : Nat
  bodyLength : Nat
  childCount : Nat
  rows : List Row
  deriving DecidableEq, Repr

def Batch.next (batch : Batch) : Nat :=
  batch.offset + 8 + batch.metadataSize + batch.bodyLength

structure Observed where
  field : ListInt32.Field
  batches : List Batch
  deriving DecidableEq, Repr

def readSchemaFrameFor (parentNullable : Bool) (limits : Arrow.Limits) (input : KBytes) :
    Except Error (ListInt32.Field × Nat) := do
  let envelope ← (readEnvelope limits input 0).mapError .schemaEnvelope
  let .metadata size := envelope | throw .expectedSchema
  let field ← (ListInt32.readSchemaFor parentNullable limits (input.slice 8 size)).mapError .schemaMetadata
  pure (field, 8 + size)

def readSchemaFrame := readSchemaFrameFor true

/-- Reuse the shared V5 RecordBatch parsing. Check running row and child
budgets before decoding any body values. -/
def readRecord (limits : Limits) (input : KBytes) (rowsBefore childrenBefore offset size : Nat) :
    Except BatchError Batch := do
  let parsed ← (readMessage { limits.ipc with fields := min 2 limits.ipc.fields }
    (input.slice (offset + 8) size)).mapError .metadata
  let .recordBatch metadata := parsed.header | throw .expectedRecord
  let layout ← layoutOf metadata
  if limits.totalRows < rowsBefore + metadata.rowCount then throw .rowLimit
  if limits.totalChildren < childrenBefore + layout.child.length then throw .childLimit
  let body ← (readBody limits.ipc input (offset + 8 + size) parsed.bodyLength).mapError .body
  let rows ← readRows layout body
  pure ⟨offset, size, parsed.bodyLength, layout.child.length, rows⟩

def readBatches (limits : Limits) (input : KBytes) :
    (fuel index rowsBefore childrenBefore offset : Nat) → Except Error (List Batch)
  | fuel, index, rowsBefore, childrenBefore, offset => do
    let envelope ← (readEnvelope limits.ipc input offset).mapError (.batch index ∘ .envelope)
    match envelope with
    | .eos =>
      if offset + 8 = input.len then return []
      else throw (.batch index .trailingBytes)
    | .metadata size =>
      match fuel with
      | 0 => throw (.batch index .batchLimit)
      | remaining + 1 =>
        let batch ← (readRecord limits input rowsBefore childrenBefore offset size).mapError (.batch index)
        let rest ← readBatches limits input remaining (index + 1) (rowsBefore + batch.rows.length)
          (childrenBefore + batch.childCount) batch.next
        pure (batch :: rest)

def checkParents (parentNullable : Bool) (batches : List Batch) : Except Error Unit :=
  if parentNullable then .ok ()
  else match batches.findIdx? (fun batch => batch.rows.any Option.isNone) with
    | none => .ok ()
    | some index => .error (.batch index .parentValidity)

/-- Consume the exact carrier and enforce the selected LIST parent nullability. -/
def readFor (parentNullable : Bool) (limits : Limits) (input : KBytes) : Except Error Observed := do
  if !input.wf then throw .source
  let (field, first) ← readSchemaFrameFor parentNullable limits.ipc input
  let batches ← readBatches limits input limits.ipc.batches 0 0 0 first
  checkParents parentNullable batches
  pure ⟨field, batches⟩

/-- The original nullable parent profile. -/
def read := readFor true

/-- Original bitmap bit and signed, bounded offsets for one parent slot. -/
def RowWire (bitmap offsets : KBytes) (children : Array (Option Int32))
    (index : Nat) (row : Row) : Prop :=
  ∃ (valid : Bool) (lo hi : Nat),
    Body.validAt bitmap index = some valid ∧
    Body.offsetAt offsets index = some lo ∧ Body.offsetAt offsets (index + 1) = some hi ∧
    lo ≤ hi ∧ hi ≤ children.size ∧
    row = (if valid then some (children.toList.extract lo hi) else none)

def RowsWire (layout : Layout) (body : KBytes) (rows : List Row) : Prop :=
  let bitmap := Body.sliceBuffer body layout.parentValidity
  let offsets := Body.sliceBuffer body layout.offsets
  BuffersFit body.len 0 layout.buffers ∧ Body.BitmapExtent bitmap layout.parent.length ∧
    offsets.len = 4 * (layout.parent.length + 1) ∧
    Body.offsetAt offsets 0 = some 0 ∧
    Body.offsetAt offsets layout.parent.length = some layout.child.length ∧
    rows.countP Option.isNone = layout.parent.nullCount ∧
    rows.length = layout.parent.length ∧
    ∃ physical, physical.length = layout.child.length ∧
      Body.ColumnWire layout.child (layout.childBuffers body) physical ∧
      List.Forall₂ (RowWire bitmap offsets (physical.map int32Slot).toArray)
        (List.range layout.parent.length) rows

structure RecordWire (limits : Limits) (input : KBytes)
    (rowsBefore childrenBefore offset size : Nat) (batch : Batch) : Prop where
  data : ∃ metadata layout body,
    readMessage { limits.ipc with fields := min 2 limits.ipc.fields }
      (input.slice (offset + 8) size) = .ok ⟨.recordBatch metadata, batch.bodyLength⟩ ∧
    layoutOf metadata = .ok layout ∧ layout.parent.length = metadata.rowCount ∧
    metadata.nodes = [layout.parent, layout.child] ∧ metadata.buffers = layout.buffers ∧
    readBody limits.ipc input (offset + 8 + size) batch.bodyLength = .ok body ∧
    RowsWire layout body batch.rows ∧
    batch.offset = offset ∧ batch.metadataSize = size ∧ batch.childCount = layout.child.length ∧
    rowsBefore + metadata.rowCount ≤ limits.totalRows ∧ childrenBefore + batch.childCount ≤ limits.totalChildren

/-- One checked output per original frame. Empty batches still consume a
record envelope, metadata, body and one unit of fuel. -/
inductive BatchesWire (limits : Limits) (input : KBytes) :
    Nat → Nat → Nat → Nat → List Batch → Prop where
  | eos {fuel rows children offset} :
      readEnvelope limits.ipc input offset = .ok .eos → offset + 8 = input.len →
      BatchesWire limits input fuel rows children offset []
  | next {fuel rows children offset size batch rest} :
      readEnvelope limits.ipc input offset = .ok (.metadata size) →
      RecordWire limits input rows children offset size batch →
      BatchesWire limits input fuel (rows + batch.rows.length) (children + batch.childCount) batch.next rest →
      BatchesWire limits input (fuel + 1) rows children offset (batch :: rest)

end Silmaril.Formats.Arrow.ListInt32.Stream
