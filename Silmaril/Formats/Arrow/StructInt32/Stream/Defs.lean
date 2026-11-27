module

public import Silmaril.Formats.Arrow.Body.Defs
public import Batteries.Data.List.Basic

/-! Checked native V5 observation of one nullable Struct with two signed Int32 children. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.StructInt32.Stream

abbrev Children := Option Int32 × Option Int32
abbrev Row := Option Children

inductive BatchError where
  | envelope (cause : Arrow.Error)
  | trailingBytes
  | batchLimit
  | metadata (cause : Arrow.Error)
  | expectedRecord
  | layout
  | budget (cause : Arrow.Error)
  | body (cause : Arrow.Error)
  | parentValidity
  | child (position : Nat) (cause : Arrow.Error)
  | requiredChild (position row : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | source
  | schemaEnvelope (cause : Arrow.Error)
  | expectedSchema
  | schemaMetadata (cause : Arrow.Error)
  | batch (index : Nat) (cause : BatchError)
  deriving DecidableEq, Repr

/-- Depth-first Struct order comprises three equal-length nodes and five buffers. -/
structure Layout where
  parent : FieldNode
  left : FieldNode
  right : FieldNode
  parentValidity : Buffer
  leftValidity : Buffer
  leftValues : Buffer
  rightValidity : Buffer
  rightValues : Buffer
  deriving DecidableEq, Repr

def Layout.nodes (layout : Layout) : List FieldNode :=
  [layout.parent, layout.left, layout.right]

def Layout.buffers (layout : Layout) : List Buffer :=
  [layout.parentValidity, layout.leftValidity, layout.leftValues, layout.rightValidity, layout.rightValues]

def Layout.leftBuffers (layout : Layout) (body : KBytes) : Body.ColumnBuffers :=
  .int32 (Body.sliceBuffer body layout.leftValidity) (Body.sliceBuffer body layout.leftValues)

def Layout.rightBuffers (layout : Layout) (body : KBytes) : Body.ColumnBuffers :=
  .int32 (Body.sliceBuffer body layout.rightValidity) (Body.sliceBuffer body layout.rightValues)

def layoutOf (metadata : RecordBatch) : Except BatchError Layout :=
  match metadata.nodes, metadata.buffers with
  | [parent, left, right], [bitmap, leftBitmap, leftValues, rightBitmap, rightValues] =>
    if parent.length = metadata.rowCount ∧ left.length = parent.length ∧ right.length = parent.length then
      .ok ⟨parent, left, right, bitmap, leftBitmap, leftValues, rightBitmap, rightValues⟩
    else .error .layout
  | _, _ => .error .layout

def int32Slot : Option Value → Option Int32
  | some (.int32 value) => some value
  | _ => none

def missingRequired (field : StructInt32.Field) (children : Children) : Option Nat :=
  if !field.left.nullable && children.1.isNone then some 0
  else if !field.right.nullable && children.2.isNone then some 1
  else none

/-- Only the parent bit controls whole-row absence. Child requiredness
is checked for visible slots. Both physical child buffers are checked separately. -/
def readRow (field : StructInt32.Field) (bitmap : KBytes) (left right : Array (Option Int32))
    (index : Nat) : Except BatchError Row :=
  match Body.validAt bitmap index with
  | none => .error .parentValidity
  | some false => .ok none
  | some true =>
    match left[index]?, right[index]? with
    | some lhs, some rhs =>
      match missingRequired field (lhs, rhs) with
      | none => .ok (some (lhs, rhs))
      | some position => .error (.requiredChild position index)
    | _, _ => .error .layout

def readRows (field : StructInt32.Field) (layout : Layout) (body : KBytes) :
    Except BatchError (List Row) := do
  if ¬ BuffersFit body.len 0 layout.buffers then throw .layout
  let bitmap := Body.sliceBuffer body layout.parentValidity
  if ¬ Body.BitmapExtent bitmap layout.parent.length then throw .parentValidity
  let left ← (Body.readColumn layout.left (layout.leftBuffers body)).mapError (.child 0)
  let right ← (Body.readColumn layout.right (layout.rightBuffers body)).mapError (.child 1)
  let rows ← (List.range layout.parent.length).mapM
    (readRow field bitmap (left.map int32Slot).toArray (right.map int32Slot).toArray)
  if rows.countP Option.isNone ≠ layout.parent.nullCount then throw .parentValidity
  return rows

structure Batch where
  offset : Nat
  metadataSize : Nat
  bodyLength : Nat
  rows : List Row
  deriving DecidableEq, Repr

def Batch.next (batch : Batch) : Nat :=
  batch.offset + 8 + batch.metadataSize + batch.bodyLength

structure Observed where
  field : StructInt32.Field
  batches : List Batch
  deriving DecidableEq, Repr

def readSchemaFrame (limits : Arrow.Limits) (input : KBytes) : Except Error (StructInt32.Field × Nat) := do
  let envelope ← (readEnvelope limits input 0).mapError .schemaEnvelope
  let .metadata size := envelope | throw .expectedSchema
  let field ← (StructInt32.readSchema limits (input.slice 8 size)).mapError .schemaMetadata
  return (field, 8 + size)

def readRecord (limits : ObservationLimits) (field : StructInt32.Field) (input : KBytes)
    (rowsBefore offset size : Nat) : Except BatchError Batch := do
  let parsed ← (readMessage { limits.ipc with fields := min 3 limits.ipc.fields }
    (input.slice (offset + 8) size)).mapError .metadata
  let .recordBatch metadata := parsed.header | throw .expectedRecord
  let layout ← layoutOf metadata
  (Body.checkBudget limits 3 (rowsBefore + metadata.rowCount)).mapError .budget
  let body ← (readBody limits.ipc input (offset + 8 + size) parsed.bodyLength).mapError .body
  let rows ← readRows field layout body
  return ⟨offset, size, parsed.bodyLength, rows⟩

def readBatches (limits : ObservationLimits) (field : StructInt32.Field) (input : KBytes) :
    (fuel index rowsBefore offset : Nat) → Except Error (List Batch)
  | fuel, index, rowsBefore, offset => do
    let envelope ← (readEnvelope limits.ipc input offset).mapError (.batch index ∘ .envelope)
    match envelope with
    | .eos =>
      if offset + 8 = input.len then return []
      else throw (.batch index .trailingBytes)
    | .metadata size =>
      match fuel with
      | 0 => throw (.batch index .batchLimit)
      | remaining + 1 =>
        let batch ← (readRecord limits field input rowsBefore offset size).mapError (.batch index)
        let rest ← readBatches limits field input remaining (index + 1)
          (rowsBefore + batch.rows.length) batch.next
        return batch :: rest

def read (limits : ObservationLimits) (input : KBytes) : Except Error Observed := do
  if !input.wf then throw .source
  let (field, first) ← readSchemaFrame limits.ipc input
  let batches ← readBatches limits field input limits.ipc.batches 0 0 first
  return ⟨field, batches⟩

/-- Preserve an independent parent bit, and the two ordered physical slots
whenever the parent is present. -/
def RowWire (field : StructInt32.Field) (bitmap : KBytes) (left right : Array (Option Int32))
    (index : Nat) (row : Row) : Prop :=
  ∃ valid : Bool, Body.validAt bitmap index = some valid ∧
    if valid then ∃ lhs rhs, left[index]? = some lhs ∧ right[index]? = some rhs ∧
      missingRequired field (lhs, rhs) = none ∧ row = some (lhs, rhs)
    else row = none

def RowsWire (field : StructInt32.Field) (layout : Layout) (body : KBytes) (rows : List Row) : Prop :=
  let bitmap := Body.sliceBuffer body layout.parentValidity
  BuffersFit body.len 0 layout.buffers ∧ Body.BitmapExtent bitmap layout.parent.length ∧
    rows.length = layout.parent.length ∧ rows.countP Option.isNone = layout.parent.nullCount ∧
    ∃ left right,
      Body.ColumnWire layout.left (layout.leftBuffers body) left ∧
      Body.ColumnWire layout.right (layout.rightBuffers body) right ∧
      List.Forall₂ (RowWire field bitmap (left.map int32Slot).toArray (right.map int32Slot).toArray)
        (List.range layout.parent.length) rows

structure RecordWire (limits : ObservationLimits) (field : StructInt32.Field) (input : KBytes)
    (rowsBefore offset size : Nat) (batch : Batch) : Prop where
  data : ∃ metadata layout body,
    readMessage { limits.ipc with fields := min 3 limits.ipc.fields }
      (input.slice (offset + 8) size) = .ok ⟨.recordBatch metadata, batch.bodyLength⟩ ∧
    layoutOf metadata = .ok layout ∧ metadata.nodes = layout.nodes ∧ metadata.buffers = layout.buffers ∧
    layout.parent.length = metadata.rowCount ∧ layout.left.length = metadata.rowCount ∧
    layout.right.length = metadata.rowCount ∧
    Body.checkBudget limits 3 (rowsBefore + metadata.rowCount) = .ok () ∧
    readBody limits.ipc input (offset + 8 + size) batch.bodyLength = .ok body ∧
    RowsWire field layout body batch.rows ∧ batch.offset = offset ∧ batch.metadataSize = size

/-- Each original record consumes a batch, including explicit zero-row records. -/
inductive BatchesWire (limits : ObservationLimits) (field : StructInt32.Field) (input : KBytes) :
    Nat → Nat → Nat → List Batch → Prop where
  | eos {fuel rows offset} :
      readEnvelope limits.ipc input offset = .ok .eos → offset + 8 = input.len →
      BatchesWire limits field input fuel rows offset []
  | next {fuel rows offset size batch rest} :
      readEnvelope limits.ipc input offset = .ok (.metadata size) →
      RecordWire limits field input rows offset size batch →
      BatchesWire limits field input fuel (rows + batch.rows.length) batch.next rest →
      BatchesWire limits field input (fuel + 1) rows offset (batch :: rest)

end Silmaril.Formats.Arrow.StructInt32.Stream
