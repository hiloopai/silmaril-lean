module

public import Silmaril.Formats.Arrow.Body.Defs
public import Silmaril.Formats.Parquet.Plain.Defs
public import Batteries.Data.List.Basic

/-! Checked native V5 observation of one nullable Struct with signed Int32 and explicit signed second-child width. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.StructInt32.Stream

open StructInt32 (RightWidth)
open Silmaril.Formats.Parquet

abbrev ChildrenFor (α : Type) := Option Int32 × Option α
abbrev RowFor (α : Type) := Option (ChildrenFor α)
abbrev Children := ChildrenFor Int32
abbrev Row := RowFor Int32

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

def missingRequiredFor {α : Type} (field : StructInt32.Field) (children : ChildrenFor α) : Option Nat :=
  if !field.left.nullable && children.1.isNone then some 0
  else if !field.right.nullable && children.2.isNone then some 1
  else none

abbrev missingRequired := @missingRequiredFor Int32

def wideSlot (bitmap : KBytes) (entry : Int64 × Nat) : Except Arrow.Error (Option Int64) := do
  let some valid := Body.validAt bitmap entry.2 | throw (.malformed .validityBitmap)
  return if valid then some entry.1 else none

/-- The buffer descriptor can include padding. Only its exact logical
prefix of eight-byte signed words is passed to the shared integer codec. -/
def readWideColumn (node : FieldNode) (bitmap values : KBytes) : Except Arrow.Error (List (Option Int64)) := do
  if ¬ Body.BitmapExtent bitmap node.length then throw (.malformed .validityBitmap)
  let extent := 8 * node.length
  if values.len < extent then throw (.malformed .bodyValues)
  let words ← (Plain.decodeInt64 node.length ⟨(values.slice 0 extent).toByteArray⟩).mapError
    fun _ => .malformed .bodyValues
  let slots ← words.zipIdx.mapM (wideSlot bitmap)
  if slots.countP Option.isNone ≠ node.nullCount then throw (.malformed .validityBitmap)
  return slots

abbrev RightPhysical : RightWidth → Type
  | .int32 => Column
  | .int64 => List (Option Int64)

def readRightColumn : (width : RightWidth) → Layout → KBytes → Except Arrow.Error (RightPhysical width)
  | .int32, layout, body => Body.readColumn layout.right (layout.rightBuffers body)
  | .int64, layout, body =>
    readWideColumn layout.right (Body.sliceBuffer body layout.rightValidity) (Body.sliceBuffer body layout.rightValues)

def rightSlots : (width : RightWidth) → RightPhysical width → List (Option width.Value)
  | .int32, slots => slots.map int32Slot
  | .int64, slots => slots

/-- Only the parent bit controls whole-row absence. Child requiredness
is checked for visible slots. Both physical child buffers are checked separately. -/
def readRowFor {α : Type} (field : StructInt32.Field) (bitmap : KBytes)
    (left : Array (Option Int32)) (right : Array (Option α)) (index : Nat) : Except BatchError (RowFor α) :=
  match Body.validAt bitmap index with
  | none => .error .parentValidity
  | some false => .ok none
  | some true =>
    match left[index]?, right[index]? with
    | some lhs, some rhs =>
      match missingRequiredFor field (lhs, rhs) with
      | none => .ok (some (lhs, rhs))
      | some position => .error (.requiredChild position index)
    | _, _ => .error .layout

abbrev readRow := @readRowFor Int32

def readRowsFor (width : RightWidth) (field : StructInt32.Field) (layout : Layout) (body : KBytes) :
    Except BatchError (List (RowFor width.Value)) := do
  if ¬ BuffersFit body.len 0 layout.buffers then throw .layout
  let bitmap := Body.sliceBuffer body layout.parentValidity
  if ¬ Body.BitmapExtent bitmap layout.parent.length then throw .parentValidity
  let left ← (Body.readColumn layout.left (layout.leftBuffers body)).mapError (.child 0)
  let right ← (readRightColumn width layout body).mapError (.child 1)
  let rows ← (List.range layout.parent.length).mapM
    (readRowFor field bitmap (left.map int32Slot).toArray (rightSlots width right).toArray)
  if rows.countP Option.isNone ≠ layout.parent.nullCount then throw .parentValidity
  return rows

abbrev readRows := readRowsFor .int32

structure Batch (α : Type := Int32) where
  offset : Nat
  metadataSize : Nat
  bodyLength : Nat
  rows : List (RowFor α)
  deriving DecidableEq, Repr

def Batch.next {α : Type} (batch : Batch α) : Nat :=
  batch.offset + 8 + batch.metadataSize + batch.bodyLength

structure Observed (α : Type := Int32) where
  field : StructInt32.Field
  batches : List (Batch α)
  deriving DecidableEq, Repr

def readSchemaFrameFor (width : RightWidth) (limits : Arrow.Limits) (input : KBytes) : Except Error (StructInt32.Field × Nat) := do
  let envelope ← (readEnvelope limits input 0).mapError .schemaEnvelope
  let .metadata size := envelope | throw .expectedSchema
  let field ← (StructInt32.readSchemaFor width limits (input.slice 8 size)).mapError .schemaMetadata
  return (field, 8 + size)

abbrev readSchemaFrame := readSchemaFrameFor .int32

def readRecordFor (width : RightWidth) (limits : ObservationLimits) (field : StructInt32.Field) (input : KBytes)
    (rowsBefore offset size : Nat) : Except BatchError (Batch width.Value) := do
  let parsed ← (readMessage { limits.ipc with fields := min 3 limits.ipc.fields }
    (input.slice (offset + 8) size)).mapError .metadata
  let .recordBatch metadata := parsed.header | throw .expectedRecord
  let layout ← layoutOf metadata
  (Body.checkBudget limits 3 (rowsBefore + metadata.rowCount)).mapError .budget
  let body ← (readBody limits.ipc input (offset + 8 + size) parsed.bodyLength).mapError .body
  let rows ← readRowsFor width field layout body
  return ⟨offset, size, parsed.bodyLength, rows⟩

abbrev readRecord := readRecordFor .int32

def readBatchesFor (width : RightWidth) (limits : ObservationLimits) (field : StructInt32.Field) (input : KBytes) :
    (fuel index rowsBefore offset : Nat) → Except Error (List (Batch width.Value))
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
        let batch ← (readRecordFor width limits field input rowsBefore offset size).mapError (.batch index)
        let rest ← readBatchesFor width limits field input remaining (index + 1)
          (rowsBefore + batch.rows.length) batch.next
        return batch :: rest

abbrev readBatches := readBatchesFor .int32

def readFor (width : RightWidth) (limits : ObservationLimits) (input : KBytes) :
    Except Error (Observed width.Value) := do
  if !input.wf then throw .source
  let (field, first) ← readSchemaFrameFor width limits.ipc input
  let batches ← readBatchesFor width limits field input limits.ipc.batches 0 0 first
  return ⟨field, batches⟩

/-- The strict two-Int32 entry point. -/
abbrev read := readFor .int32

/-- Preserve signed little-endian words and the independent child bitmap,
including physical slots that the parent may hide. -/
def WideColumnWire (node : FieldNode) (bitmap values : KBytes) (slots : List (Option Int64)) : Prop :=
  Body.BitmapExtent bitmap node.length ∧ 8 * node.length ≤ values.len ∧
    slots.countP Option.isNone = node.nullCount ∧
    ∃ words : List (List UInt8),
      (values.slice 0 (8 * node.length)).toList = words.flatten ∧
      words.length = node.length ∧ (∀ word ∈ words, word.length = 8) ∧
      List.Forall₂ (fun (word, index) slot =>
        ∃ valid, Body.validAt bitmap index = some valid ∧
          slot = (if valid then some (UInt64.ofNat (KBytes.leVal word)).toInt64 else none))
        words.zipIdx slots

def RightColumnWire : (width : RightWidth) → Layout → KBytes → RightPhysical width → Prop
  | .int32, layout, body, slots => Body.ColumnWire layout.right (layout.rightBuffers body) slots
  | .int64, layout, body, slots =>
    WideColumnWire layout.right (Body.sliceBuffer body layout.rightValidity)
      (Body.sliceBuffer body layout.rightValues) slots

/-- Preserve an independent parent bit, and the two ordered physical slots
whenever the parent is present. -/
def RowWireFor {α : Type} (field : StructInt32.Field) (bitmap : KBytes)
    (left : Array (Option Int32)) (right : Array (Option α)) (index : Nat) (row : RowFor α) : Prop :=
  ∃ valid : Bool, Body.validAt bitmap index = some valid ∧
    if valid then ∃ lhs rhs, left[index]? = some lhs ∧ right[index]? = some rhs ∧
      missingRequiredFor field (lhs, rhs) = none ∧ row = some (lhs, rhs)
    else row = none

abbrev RowWire := @RowWireFor Int32

def RowsWireFor (width : RightWidth) (field : StructInt32.Field) (layout : Layout) (body : KBytes)
    (rows : List (RowFor width.Value)) : Prop :=
  let bitmap := Body.sliceBuffer body layout.parentValidity
  BuffersFit body.len 0 layout.buffers ∧ Body.BitmapExtent bitmap layout.parent.length ∧
    rows.length = layout.parent.length ∧ rows.countP Option.isNone = layout.parent.nullCount ∧
    ∃ left right,
      Body.ColumnWire layout.left (layout.leftBuffers body) left ∧
      RightColumnWire width layout body right ∧
      List.Forall₂ (RowWireFor field bitmap (left.map int32Slot).toArray (rightSlots width right).toArray)
        (List.range layout.parent.length) rows

abbrev RowsWire := RowsWireFor .int32

structure RecordWireFor (width : RightWidth) (limits : ObservationLimits) (field : StructInt32.Field) (input : KBytes)
    (rowsBefore offset size : Nat) (batch : Batch width.Value) : Prop where
  data : ∃ metadata layout body,
    readMessage { limits.ipc with fields := min 3 limits.ipc.fields }
      (input.slice (offset + 8) size) = .ok ⟨.recordBatch metadata, batch.bodyLength⟩ ∧
    layoutOf metadata = .ok layout ∧ metadata.nodes = layout.nodes ∧ metadata.buffers = layout.buffers ∧
    layout.parent.length = metadata.rowCount ∧ layout.left.length = metadata.rowCount ∧
    layout.right.length = metadata.rowCount ∧
    Body.checkBudget limits 3 (rowsBefore + metadata.rowCount) = .ok () ∧
    readBody limits.ipc input (offset + 8 + size) batch.bodyLength = .ok body ∧
    RowsWireFor width field layout body batch.rows ∧ batch.offset = offset ∧ batch.metadataSize = size

abbrev RecordWire := RecordWireFor .int32

namespace RecordWire
abbrev mk := @RecordWireFor.mk .int32
abbrev data := @RecordWireFor.data .int32
end RecordWire

/-- Each original record consumes a batch, including explicit zero-row records. -/
inductive BatchesWireFor (width : RightWidth) (limits : ObservationLimits) (field : StructInt32.Field) (input : KBytes) :
    Nat → Nat → Nat → List (Batch width.Value) → Prop where
  | eos {fuel rows offset} :
      readEnvelope limits.ipc input offset = .ok .eos → offset + 8 = input.len →
      BatchesWireFor width limits field input fuel rows offset []
  | next {fuel rows offset size batch rest} :
      readEnvelope limits.ipc input offset = .ok (.metadata size) →
      RecordWireFor width limits field input rows offset size batch →
      BatchesWireFor width limits field input fuel (rows + batch.rows.length) batch.next rest →
      BatchesWireFor width limits field input (fuel + 1) rows offset (batch :: rest)

abbrev BatchesWire := BatchesWireFor .int32

namespace BatchesWire
abbrev eos := @BatchesWireFor.eos .int32
abbrev next := @BatchesWireFor.next .int32
end BatchesWire

end Silmaril.Formats.Arrow.StructInt32.Stream
