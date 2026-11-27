module

public import Silmaril.Formats.Arrow.MixedFlat.Defs
public import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Defs
public import Silmaril.Formats.Arrow.MetadataWriter.Defs

/-! Checked standalone V5 RecordBatch writing for one Int32 and one BinaryView field. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Writer

inductive Order where
  | intFirst | viewFirst
  deriving DecidableEq, Repr

def Order.pair {α : Type} (order : Order) (integer view : α) : List α :=
  match order with
  | .intFirst => [integer, view]
  | .viewFirst => [view, integer]

def Order.indices : Order → Nat × Nat
  | .intFirst => (0, 1)
  | .viewFirst => (1, 0)

structure Input where
  order : Order
  rowCount : Nat
  intName : String
  intNullable : Bool
  intValues : List (Option Int32)
  viewName : String
  viewNullable : Bool
  viewValues : List (Option KBytes)

def Input.intField (input : Input) : Field := ⟨input.intName, input.intNullable, .primitive .int32⟩

def Input.viewField (input : Input) : Field := ⟨input.viewName, input.viewNullable, .view .binary⟩

def Input.fields (input : Input) : List Field :=
  input.order.pair input.intField input.viewField

def Input.intColumn (input : Input) : Arrow.Writer.ColumnValues := .int32 input.intValues

def Input.intNode (input : Input) : FieldNode :=
  ⟨input.intColumn.length, input.intColumn.nullCount⟩

def viewParts (view : BinaryView.Column.Buffers) : List KBytes :=
  view.validity :: view.payload.views :: view.payload.data.toList

def Input.parts (input : Input) (view : BinaryView.Column.Buffers) : List KBytes :=
  (input.order.pair input.intColumn.emit (viewParts view)).flatten

inductive ColumnObservation where
  | int32 (values : Arrow.Column)
  | binaryView (values : List (Option (List UInt8)))
  | utf8View (values : List (Option String))
  deriving DecidableEq

def Input.observe (input : Input) : List (Field × ColumnObservation) :=
  input.order.pair (input.intField, .int32 input.intColumn.observe)
    (input.viewField, .binaryView (input.viewValues.map (Option.map KBytes.toList)))

def observeColumns (columns : List (Field × MixedFlat.Column)) :
    Option (List (Field × ColumnObservation)) :=
  columns.mapM fun (field, column) => do
    let values ← match column with
      | .primitive values => some (.int32 values)
      | .binaryView values => some (.binaryView (values.map (Option.map KBytes.toList)))
      | .utf8View values => some (.utf8View values)
    return (field, values)

namespace Wire

open MetadataWriter.Wire

/-- V5 RecordBatch Message with aligned node, descriptor, and signed count
vectors. The count vector follows the descriptors in view field order. -/
def metadataWithCounts (batch : RecordBatch) (bodyLength : Nat) (variadic : List Nat) : KBytes :=
  let nodeBytes := 16 * batch.nodes.length
  let bufferBytes := 16 * batch.buffers.length
  let vtable := words [halfwords 14 32, halfwords 8 16, halfwords 20 0, halfwords 24 0]
  let table := words [16, 0] ++
    (longs [batch.rowCount] ++ words [20, 24 + nodeBytes, 28 + nodeBytes + bufferBytes, 0])
  let nodes := words [0, batch.nodes.length] ++
    longs (batch.nodes.flatMap fun node => [node.length, node.nullCount])
  let buffers := words [0, batch.buffers.length] ++
    longs (batch.buffers.flatMap fun buffer => [buffer.offset, buffer.length])
  let counts := words [0, variadic.length] ++ longs variadic
  messagePrefix 3 64 bodyLength ++ (vtable ++ (table ++ (nodes ++ (buffers ++ counts))))

def metadata (batch : RecordBatch) (bodyLength count : Nat) : KBytes :=
  metadataWithCounts batch bodyLength [count]

def metadataSizeWithCounts (nodes buffers counts : Nat) : Nat :=
  120 + 16 * nodes + 16 * buffers + 8 * counts

def metadataSize (nodes buffers : Nat) : Nat := 128 + 16 * nodes + 16 * buffers

end Wire

inductive Error where
  | ipc (cause : Arrow.Error)
  | rowCount (fieldIndex expected actual : Nat)
  | nullInRequired (fieldIndex : Nat)
  | view (fieldIndex : Nat) (cause : BinaryView.Column.Writer.Error)
  | metadata (cause : MixedFlat.MetadataError)
  | metadataMismatch
  | readback (cause : MixedFlat.Error)
  | valuesMismatch
  deriving DecidableEq, Repr

structure Emitted where
  metadata : MixedFlat.Metadata
  metadataBytes : KBytes
  body : KBytes

def checkInput (limits : MixedFlat.Limits) (input : Input) : Except Error Unit := do
  let ipc := limits.observation.ipc
  if 2 > ipc.fields then throw (.ipc (.limit .fields))
  if input.rowCount > ipc.rows then throw (.ipc (.limit .rows))
  if input.rowCount ≥ 2^63 then throw (.ipc (.malformed .batchLayout))
  (Body.checkBudget limits.observation 2 input.rowCount).mapError .ipc
  let (integer, view) := input.order.indices
  if input.intValues.length ≠ input.rowCount then
    throw (.rowCount integer input.rowCount input.intValues.length)
  if input.viewValues.length ≠ input.rowCount then
    throw (.rowCount view input.rowCount input.viewValues.length)
  if !input.intNullable && input.intValues.any Option.isNone then throw (.nullInRequired integer)

def checkSizes (limits : MixedFlat.Limits) (count : Nat) (sizes : List Nat) : Except Error Unit := do
  let ipc := limits.observation.ipc
  if count > limits.totalDataBuffers then throw (.metadata .totalDataBufferLimit)
  if Wire.metadataSize 2 sizes.length > ipc.metadataBytes then throw (.ipc (.limit .metadataBytes))
  let bodySize := (sizes.map fun size => size + Arrow.Writer.padding size).sum
  if bodySize ≥ 2^63 then throw (.ipc (.malformed .bodyLength))
  if bodySize > ipc.bodyBytes then throw (.ipc (.limit .bodyBytes))

def encode (input : Input) (view : BinaryView.Column.Writer.Emitted) : Emitted :=
  let count := view.buffers.payload.data.size
  let (buffers, body) := Arrow.Writer.packBuffers 0 (input.parts view.buffers)
  let batch : RecordBatch := ⟨input.rowCount, input.order.pair input.intNode view.node, buffers⟩
  ⟨⟨batch, body.len, [count]⟩, Wire.metadata batch body.len count, body⟩

def serialize (limits : MixedFlat.Limits) (input : Input) : Except Error Emitted := do
  checkInput limits input
  let view ← (BinaryView.Column.Writer.emitBinary limits.view input.viewNullable input.viewValues).mapError
    (.view input.order.indices.2)
  checkSizes limits view.buffers.payload.data.size
    (input.intColumn.bufferSizes ++ (viewParts view.buffers).map KBytes.len)
  return encode input view

/-- Certify the emitted FlatBuffers region and packed body with the mixed-flat
reader, using the caller's exact field declarations in their selected order. -/
def emit (limits : MixedFlat.Limits) (input : Input) : Except Error Emitted := do
  let output ← serialize limits input
  let metadata ← (MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers
    limits.totalDataBuffers input.fields output.metadataBytes).mapError .metadata
  if metadata ≠ output.metadata then throw .metadataMismatch
  let values ← (MixedFlat.readParsed limits input.fields metadata output.body).mapError .readback
  if values.rowCount = input.rowCount ∧ observeColumns values.columns = some input.observe then
    return output
  else throw .valuesMismatch

/-- The packed bytes and metadata of a successful write retain the admitted
input rows and the exact physical pieces in schema order. -/
structure Layout (limits : MixedFlat.Limits) (input : Input) (output : Emitted) : Prop where
  lengths : input.intValues.length = input.rowCount ∧ input.viewValues.length = input.rowCount
  rows : output.metadata.batch.rowCount = input.rowCount
  nodes : output.metadata.batch.nodes = input.order.pair
    ⟨input.intValues.length, input.intValues.countP Option.isNone⟩
    ⟨input.viewValues.length, input.viewValues.countP Option.isNone⟩
  counts : output.metadata.counts =
    [BinaryView.Column.Writer.dataCount (BinaryView.Column.Writer.longBytes KBytes.len input.viewValues)]
  bodyExtent : output.metadata.bodyLength = output.body.len
  bodyAligned : output.body.len % 8 = 0
  metadataExtent : output.metadataBytes.len =
    Wire.metadataSize output.metadata.batch.nodes.length output.metadata.batch.buffers.length
  packed : ∃ view, BinaryView.Column.Writer.emitBinary limits.view input.viewNullable input.viewValues = .ok view ∧
    Arrow.Writer.PackedWire output.body.toList 0 (input.parts view.buffers) output.metadata.batch.buffers

end Silmaril.Formats.Arrow.MixedFlat.Writer
