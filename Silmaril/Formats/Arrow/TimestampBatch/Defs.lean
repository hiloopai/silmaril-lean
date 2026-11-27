module

public import Silmaril.Formats.Arrow.Body.Defs
public import Silmaril.Formats.ColumnarTimestamp.Wire.Defs
public import Mathlib.Data.List.Forall2

/-! # Checked one-column Arrow IPC Timestamp batches -/

@[expose] public section

namespace Silmaril.Formats.Arrow.TimestampBatch

open Numeric.Timestamp

/-- Interpret the IDL unit on the existing signed tick scale. -/
def tickUnit : SchemaReader.TimestampUnit → TickUnit
  | .second => .second
  | .millisecond => .millisecond
  | .microsecond => .microsecond
  | .nanosecond => .nanosecond

structure Binding where
  name : String
  nullable : Bool
  metadata : ColumnarTimestamp.Arrow.Metadata
  deriving DecidableEq

/-- Bind one normalized Timestamp field for little-endian value decoding. -/
def bindSchema (schema : SchemaReader.Schema) : Except Error Binding :=
  if schema.endianness ≠ .little then .error (.unsupported (.endianness schema.endianness.code))
  else match schema.fields with
    | [⟨name, nullable, .timestamp unit timezone⟩] => .ok ⟨name, nullable, ⟨tickUnit unit, timezone⟩⟩
    | _ => .error (.malformed .batchLayout)

abbrev Value (binding : Binding) := Ticks binding.metadata.kind binding.metadata.unit
abbrev Column (binding : Binding) := List (Option (Value binding))

structure View where
  node : FieldNode
  validity : KBytes
  values : Bytes

/-- Check the declared body extent, the sole field node, and the ordered bitmap
    and data extents. Pass only the logical value prefix to the exact wire codec. -/
def batchView (limits : Limits) (binding : Binding) (message : Message) (body : KBytes) :
    Except Error View :=
  if !body.wf then .error (.malformed .source)
  else if message.bodyLength ≠ body.len ∨ body.len % 8 ≠ 0 then .error (.malformed .bodyLength)
  else if body.len > limits.bodyBytes then .error (.limit .bodyBytes)
  else if limits.fields = 0 then .error (.limit .fields)
  else match message.header with
    | .schema _ => .error (.malformed .schemaOrder)
    | .recordBatch batch =>
      if batch.rowCount > limits.rows then .error (.limit .rows)
      else match batch.nodes, batch.buffers with
        | [node], [bitmap, data] =>
          if node.length = batch.rowCount ∧ BuffersFit body.len 0 [bitmap, data] then
            let validity := Body.sliceBuffer body bitmap
            if node.nullCount ≤ node.length ∧ (binding.nullable = false → node.nullCount = 0) ∧
                Body.BitmapExtent validity node.length then
              let size := 8 * node.length
              if size ≤ data.length then
                .ok ⟨node, validity, ⟨(body.slice data.offset size).toByteArray⟩⟩
              else .error (.malformed .bodyValues)
            else .error (.malformed .validityBitmap)
          else .error (.malformed .batchLayout)
        | _, _ => .error (.malformed .batchLayout)

/-- Each observation takes its presence from the corresponding LSB-first bit. -/
def place {binding : Binding} (bitmap : KBytes) (entry : Value binding × Nat) :
    Except Error (Option (Value binding)) := do
  let some valid := Body.validAt bitmap entry.2 | throw (.malformed .validityBitmap)
  return if valid then some entry.1 else none

def SlotWire {binding : Binding} (bitmap : KBytes) (entry : Value binding × Nat)
    (value : Option (Value binding)) : Prop :=
  ∃ valid, Body.validAt bitmap entry.2 = some valid ∧
    value = (if valid then some entry.1 else none)

/-- Take the ordered value words from the existing exact Timestamp decoder and
    apply the checked bitmap. Only present slots contribute observed ticks. -/
def decodeBatch (limits : Limits) (binding : Binding) (message : Message) (body : KBytes) :
    Except Error (Column binding) := do
  let view ← batchView limits binding message body
  let ticks ← (binding.metadata.decodeBufferLE view.node.length view.values).mapError
    fun _ => .malformed .bodyValues
  let slots ← ticks.zipIdx.mapM (place view.validity)
  if slots.countP Option.isNone ≠ view.node.nullCount then throw (.malformed .validityBitmap)
  return slots

structure Observation where
  binding : Binding
  slots : Column binding

/-- Decode a standalone batch from two delimited message metadata slices and
    the associated body. The caller supplies the pairing. -/
def readBatch (limits : Limits) (schemaMetadata recordMetadata body : KBytes) :
    Except Error Observation := do
  let binding ← bindSchema (← SchemaReader.readMessage limits schemaMetadata)
  let record ← Arrow.readMessage limits recordMetadata
  return ⟨binding, ← decodeBatch limits binding record body⟩

end Silmaril.Formats.Arrow.TimestampBatch
