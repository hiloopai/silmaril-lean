module

public import Silmaril.Formats.Arrow.Binary.Stream.Defs
public import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Defs
public import Silmaril.Formats.Arrow.StreamWriter.Defs

/-! One plain Binary field in a modern Arrow V5 IPC stream. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.Binary.StreamWriter

namespace Wire

open MetadataWriter.Wire

def schema (field : Binary.Field) : KBytes :=
  let emptyType := words [halfwords 4 4, 0, 8, 0, 0]
  messagePrefix 1 56 0 ++ schemaPayloadOf [fieldFragment field.name field.nullable 4 emptyType]

/-- The field fragment starts at byte 72 and includes a 53-byte prefix and
terminator before padding. -/
def schemaSize (field : Binary.Field) : Nat :=
  let fragment := 53 + field.name.utf8ByteSize
  72 + fragment + Arrow.Writer.padding fragment

end Wire

inductive RecordError where
  | ipc (cause : Arrow.Error)
  | nullInRequired
  | signedOffsetExtent (bytes : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | ipc (cause : Arrow.Error)
  | record (ordinal : Nat) (cause : RecordError)
  | readback (cause : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def valueSize (value : Option KBytes) : Nat := (value.getD KBytes.empty).len

def dataSize (values : Binary.Column) : Nat :=
  values.foldl (fun offset value => offset + valueSize value) 0

def bodySize (rows bytes : Nat) : Nat :=
  ([(rows + 7) / 8, 4 * (rows + 1), bytes].map
    (fun size => size + Arrow.Writer.padding size)).sum

/-- Check the input before building any body buffers. The terminal data offset
bounds every signed i32 offset in the batch. -/
def checkRecord (limits : Limits) (nullable : Bool) (values : Binary.Column) :
    Except RecordError FieldNode := do
  let rows := values.length
  if rows > limits.rows then throw (.ipc (.limit .rows))
  let nulls := values.countP Option.isNone
  if !nullable && nulls != 0 then throw .nullInRequired
  let bytes := dataSize values
  if bytes ≥ 2^31 then throw (.signedOffsetExtent bytes)
  let paddedBytes := bodySize rows bytes
  if paddedBytes > limits.bodyBytes then throw (.ipc (.limit .bodyBytes))
  if rows ≥ 2^63 || paddedBytes ≥ 2^63 then throw (.ipc (.malformed .batchLayout))
  if !values.all (fun value => (value.map KBytes.wf).getD true) then
    throw (.ipc (.malformed .source))
  return ⟨rows, nulls⟩

/-- Plain Binary uses three non-variadic buffers. Null and empty values both
repeat the current offset, and their validity bits distinguish them. -/
def columnParts (values : Binary.Column) : List KBytes :=
  let offsets := values.scanl (fun offset value => offset + valueSize value) 0
  let data := BinaryView.Column.Writer.join (values.filterMap id)
  [Arrow.Writer.emitBitmap values, Arrow.Writer.emitWords 4 offsets, data]

def emitRecord (limits : Limits) (field : Binary.Field) (values : Binary.Column) :
    Except RecordError KBytes := do
  let node ← checkRecord limits field.nullable values
  let (descriptors, body) := Arrow.Writer.packBuffers 0 (columnParts values)
  let metadata : RecordBatch := ⟨node.length, [node], descriptors⟩
  (Arrow.StreamWriter.emitFrame limits ⟨.recordBatch metadata, body.len⟩ body).mapError .ipc

def serialize (limits : Limits) (field : Binary.Field) (batches : List Binary.Column) :
    Except Error KBytes := do
  if limits.fields = 0 then throw (.ipc (.limit .fields))
  if batches.length > limits.batches then throw (.ipc (.limit .batches))
  let size := Wire.schemaSize field
  let _ ← (Arrow.readPrefix limits 0xffffffff size).mapError .ipc
  let records ← batches.zipIdx.mapM fun (values, ordinal) =>
    (emitRecord limits field values).mapError (.record ordinal)
  let schema := Arrow.StreamWriter.envelopeBytes size ++ Wire.schema field
  return schema ++ (BinaryView.Column.Writer.join records ++ Arrow.StreamWriter.eos)

def observe (column : Binary.Column) : List (Option (List UInt8)) :=
  column.map (Option.map KBytes.toList)

def Agrees (field : Binary.Field) (batches : List Binary.Column) (decoded : Stream.Observed) : Prop :=
  decoded.field = field ∧ decoded.batches.map (observe ∘ Stream.Batch.values) = batches.map observe

instance (field : Binary.Field) (batches : List Binary.Column) (decoded : Stream.Observed) :
    Decidable (Agrees field batches decoded) := by
  unfold Agrees
  infer_instance

/-- Certify the emitted wire against the checked stream reader, including the
declared field, exact optional octets and every batch boundary. -/
def emit (limits : Limits) (field : Binary.Field) (batches : List Binary.Column) :
    Except Error KBytes := do
  let wire ← serialize limits field batches
  let decoded ← (Stream.read limits .modern wire).mapError .readback
  if Agrees field batches decoded then .ok wire else .error .readbackMismatch

end Silmaril.Formats.Arrow.Binary.StreamWriter
