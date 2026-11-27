module

public import Silmaril.Formats.Arrow.LargeUtf8.Stream.Defs
public import Silmaril.Formats.Arrow.Binary.StreamWriter.Defs

/-! One flat LargeUtf8 field in a canonical modern Arrow V5 IPC stream. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeUtf8.StreamWriter

inductive Error where
  | serialize (cause : Binary.StreamWriter.Error)
  | readback (cause : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- Check the body and fixed metadata shape without building offsets,
validity or data buffers. Text is counted in UTF-8 bytes. -/
def checkRecord (limits : Limits) (nullable : Bool) (values : LargeUtf8.Column) :
    Except Binary.StreamWriter.RecordError Unit := do
  let _ ← Binary.StreamWriter.checkRecordSize .i64 limits nullable values Writer.utf8ByteCount
  let shape : RecordBatch := ⟨0, [⟨0, 0⟩], List.replicate 3 ⟨0, 0⟩⟩
  let size := MetadataWriter.wireSize ⟨.recordBatch shape, 0⟩
  let _ ← (Arrow.readPrefix limits 0xffffffff size).mapError .ipc

/-- Admit every batch and the schema before materializing the UTF-8 payload. -/
def preflight (limits : Limits) (field : LargeUtf8.Field) (batches : List LargeUtf8.Column) :
    Except Binary.StreamWriter.Error Unit := do
  let _ ← Binary.StreamWriter.checkStreamHeader limits field.name batches.length
  for (values, ordinal) in batches.zipIdx do
    (checkRecord limits field.nullable values).mapError (.record ordinal)

def encodeValue (text : String) : KBytes :=
  Writer.emitWords 1 ((Writer.utf8Part (some text)).map UInt8.toNat)

def encodeColumn (values : LargeUtf8.Column) : Binary.Column :=
  values.map (Option.map encodeValue)

def serialize (limits : Limits) (field : LargeUtf8.Field) (batches : List LargeUtf8.Column) :
    Except Binary.StreamWriter.Error KBytes := do
  preflight limits field batches
  Binary.StreamWriter.serializeProfile .largeUtf8 limits field.name field.nullable
    (batches.map encodeColumn)

def Agrees (field : LargeUtf8.Field) (batches : List LargeUtf8.Column)
    (decoded : Stream.Observed) : Prop :=
  decoded.field = field ∧ decoded.batches.map Stream.Batch.values = batches

instance (field : LargeUtf8.Field) (batches : List LargeUtf8.Column) (decoded : Stream.Observed) :
    Decidable (Agrees field batches decoded) := by
  unfold Agrees
  infer_instance

/-- Certify the descriptor, each batch's exact nullable strings and exact EOS
with the checked modern stream reader. -/
def emit (limits : Limits) (field : LargeUtf8.Field) (batches : List LargeUtf8.Column) :
    Except Error KBytes := do
  let wire ← (serialize limits field batches).mapError .serialize
  let decoded ← (Stream.read limits .modern wire).mapError .readback
  if Agrees field batches decoded then .ok wire else .error .readbackMismatch

end Silmaril.Formats.Arrow.LargeUtf8.StreamWriter
