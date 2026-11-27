module

public import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Defs
public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
public import Silmaril.Formats.Arrow.TimestampStream.Ordered.Writer.Defs

/-! Checked native emission for the ordered INT32, UTF8 and TIMESTAMP profile. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer

open MetadataWriter.Wire

inductive RecordError where
  | ipc (cause : Arrow.Error)
  | columnCount (expected actual : Nat)
  | columnType (position : Nat)
  | primitive (cause : MixedFlat.OrderedWriter.RecordError)
  | timestamp (cause : TimestampStream.Ordered.Writer.RecordError)
  deriving DecidableEq, Repr

inductive Error where
  | ipc (cause : Arrow.Error)
  | timezone (position : Nat) (actual : Option String)
  | record (index : Nat) (cause : RecordError)
  | readback (cause : Timestamp.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def fieldBytes (field : Field) : KBytes :=
  match field.kind with
  | .int32 => MetadataWriter.Wire.fieldBytes ⟨field.name, field.nullable, .int32⟩
  | .utf8 => MetadataWriter.Wire.fieldBytes ⟨field.name, field.nullable, .utf8⟩
  | .timestamp metadata => TimestampStream.Ordered.Writer.timestampField (field.timestampBinding metadata)

def fieldSize (field : Field) : Nat :=
  let base := TimestampStream.Writer.Internal.nameFragmentSize field.name
  match field.kind with
  | .timestamp metadata => base + if metadata.timezone == some "UTC" then 8 else 0
  | .int32 | .utf8 => base

def schemaSize (fields : List Field) : Nat :=
  let vectorEnd := 20 + 4 * fields.length
  48 + vectorEnd + Arrow.Writer.padding vectorEnd + (fields.map fieldSize).sum

def emitSchema (limits : Arrow.Limits) (fields : List Field) : Except Error KBytes := do
  if fields.length > limits.fields then throw (.ipc (.limit .fields))
  fields.zipIdx.forM fun (field, position) =>
    match field.kind with
    | .timestamp metadata =>
      if TimestampStream.Ordered.supportedTimezone metadata.timezone then .ok ()
      else .error (.timezone position metadata.timezone)
    | .int32 | .utf8 => .ok ()
  let size := schemaSize fields
  if size ≥ 2^31 then throw (.ipc (.malformed .metadataLength))
  if size > limits.metadataBytes then throw (.ipc (.limit .metadataBytes))
  return StreamWriter.envelopeBytes size ++ (messagePrefix 1 56 0 ++ schemaPayloadOf (fields.map fieldBytes))

def bufferSizes : Column → List Nat
  | .int32 values => (Arrow.Writer.ColumnValues.int32 values).bufferSizes
  | .utf8 values => (Arrow.Writer.ColumnValues.utf8 values).bufferSizes
  | .timestamp counts => [(counts.length + 7) / 8, 8 * counts.length]

def compile (limits : ObservationLimits) (rows : Nat) (field : Field) (column : Column)
    (position : Nat) : Except RecordError (FieldNode × List KBytes) := do
  let primitive := fun (column : MixedFlat.OrderedWriter.Column) =>
    ((column.compile {observation := limits} rows position).map
      (fun physical => (physical.node, physical.parts))).mapError RecordError.primitive
  match field.kind, column with
  | .int32, .int32 values => primitive (.int32 field.name field.nullable values)
  | .utf8, .utf8 values => primitive (.utf8 field.name field.nullable values)
  | .timestamp metadata, .timestamp counts =>
    (TimestampStream.Ordered.Writer.compile rows (field.timestampBinding metadata) counts position).mapError .timestamp
  | _, _ => throw (.columnType position)

def checkRecord (limits : ObservationLimits) (fields : List Field) (batch : Batch) :
    Except RecordError Unit := do
  let ipc := limits.ipc
  if batch.columns.length ≠ fields.length then throw (.columnCount fields.length batch.columns.length)
  if fields.length > ipc.fields then throw (.ipc (.limit .fields))
  if batch.rowCount > ipc.rows then throw (.ipc (.limit .rows))
  if batch.rowCount ≥ 2^63 then throw (.ipc (.malformed .batchLayout))
  (Body.checkBudget limits fields.length batch.rowCount).mapError .ipc
  let sizes := batch.columns.flatMap bufferSizes
  let metadata := 104 + 16 * fields.length + 16 * sizes.length
  if metadata ≥ 2^31 then throw (.ipc (.malformed .metadataLength))
  if metadata > ipc.metadataBytes then throw (.ipc (.limit .metadataBytes))
  let body := (sizes.map fun size => size + Arrow.Writer.padding size).sum
  if body ≥ 2^63 then throw (.ipc (.malformed .bodyLength))
  if body > ipc.bodyBytes then throw (.ipc (.limit .bodyBytes))

def encodeRecord (limits : Arrow.Limits) (rows : Nat) (columns : List (FieldNode × List KBytes)) :
    Except RecordError KBytes :=
  let (buffers, body) := Arrow.Writer.packBuffers 0 (columns.flatMap Prod.snd)
  let record : RecordBatch := ⟨rows, columns.map Prod.fst, buffers⟩
  (StreamWriter.emitFrame limits ⟨.recordBatch record, body.len⟩ body).mapError .ipc

def emitRecord (limits : ObservationLimits) (fields : List Field) (batch : Batch) :
    Except RecordError KBytes := do
  checkRecord limits fields batch
  let columns ← (fields.zip batch.columns).zipIdx.mapM fun ((field, column), position) =>
    compile limits batch.rowCount field column position
  encodeRecord limits.ipc batch.rowCount columns

def serialize (limits : ObservationLimits) (stream : Stream) : Except Error KBytes := do
  if stream.batches.length > limits.ipc.batches then throw (.ipc (.limit .batches))
  (Body.checkBudget limits stream.fields.length (stream.batches.map Batch.rowCount).sum).mapError .ipc
  let schema ← emitSchema limits.ipc stream.fields
  let records ← stream.batches.zipIdx.mapM fun (batch, index) =>
    (emitRecord limits stream.fields batch).mapError (.record index)
  return schema ++ records.foldr (· ++ ·) StreamWriter.eos

/-- Certify exact positional fields and batches with the bounded mixed reader. -/
def emit (limits : ObservationLimits) (stream : Stream) : Except Error KBytes := do
  let wire ← serialize limits stream
  let decoded ← (Timestamp.read limits wire).mapError .readback
  if decoded = stream then return wire else throw .readbackMismatch

end Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer
