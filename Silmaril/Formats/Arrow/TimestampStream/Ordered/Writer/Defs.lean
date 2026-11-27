module

public import Silmaril.Formats.Arrow.TimestampStream.Ordered.Defs

/-! Native IPC emission certified against the ordered TIMESTAMP reader. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.TimestampStream.Ordered.Writer

open Silmaril.Numeric.Timestamp (ConversionError)
open MetadataWriter.Wire

inductive RecordError where
  | ipc (cause : Arrow.Error)
  | columnCount (expected actual : Nat)
  | rowCount (position expected actual : Nat)
  | requiredNull (position : Nat)
  | payload (position : Nat) (cause : ConversionError)
  deriving DecidableEq, Repr

inductive Error where
  | ipc (cause : Arrow.Error)
  | timezone (position : Nat) (actual : Option String)
  | record (index : Nat) (cause : RecordError)
  | readback (cause : Ordered.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

abbrev timestampField := TimestampStream.Writer.Internal.timestampField

def checkTimezone (field : Field) (position : Nat) : Except Error Unit :=
  if supportedTimezone field.metadata.timezone then .ok () else .error (.timezone position field.metadata.timezone)

def schemaMetadata (fields : List Field) : KBytes :=
  messagePrefix 1 56 0 ++ schemaPayloadOf (fields.map timestampField)

def schemaSize (fields : List Field) : Nat :=
  let vectorEnd := 20 + 4 * fields.length
  48 + vectorEnd + Arrow.Writer.padding vectorEnd +
    (fields.map fun field =>
      TimestampStream.Writer.Internal.nameFragmentSize field.name +
        if field.metadata.timezone == some "UTC" then 8 else 0).sum

def emitSchema (limits : Limits) (fields : List Field) : Except Error KBytes := do
  if fields.length > limits.fields then throw (.ipc (.limit .fields))
  fields.zipIdx.forM fun (field, position) => checkTimezone field position
  let size := schemaSize fields
  if size ≥ 2^31 then throw (.ipc (.malformed .metadataLength))
  if size > limits.metadataBytes then throw (.ipc (.limit .metadataBytes))
  return StreamWriter.envelopeBytes size ++ schemaMetadata fields

def compile (rows : Nat) (field : Field) (column : Column) (position : Nat) :
    Except RecordError (FieldNode × List KBytes) := do
  if column.length ≠ rows then throw (.rowCount position rows column.length)
  if !field.nullable && column.any Option.isNone then throw (.requiredNull position)
  let slots : TimestampBatch.Column field := column.map (Option.map fun ticks => ⟨ticks⟩)
  let parts ← (TimestampBatch.Writer.encodeParts field slots).mapError (.payload position)
  return (⟨rows, column.countP Option.isNone⟩, parts)

def emitRecord (limits : Limits) (fields : List Field) (batch : Batch) : Except RecordError KBytes := do
  if batch.columns.length ≠ fields.length then throw (.columnCount fields.length batch.columns.length)
  if fields.length > limits.fields then throw (.ipc (.limit .fields))
  if batch.rowCount > limits.rows then throw (.ipc (.limit .rows))
  if batch.rowCount ≥ 2^63 then throw (.ipc (.malformed .batchLayout))
  let bitmap := (batch.rowCount + 7) / 8
  let bodySize := fields.length * (bitmap + Arrow.Writer.padding bitmap + 8 * batch.rowCount)
  if bodySize ≥ 2^63 then throw (.ipc (.malformed .bodyLength))
  if bodySize > limits.bodyBytes then throw (.ipc (.limit .bodyBytes))
  let columns ← (fields.zip batch.columns).zipIdx.mapM fun ((field, column), position) =>
    compile batch.rowCount field column position
  let (buffers, body) := Arrow.Writer.packBuffers 0 (columns.flatMap Prod.snd)
  let record : RecordBatch := ⟨batch.rowCount, columns.map Prod.fst, buffers⟩
  (StreamWriter.emitFrame limits ⟨.recordBatch record, body.len⟩ body).mapError .ipc

def serialize (limits : ObservationLimits) (fields : List Field) (batches : List Batch) : Except Error KBytes := do
  if batches.length > limits.ipc.batches then throw (.ipc (.limit .batches))
  (Body.checkBudget limits fields.length (batches.map Batch.rowCount).sum).mapError .ipc
  let schema ← emitSchema limits.ipc fields
  let records ← batches.zipIdx.mapM fun (batch, index) => (emitRecord limits.ipc fields batch).mapError (.record index)
  return schema ++ records.foldr (· ++ ·) StreamWriter.eos

/-- Certify the complete native stream, including all positional descriptors
and batch counts, before returning its bytes. -/
def emit (limits : ObservationLimits) (fields : List Field) (batches : List Batch) : Except Error KBytes := do
  let wire ← serialize limits fields batches
  let observed ← (Ordered.read limits.ipc wire).mapError .readback
  if observed = ⟨fields, batches⟩ then .ok wire else .error .readbackMismatch

end Silmaril.Formats.Arrow.TimestampStream.Ordered.Writer
