module

public import Silmaril.Formats.Arrow.DateStream.Writer.Defs

/-! Native little-endian V5 streams with one Date32 and one plain Utf8 field. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.DateUtf8Stream

open DateInterop

inductive Order where
  | dateFirst
  | textFirst
  deriving DecidableEq, Repr

def Order.arrange {α : Type*} (order : Order) (date text : α) : α × α :=
  match order with
  | .dateFirst => (date, text)
  | .textFirst => (text, date)

structure Field where
  name : String
  nullable : Bool
  deriving DecidableEq, Repr

structure Schema where
  date : Field
  text : Field
  order : Order
  deriving DecidableEq, Repr

/-- DATE days share the validity and signed four-byte payload of physical Int32. -/
def Schema.physical (schema : Schema) : List Arrow.Field :=
  let (first, second) := schema.order.arrange
    ⟨schema.date.name, schema.date.nullable, .int32⟩ ⟨schema.text.name, schema.text.nullable, .utf8⟩
  [first, second]

structure Batch where
  dates : List (Option Date32.Payload)
  texts : List (Option String)
  deriving DecidableEq, Repr

structure Observed where
  schema : Schema
  batches : List Batch
  deriving DecidableEq, Repr

inductive ReadError where
  | ipc (cause : Arrow.Error)
  | schema
  deriving DecidableEq, Repr

def readSchema (ipc : Arrow.Limits) (input : KBytes) : Except ReadError (Schema × Nat) := do
  let .metadata size ← (readEnvelope ipc input 0).mapError .ipc | throw .schema
  let wire ← (SchemaReader.readMessage ipc (input.slice 8 size)).mapError .ipc
  if wire.endianness ≠ .little then throw .schema
  match wire.fields with
  | [⟨day, dayNull, .date .day⟩, ⟨text, textNull, .primitive .utf8⟩] =>
    return (⟨⟨day, dayNull⟩, ⟨text, textNull⟩, .dateFirst⟩, 8 + size)
  | [⟨text, textNull, .primitive .utf8⟩, ⟨day, dayNull, .date .day⟩] =>
    return (⟨⟨day, dayNull⟩, ⟨text, textNull⟩, .textFirst⟩, 8 + size)
  | _ => throw .schema

def decodeBatch (limits : ObservationLimits) (schema : Schema) (frame : BatchFrame schema.physical) :
    Except Arrow.Error Batch := do
  Body.checkBatch limits frame
  let [first, second] ← Body.readColumns frame.body schema.physical frame.metadata.nodes frame.metadata.buffers
    | throw (.malformed .batchLayout)
  let (day, text) := schema.order.arrange first second
  let dates ← day.mapM (Option.mapM fun
    | .int32 word => .ok word
    | .utf8 _ => .error (.malformed .batchLayout))
  let texts ← text.mapM (Option.mapM fun
    | .utf8 value => .ok value
    | .int32 _ => .error (.malformed .batchLayout))
  return ⟨dates, texts⟩

/-- Check the logical schema before decoding physical buffers and consume
all frames through the shared exact-EOS reader. -/
def read (limits : ObservationLimits) (input : KBytes) : Except ReadError Observed := do
  if !input.wf then throw (.ipc (.malformed .source))
  let ipc := limits.ipc
  let (schema, start) ← readSchema ipc input
  let frames ← (Arrow.Stream.readBatches ipc input schema.physical ipc.batches start []).mapError .ipc
  (Body.checkBudget limits 2 (frames.map fun frame => frame.metadata.rowCount).sum).mapError .ipc
  return ⟨schema, ← (frames.mapM (decodeBatch limits schema)).mapError .ipc⟩

inductive Error where
  | ipc (cause : Arrow.Error)
  | record (index : Nat) (cause : Arrow.Error)
  | readback (cause : ReadError)
  | readbackMismatch
  deriving DecidableEq, Repr

def emitSchema (ipc : Arrow.Limits) (schema : Schema) : Except Error KBytes := do
  if ipc.fields < 2 then throw (.ipc (.limit .fields))
  let size := MetadataWriter.wireSize ⟨.schema schema.physical, 0⟩
  if size ≥ 2^31 then throw (.ipc (.malformed .metadataLength))
  if size > ipc.metadataBytes then throw (.ipc (.limit .metadataBytes))
  let (first, second) := schema.order.arrange
    (DateStream.Writer.date32FieldBytes schema.date.name schema.date.nullable)
    (MetadataWriter.Wire.fieldBytes ⟨schema.text.name, schema.text.nullable, .utf8⟩)
  let bytes := MetadataWriter.Wire.messagePrefix 1 56 0 ++
    MetadataWriter.Wire.schemaPayloadOf [first, second]
  return StreamWriter.envelopeBytes size ++ bytes

def recordInput (schema : Schema) (batch : Batch) : Writer.BatchInput :=
  let (first, second) := schema.order.arrange
    ⟨schema.date.name, schema.date.nullable, .int32 batch.dates⟩
    ⟨schema.text.name, schema.text.nullable, .utf8 batch.texts⟩
  ⟨batch.dates.length, [first, second]⟩

def serialize (limits : ObservationLimits) (schema : Schema) (batches : List Batch) : Except Error KBytes := do
  if batches.length > limits.ipc.batches then throw (.ipc (.limit .batches))
  (Body.checkBudget limits 2 (batches.map fun batch => batch.dates.length).sum).mapError .ipc
  let header ← emitSchema limits.ipc schema
  let records ← batches.zipIdx.mapM fun (batch, index) =>
    (StreamWriter.emitRecord limits schema.physical (recordInput schema batch)).mapError (.record index)
  return header ++ records.foldr (· ++ ·) StreamWriter.eos

/-- Certify the exact logical schema, nullable slots and ordered record
boundaries before publishing the stream. -/
def emit (limits : ObservationLimits) (schema : Schema) (batches : List Batch) : Except Error KBytes := do
  let wire ← serialize limits schema batches
  let decoded ← (read limits wire).mapError .readback
  if decoded = ⟨schema, batches⟩ then return wire else throw .readbackMismatch

end Silmaril.Formats.Arrow.DateUtf8Stream
