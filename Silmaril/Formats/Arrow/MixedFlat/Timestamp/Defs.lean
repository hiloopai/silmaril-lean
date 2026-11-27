module

public import Silmaril.Formats.Arrow.MixedFlat.Defs
public import Silmaril.Formats.Arrow.TimestampStream.Ordered.Defs

/-! Ordered flat INT32, UTF8 and TIMESTAMP in a bounded native IPC V5 stream. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Timestamp


inductive Kind where
  | int32
  | utf8
  | timestamp (metadata : ColumnarTimestamp.Arrow.Metadata)
  deriving DecidableEq

structure Field where
  name : String
  nullable : Bool
  kind : Kind
  deriving DecidableEq

inductive Column where
  | int32 (values : List (Option Int32))
  | utf8 (values : List (Option String))
  | timestamp (counts : List (Option Int))
  deriving DecidableEq, Repr

structure Batch where
  rowCount : Nat
  columns : List Column
  deriving DecidableEq, Repr

structure Stream where
  fields : List Field
  batches : List Batch
  deriving DecidableEq

def Field.timestampBinding (field : Field) (metadata : ColumnarTimestamp.Arrow.Metadata) :
    TimestampBatch.Binding := ⟨field.name, field.nullable, metadata⟩

/-- Descriptor assignment needs only the name, nullability and buffer
arity. The two-buffer TIMESTAMP layout shares the fixed-width arity. -/
def Field.layout (field : Field) : MixedFlat.Field :=
  ⟨field.name, field.nullable, .primitive (match field.kind with
    | .utf8 => .utf8
    | .int32 | .timestamp _ => .int32)⟩

inductive BatchError where
  | envelope (cause : Arrow.Error)
  | trailingBytes
  | batchLimit
  | metadata (cause : Arrow.Error)
  | expectedRecordBatch
  | body (cause : Arrow.Error)
  | budget (cause : Arrow.Error)
  | layout (cause : MixedFlat.Error)
  | column (position : Nat) (cause : Arrow.Error)
  | assignment
  deriving DecidableEq, Repr

inductive Error where
  | source
  | schemaEnvelope (cause : Arrow.Error)
  | expectedSchema
  | schemaMetadata (cause : Arrow.Error)
  | bigEndian
  | fieldType (position : Nat) (actual : SchemaReader.FieldType)
  | timezone (position : Nat) (actual : Option String)
  | batch (index : Nat) (cause : BatchError)
  deriving DecidableEq, Repr

def bindField (field : SchemaReader.Field) (position : Nat) : Except Error Field := do
  let kind ← match field.type with
    | .primitive .int32 => .ok Kind.int32
    | .primitive .utf8 => .ok .utf8
    | .timestamp unit timezone =>
      if TimestampStream.Ordered.supportedTimezone timezone then
        .ok (.timestamp ⟨TimestampBatch.tickUnit unit, timezone⟩)
      else .error (.timezone position timezone)
    | other => .error (.fieldType position other)
  return ⟨field.name, field.nullable, kind⟩

def readSchema (limits : Arrow.Limits) (input : KBytes) : Except Error (List Field × Nat) := do
  let envelope ← (readEnvelope limits input 0).mapError .schemaEnvelope
  let .metadata size := envelope | throw .expectedSchema
  let schema ← (SchemaReader.readMessage limits (input.slice 8 size)).mapError .schemaMetadata
  if schema.endianness ≠ .little then throw .bigEndian
  let fields ← schema.fields.zipIdx.mapM fun (field, position) => bindField field position
  return (fields, 8 + size)

def primitiveSlot {α : Type} (extract : Arrow.Value → Option α) :
    Option Arrow.Value → Except Arrow.Error (Option α)
  | none => .ok none
  | some value => match extract value with
    | some result => .ok (some result)
    | none => .error (.malformed .batchLayout)

def readColumn (limits : Arrow.Limits) (body : KBytes) (field : Field) {rows : Nat} (group : MixedFlat.Group rows) :
    Except Arrow.Error Column := do
  match field.kind with
  | .timestamp metadata =>
    let [bitmap, values] := group.buffers | throw (.malformed .batchLayout)
    let binding := field.timestampBinding metadata
    let message := TimestampStream.Ordered.columnMessage rows body.len group.node bitmap values
    let slots ← TimestampBatch.decodeBatch limits binding message body
    return .timestamp (TimestampBatch.Writer.tickCounts slots)
  | .int32 | .utf8 =>
    let .primitive kind := field.layout.kind | throw (.malformed .batchLayout)
    let some (buffers, []) := Body.nextColumn body kind group.buffers | throw (.malformed .batchLayout)
    let slots ← Body.readColumn group.node buffers
    match kind with
    | .int32 =>
      return .int32 (← slots.mapM (primitiveSlot fun | .int32 value => some value | _ => none))
    | .utf8 =>
      return .utf8 (← slots.mapM (primitiveSlot fun | .utf8 value => some value | _ => none))

def readColumns (limits : Arrow.Limits) (body : KBytes) {rows : Nat} :
    Nat → List Field → List (MixedFlat.Group rows) → Except BatchError (List Column)
  | _, [], [] => .ok []
  | index, field :: fields, group :: groups => do
    let column ← (readColumn limits body field group).mapError (.column index)
    let rest ← readColumns limits body (index + 1) fields groups
    return column :: rest
  | _, _, _ => .error .assignment

def recordMetadata (record : RecordBatch) (length : Nat) : MixedFlat.Metadata :=
  ⟨record, length, []⟩

def readParsed (limits : ObservationLimits) (fields : List Field) (record : RecordBatch)
    (length : Nat) (body : KBytes) : Except BatchError Batch := do
  let plan ← (MixedFlat.bindBatch {observation := limits} (fields.map Field.layout)
    (recordMetadata record length) body).mapError .layout
  let columns ← readColumns limits.ipc body 0 fields plan.assignment.groups
  return ⟨record.rowCount, columns⟩

def readRecord (limits : ObservationLimits) (input : KBytes) (fields : List Field)
    (rows offset size : Nat) : Except BatchError (Batch × Nat) := do
  let bodyStart := offset + 8 + size
  let message ← (Arrow.readMessage limits.ipc (input.slice (offset + 8) size)).mapError .metadata
  let .recordBatch record := message.header | throw .expectedRecordBatch
  let body ← (readBody limits.ipc input bodyStart message.bodyLength).mapError .body
  (Body.checkBudget limits fields.length (rows + record.rowCount)).mapError .budget
  let batch ← readParsed limits fields record message.bodyLength body
  return (batch, bodyStart + message.bodyLength)

def readBatches (limits : ObservationLimits) (input : KBytes) (fields : List Field) :
    Nat → Nat → Nat → Nat → Except Error (List Batch)
  | remaining, index, rows, offset => do
    let envelope ← (readEnvelope limits.ipc input offset).mapError (.batch index ∘ .envelope)
    match envelope with
    | .eos => if offset + 8 = input.len then .ok [] else .error (.batch index .trailingBytes)
    | .metadata size =>
      match remaining with
      | 0 => throw (.batch index .batchLimit)
      | fuel + 1 =>
        let (batch, next) ← (readRecord limits input fields rows offset size).mapError (.batch index)
        let tail ← readBatches limits input fields fuel (index + 1) (rows + batch.rowCount) next
        return batch :: tail

def read (limits : ObservationLimits) (input : KBytes) : Except Error Stream := do
  if !input.wf then throw .source
  let (fields, start) ← readSchema limits.ipc input
  let batches ← readBatches limits input fields limits.ipc.batches 0 0 start
  return ⟨fields, batches⟩

/-- The record retains the exact original schema-order assignment and
observes the decoded columns and explicit row count of that record. -/
def BatchWire (limits : ObservationLimits) (fields : List Field) (record : RecordBatch)
    (length : Nat) (body : KBytes) (batch : Batch) : Prop :=
  ∃ plan : MixedFlat.Plan (fields.map Field.layout) (recordMetadata record length) body,
    MixedFlat.bindBatch {observation := limits} (fields.map Field.layout)
      (recordMetadata record length) body = .ok plan ∧
    batch.rowCount = record.rowCount ∧
    readColumns limits.ipc body 0 fields plan.assignment.groups = .ok batch.columns

/-- Each successful record consumes its original metadata and body,
with an explicit cumulative budget. EOS occupies the exact final eight bytes. -/
inductive BatchesWire (limits : ObservationLimits) (input : KBytes) (fields : List Field) :
    Nat → Nat → Nat → List Batch → Prop where
  | eos {remaining rows offset} :
      readEnvelope limits.ipc input offset = .ok .eos →
      offset + 8 = input.len →
      BatchesWire limits input fields remaining rows offset []
  | record {remaining rows offset size record length body batch batches} :
      readEnvelope limits.ipc input offset = .ok (.metadata size) →
      Arrow.readMessage limits.ipc (input.slice (offset + 8) size) = .ok ⟨.recordBatch record, length⟩ →
      readBody limits.ipc input (offset + 8 + size) length = .ok body →
      Body.checkBudget limits fields.length (rows + record.rowCount) = .ok () →
      BatchWire limits fields record length body batch →
      BatchesWire limits input fields remaining (rows + batch.rowCount) (offset + 8 + size + length) batches →
      BatchesWire limits input fields (remaining + 1) rows offset (batch :: batches)

end Silmaril.Formats.Arrow.MixedFlat.Timestamp
