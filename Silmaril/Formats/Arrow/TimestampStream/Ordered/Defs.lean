module

public import Silmaril.Formats.Arrow.TimestampStream.Writer.Defs

/-! Ordered flat little-endian TIMESTAMP IPC V5 with explicit batch row counts. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.TimestampStream.Ordered

abbrev Field := TimestampBatch.Binding
abbrev Column := List (Option Int)

structure Batch where
  rowCount : Nat
  columns : List Column
  deriving DecidableEq, Repr

def Batch.Aligned (fields : List Field) (batch : Batch) : Prop :=
  batch.columns.length = fields.length ∧ ∀ column ∈ batch.columns, column.length = batch.rowCount

structure Stream where
  fields : List Field
  batches : List Batch
  deriving DecidableEq

def supportedTimezone (timezone : Option String) : Bool :=
  timezone.isNone || timezone == some "UTC"

inductive Error where
  | source
  | schemaEnvelope (cause : Arrow.Error)
  | expectedSchema
  | schemaMetadata (cause : Arrow.Error)
  | bigEndian
  | fieldType (position : Nat) (actual : SchemaReader.FieldType)
  | timezone (position : Nat) (actual : Option String)
  | batch (index : Nat) (cause : TimestampStream.BatchError)
  deriving DecidableEq, Repr

def bindField (field : SchemaReader.Field) (position : Nat) : Except Error Field := do
  let .timestamp unit timezone := field.type | throw (.fieldType position field.type)
  if !supportedTimezone timezone then throw (.timezone position timezone)
  return ⟨field.name, field.nullable, ⟨TimestampBatch.tickUnit unit, timezone⟩⟩

def readSchema (limits : Limits) (input : KBytes) : Except Error (List Field × Nat) := do
  let envelope ← (readEnvelope limits input 0).mapError .schemaEnvelope
  let .metadata size := envelope | throw .expectedSchema
  let schema ← (SchemaReader.readMessage limits (input.slice 8 size)).mapError .schemaMetadata
  if schema.endianness ≠ .little then throw .bigEndian
  let fields ← schema.fields.zipIdx.mapM fun (field, position) => bindField field position
  return (fields, 8 + size)

/-- Give the existing column reader its original field node and buffer pair
without rebasing either descriptor. The caller checks the complete layout. -/
def columnMessage (rows length : Nat) (node : FieldNode) (bitmap values : Buffer) : Message :=
  ⟨.recordBatch ⟨rows, [node], [bitmap, values]⟩, length⟩

def readColumns (limits : Limits) (rows : Nat) (body : KBytes) :
    List Field → List FieldNode → List Buffer → Except Arrow.Error (List Column)
  | [], [], [] => .ok []
  | field :: fields, node :: nodes, bitmap :: values :: buffers => do
    let slots ← TimestampBatch.decodeBatch limits field (columnMessage rows body.len node bitmap values) body
    let rest ← readColumns limits rows body fields nodes buffers
    return TimestampBatch.Writer.tickCounts slots :: rest
  | _, _, _ => .error (.malformed .batchLayout)

def decodeBatch (limits : Limits) (fields : List Field) (batch : RecordBatch) (length : Nat)
    (body : KBytes) : Except Arrow.Error Batch := do
  StreamWriter.checkBody limits ⟨.recordBatch batch, length⟩ body
  if fields.length > limits.fields then throw (.limit .fields)
  if batch.rowCount > limits.rows then throw (.limit .rows)
  if ¬ BuffersFit body.len 0 batch.buffers then throw (.malformed .batchLayout)
  let columns ← readColumns limits batch.rowCount body fields batch.nodes batch.buffers
  return ⟨batch.rowCount, columns⟩

def readBatch (limits : Limits) (input : KBytes) (fields : List Field) (offset size : Nat) :
    Except TimestampStream.BatchError (Batch × Nat) := do
  let bodyStart := offset + 8 + size
  let message ← (Arrow.readMessage limits (input.slice (offset + 8) size)).mapError .metadata
  let .recordBatch batch := message.header | throw .expectedRecordBatch
  let body ← (readBody limits input bodyStart message.bodyLength).mapError .body
  let decoded ← (decodeBatch limits fields batch message.bodyLength body).mapError .values
  return (decoded, bodyStart + message.bodyLength)

def readBatches (limits : Limits) (input : KBytes) (fields : List Field) :
    Nat → Nat → Nat → Except Error (List Batch)
  | remaining, index, offset => do
    let envelope ← (readEnvelope limits input offset).mapError fun cause => .batch index (.envelope cause)
    match envelope with
    | .eos =>
      if offset + 8 = input.len then .ok [] else .error (.batch index .trailingBytes)
    | .metadata size =>
      match remaining with
      | 0 => throw (.batch index .batchLimit)
      | fuel + 1 =>
        let (batch, next) ← (readBatch limits input fields offset size).mapError (.batch index)
        let tail ← readBatches limits input fields fuel (index + 1) next
        return batch :: tail

def read (limits : Limits) (input : KBytes) : Except Error Stream :=
  if !input.wf then .error .source
  else do
    let (fields, start) ← readSchema limits input
    let batches ← readBatches limits input fields limits.batches 0 start
    return ⟨fields, batches⟩

/-- Every original node and validity/value descriptor pair is consumed once. -/
inductive ColumnsWire (limits : Limits) (rows : Nat) (body : KBytes) :
    List Field → List FieldNode → List Buffer → List Column → Prop where
  | nil : ColumnsWire limits rows body [] [] [] []
  | next {field fields node nodes bitmap values buffers slots tail} :
      TimestampBatch.decodeBatch limits field (columnMessage rows body.len node bitmap values) body = .ok slots →
      ColumnsWire limits rows body fields nodes buffers tail →
      ColumnsWire limits rows body (field :: fields) (node :: nodes) (bitmap :: values :: buffers)
        (TimestampBatch.Writer.tickCounts slots :: tail)

def BatchWire (limits : Limits) (fields : List Field) (batch : RecordBatch) (length : Nat)
    (body : KBytes) (decoded : Batch) : Prop :=
  length = body.len ∧ body.wf = true ∧ body.len % 8 = 0 ∧ body.len ≤ limits.bodyBytes ∧
  fields.length ≤ limits.fields ∧ decoded.rowCount = batch.rowCount ∧ decoded.rowCount ≤ limits.rows ∧
  BuffersFit body.len 0 batch.buffers ∧ ColumnsWire limits batch.rowCount body fields batch.nodes batch.buffers decoded.columns

/-- Original record frames in order, followed by EOS at the exact end. -/
inductive BatchesWire (limits : Limits) (input : KBytes) (fields : List Field) :
    Nat → Nat → List Batch → Prop where
  | eos {remaining offset} :
      readEnvelope limits input offset = .ok .eos → offset + 8 = input.len →
      BatchesWire limits input fields remaining offset []
  | next {fuel offset size nextOffset batch tail} :
      readEnvelope limits input offset = .ok (.metadata size) →
      readBatch limits input fields offset size = .ok (batch, nextOffset) →
      BatchesWire limits input fields fuel nextOffset tail →
      BatchesWire limits input fields (fuel + 1) offset (batch :: tail)

end Silmaril.Formats.Arrow.TimestampStream.Ordered
