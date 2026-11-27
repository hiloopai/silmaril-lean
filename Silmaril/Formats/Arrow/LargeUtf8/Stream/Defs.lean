module

public import Silmaril.Formats.Arrow.LargeUtf8.Defs
public import Silmaril.Formats.Arrow.Binary.Stream.Defs

/-! One flat little-endian LargeUtf8 field in a complete Arrow V5 IPC stream. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeUtf8.Stream

abbrev Framing := Binary.Stream.Framing
abbrev Range := Binary.Stream.Range
structure Batch where
  range : Range
  values : LargeUtf8.Column

inductive Cause where
  | ipc (cause : Binary.Stream.Cause)
  | invalidUtf8 (slot : Nat)
  deriving DecidableEq, Repr

def Cause.decode : LargeUtf8.Error → Cause
  | .binary cause => .ipc (.decode cause)
  | .invalidUtf8 slot => .invalidUtf8 slot

inductive Error where
  | schema (cause : Binary.Stream.SchemaFailure)
  | record (ordinal offset : Nat) (cause : Cause)
  deriving DecidableEq, Repr

structure Observed where
  field : LargeUtf8.Field
  batches : List Batch
  eosOffset : Nat

def readSchemaFrame (limits : Limits) (framing : Framing) (input : KBytes) :
    Except Binary.Stream.SchemaFailure (LargeUtf8.Field × Nat) := do
  let envelope ← (framing.readEnvelope limits input 0).mapError .envelope
  let .metadata size := envelope | throw .expectedSchema
  let field ← (LargeUtf8.readSchema limits (input.slice framing.prefixSize size)).mapError .metadata
  return (field, framing.prefixSize + size)

def readRecord (limits : Limits) (framing : Framing) (input : KBytes)
    (field : LargeUtf8.Field) (offset size : Nat) : Except Cause Batch := do
  let message ← (Arrow.readMessage limits (input.slice (offset + framing.prefixSize) size)).mapError (.ipc ∘ Binary.Stream.Cause.metadata)
  let .recordBatch metadata := message.header | throw (.ipc .expectedRecordBatch)
  let range : Range := ⟨offset, framing.prefixSize, size, message.bodyLength⟩
  let body ← (Arrow.readBody limits input range.bodyStart range.bodyLength).mapError (.ipc ∘ Binary.Stream.Cause.body)
  let (node, buffers) ← (Binary.bindBody limits metadata body).mapError (.ipc ∘ Binary.Stream.Cause.decode)
  let values ← (LargeUtf8.readColumn limits field.nullable node buffers).mapError Cause.decode
  return ⟨range, values⟩

/-- Each admitted record consumes a budget unit, including an empty one.
Errors identify the ordinal and absolute prefix offset of the failed attempt. -/
def readBatches (limits : Limits) (framing : Framing) (input : KBytes)
    (field : LargeUtf8.Field) : (remaining ordinal offset : Nat) → Except Error (List Batch × Nat)
  | remaining, ordinal, offset => do
    let envelope ← (framing.readEnvelope limits input offset).mapError
      fun cause => .record ordinal offset (.ipc (.envelope cause))
    match envelope with
    | .eos =>
      if offset + framing.prefixSize = input.len then .ok ([], offset)
      else .error (.record ordinal offset (.ipc .trailingBytes))
    | .metadata size =>
      match remaining with
      | 0 => .error (.record ordinal offset (.ipc .batchLimit))
      | fuel + 1 =>
        let record ← (readRecord limits framing input field offset size).mapError
          fun cause => .record ordinal offset cause
        let (rest, eos) ← readBatches limits framing input field fuel (ordinal + 1) record.range.next
        return (record :: rest, eos)

/-- Read a complete carrier through its explicit EOS, with one framing
profile selected for the entire stream. -/
def read (limits : Limits) (framing : Framing) (input : KBytes) : Except Error Observed :=
  if !input.wf then .error (.schema .source)
  else do
    let (field, start) ← (readSchemaFrame limits framing input).mapError .schema
    let (batches, eos) ← readBatches limits framing input field limits.batches 0 start
    return ⟨field, batches, eos⟩

def RecordWire (limits : Limits) (framing : Framing) (input : KBytes)
    (field : LargeUtf8.Field) (offset size : Nat) (record : Batch) : Prop :=
  let range := record.range
  range = ⟨offset, framing.prefixSize, size, range.bodyLength⟩ ∧ range.next ≤ input.len ∧
    ∃ metadata node buffers,
      Arrow.readMessage limits (input.slice range.metadataStart size) =
        .ok ⟨.recordBatch metadata, range.bodyLength⟩ ∧
      Binary.BodyWire metadata (input.slice range.bodyStart range.bodyLength) node buffers ∧
      Binary.checkColumn limits field.nullable node buffers = .ok () ∧
      LargeUtf8.ColumnWire node buffers record.values

inductive BatchesWire (limits : Limits) (framing : Framing) (input : KBytes)
    (field : LargeUtf8.Field) : Nat → Nat → List Batch → Nat → Prop where
  | eos {remaining offset} :
      framing.readEnvelope limits input offset = .ok .eos →
      offset + framing.prefixSize = input.len →
      BatchesWire limits framing input field remaining offset [] offset
  | more {fuel offset size record rest eos} :
      framing.readEnvelope limits input offset = .ok (.metadata size) →
      RecordWire limits framing input field offset size record →
      BatchesWire limits framing input field fuel record.range.next rest eos →
      BatchesWire limits framing input field (fuel + 1) offset (record :: rest) eos

/-- A failure follows only complete records at their checked original
offsets. The terminal attempt is still at its original ordinal and offset. -/
inductive BatchesFailure (limits : Limits) (framing : Framing) (input : KBytes)
    (field : LargeUtf8.Field) : Nat → Nat → Nat → Error → Prop where
  | envelope {remaining ordinal offset cause} :
      framing.readEnvelope limits input offset = .error cause →
      BatchesFailure limits framing input field remaining ordinal offset
        (.record ordinal offset (.ipc (.envelope cause)))
  | trailing {remaining ordinal offset} :
      framing.readEnvelope limits input offset = .ok .eos →
      offset + framing.prefixSize ≠ input.len →
      BatchesFailure limits framing input field remaining ordinal offset
        (.record ordinal offset (.ipc .trailingBytes))
  | limit {ordinal offset size} :
      framing.readEnvelope limits input offset = .ok (.metadata size) →
      BatchesFailure limits framing input field 0 ordinal offset
        (.record ordinal offset (.ipc .batchLimit))
  | record {fuel ordinal offset size cause} :
      framing.readEnvelope limits input offset = .ok (.metadata size) →
      readRecord limits framing input field offset size = .error cause →
      BatchesFailure limits framing input field (fuel + 1) ordinal offset (.record ordinal offset cause)
  | more {fuel ordinal offset size record error} :
      framing.readEnvelope limits input offset = .ok (.metadata size) →
      RecordWire limits framing input field offset size record →
      BatchesFailure limits framing input field fuel (ordinal + 1) record.range.next error →
      BatchesFailure limits framing input field (fuel + 1) ordinal offset error

def StreamWire (limits : Limits) (framing : Framing) (input : KBytes) (observed : Observed) : Prop :=
  input.wf = true ∧ ∃ schemaSize,
    framing.readEnvelope limits input 0 = .ok (.metadata schemaSize) ∧
    LargeUtf8.readSchema limits (input.slice framing.prefixSize schemaSize) = .ok observed.field ∧
    BatchesWire limits framing input observed.field limits.batches (framing.prefixSize + schemaSize)
      observed.batches observed.eosOffset

end Silmaril.Formats.Arrow.LargeUtf8.Stream
