module

public import Silmaril.Formats.Arrow.LargeBinary.Defs
public import Silmaril.Formats.Arrow.Binary.Stream.Defs

/-! One flat little-endian LargeBinary field in a complete Arrow V5 IPC stream. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeBinary.Stream

abbrev Framing := Binary.Stream.Framing
abbrev Range := Binary.Stream.Range
abbrev Batch := Binary.Stream.Batch
abbrev Error := Binary.Stream.Error

structure Observed where
  field : LargeBinary.Field
  batches : List Batch
  eosOffset : Nat

def readSchemaFrame (limits : Limits) (framing : Framing) (input : KBytes) :
    Except Binary.Stream.SchemaFailure (LargeBinary.Field × Nat) := do
  let envelope ← (framing.readEnvelope limits input 0).mapError .envelope
  let .metadata size := envelope | throw .expectedSchema
  let field ← (LargeBinary.readSchema limits (input.slice framing.prefixSize size)).mapError .metadata
  return (field, framing.prefixSize + size)

def readRecord (limits : Limits) (framing : Framing) (input : KBytes)
    (field : LargeBinary.Field) (offset size : Nat) : Except Binary.Stream.Cause Batch := do
  let message ← (Arrow.readMessage limits (input.slice (offset + framing.prefixSize) size)).mapError .metadata
  let .recordBatch metadata := message.header | throw .expectedRecordBatch
  let range : Range := ⟨offset, framing.prefixSize, size, message.bodyLength⟩
  let body ← (Arrow.readBody limits input range.bodyStart range.bodyLength).mapError .body
  let (node, buffers) ← (Binary.bindBody limits metadata body).mapError .decode
  let values ← (LargeBinary.readColumn limits field.nullable node buffers).mapError .decode
  return ⟨range, values⟩

/-- Each admitted record consumes a budget unit, including an empty one.
Errors identify the ordinal and absolute prefix offset of the failed attempt. -/
def readBatches (limits : Limits) (framing : Framing) (input : KBytes)
    (field : LargeBinary.Field) : (remaining ordinal offset : Nat) → Except Error (List Batch × Nat)
  | remaining, ordinal, offset => do
    let envelope ← (framing.readEnvelope limits input offset).mapError
      fun cause => .record ⟨ordinal, offset, .envelope cause⟩
    match envelope with
    | .eos =>
      if offset + framing.prefixSize = input.len then .ok ([], offset)
      else .error (.record ⟨ordinal, offset, .trailingBytes⟩)
    | .metadata size =>
      match remaining with
      | 0 => .error (.record ⟨ordinal, offset, .batchLimit⟩)
      | fuel + 1 =>
        let record ← (readRecord limits framing input field offset size).mapError
          fun cause => .record ⟨ordinal, offset, cause⟩
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
    (field : LargeBinary.Field) (offset size : Nat) (record : Batch) : Prop :=
  let range := record.range
  range = ⟨offset, framing.prefixSize, size, range.bodyLength⟩ ∧ range.next ≤ input.len ∧
    ∃ metadata node buffers,
      Arrow.readMessage limits (input.slice range.metadataStart size) =
        .ok ⟨.recordBatch metadata, range.bodyLength⟩ ∧
      Binary.BodyWire metadata (input.slice range.bodyStart range.bodyLength) node buffers ∧
      Binary.checkColumn limits field.nullable node buffers = .ok () ∧
      LargeBinary.ColumnWire node buffers record.values

inductive BatchesWire (limits : Limits) (framing : Framing) (input : KBytes)
    (field : LargeBinary.Field) : Nat → Nat → List Batch → Nat → Prop where
  | eos {remaining offset} :
      framing.readEnvelope limits input offset = .ok .eos →
      offset + framing.prefixSize = input.len →
      BatchesWire limits framing input field remaining offset [] offset
  | more {fuel offset size record rest eos} :
      framing.readEnvelope limits input offset = .ok (.metadata size) →
      RecordWire limits framing input field offset size record →
      BatchesWire limits framing input field fuel record.range.next rest eos →
      BatchesWire limits framing input field (fuel + 1) offset (record :: rest) eos

def StreamWire (limits : Limits) (framing : Framing) (input : KBytes) (observed : Observed) : Prop :=
  input.wf = true ∧ ∃ schemaSize,
    framing.readEnvelope limits input 0 = .ok (.metadata schemaSize) ∧
    LargeBinary.readSchema limits (input.slice framing.prefixSize schemaSize) = .ok observed.field ∧
    BatchesWire limits framing input observed.field limits.batches (framing.prefixSize + schemaSize)
      observed.batches observed.eosOffset

end Silmaril.Formats.Arrow.LargeBinary.Stream
