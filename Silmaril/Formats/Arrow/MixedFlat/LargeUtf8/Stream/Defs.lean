module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Defs
public import Silmaril.Formats.Arrow.Binary.Stream.Defs

/-! Ordered mixed-flat V5 stream decoding with exact terminal context. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream

abbrev Framing := Binary.Stream.Framing
abbrev Range := Binary.Stream.Range

structure Batch where
  range : Range
  observed : LargeUtf8.Observed

inductive SchemaError where
  | source
  | envelope (cause : Arrow.Error)
  | expectedSchema
  | metadata (cause : Arrow.Error)
  deriving DecidableEq, Repr

inductive Cause where
  | envelope (cause : Arrow.Error)
  | trailingBytes
  | batchLimit
  | metadata (cause : MetadataError)
  | body (cause : Arrow.Error)
  | budget (cause : Arrow.Error)
  | decode (cause : LargeUtf8.Error)
  deriving DecidableEq, Repr

inductive Termination where
  | eos (offset : Nat)
  | error (ordinal offset : Nat) (cause : Cause)
  deriving DecidableEq, Repr

structure Trace where
  batches : List Batch
  termination : Termination

structure Observed where
  fields : List Field
  trace : Trace

def readSchemaFrame (limits : Arrow.Limits) (framing : Framing) (input : KBytes) :
    Except SchemaError (List Field × Nat) := do
  let envelope ← (framing.readEnvelope limits input 0).mapError .envelope
  let .metadata size := envelope | throw .expectedSchema
  let fields ← (LargeUtf8.readSchema limits (input.slice framing.prefixSize size)).mapError .metadata
  return (fields, framing.prefixSize + size)

/-- Check metadata and the original body envelope before applying the
running row and cell budgets and decoding the assigned columns. -/
def readRecord (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes)
    (fields : List Field) (rowsBefore offset size : Nat) : Except Cause Batch := do
  let metadata ← (LargeUtf8.readMetadata limits fields
    (input.slice (offset + framing.prefixSize) size)).mapError .metadata
  let range : Range := ⟨offset, framing.prefixSize, size, metadata.bodyLength⟩
  let body ← (Arrow.readBody limits.observation.ipc input range.bodyStart range.bodyLength).mapError .body
  (Body.checkBudget limits.observation fields.length (rowsBefore + metadata.batch.rowCount)).mapError .budget
  let observed ← (LargeUtf8.readParsed limits fields metadata body).mapError .decode
  return ⟨range, observed⟩

/-- Keep the completed records on any late error. No partial record enters
the trace, and an explicit empty record consumes a batch slot. -/
def readBatches (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes) (fields : List Field) :
    (remaining ordinal rowsBefore offset : Nat) → Trace
  | remaining, ordinal, rowsBefore, offset =>
    match framing.readEnvelope limits.observation.ipc input offset with
    | .error cause => ⟨[], .error ordinal offset (.envelope cause)⟩
    | .ok .eos =>
      if offset + framing.prefixSize = input.len then ⟨[], .eos offset⟩
      else ⟨[], .error ordinal offset .trailingBytes⟩
    | .ok (.metadata size) =>
      match remaining with
      | 0 => ⟨[], .error ordinal offset .batchLimit⟩
      | fuel + 1 =>
        match readRecord limits framing input fields rowsBefore offset size with
        | .error cause => ⟨[], .error ordinal offset cause⟩
        | .ok batch =>
          let rest := readBatches limits framing input fields fuel (ordinal + 1)
            (rowsBefore + batch.observed.rowCount) batch.range.next
          ⟨batch :: rest.batches, rest.termination⟩

/-- Materialize the checked prefix after schema admission. Inspect the
trace termination for exact EOS or the first typed record failure. -/
def read (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes) :
    Except SchemaError Observed :=
  if !input.wf then .error .source
  else do
    let (fields, start) ← readSchemaFrame limits.observation.ipc framing input
    return ⟨fields, readBatches limits framing input fields limits.observation.ipc.batches 0 0 start⟩

def RecordWire (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes)
    (fields : List Field) (rowsBefore offset size : Nat) (batch : Batch) : Prop :=
  ∃ metadata body,
    LargeUtf8.readMetadata limits fields (input.slice (offset + framing.prefixSize) size) = .ok metadata ∧
    batch.range = ⟨offset, framing.prefixSize, size, metadata.bodyLength⟩ ∧
    Arrow.readBody limits.observation.ipc input batch.range.bodyStart batch.range.bodyLength = .ok body ∧
    Body.checkBudget limits.observation fields.length (rowsBefore + metadata.batch.rowCount) = .ok () ∧
    BatchWire limits fields metadata body batch.observed

inductive StopWire (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes)
    (fields : List Field) : Nat → Nat → Nat → Nat → Termination → Prop where
  | eos {remaining ordinal rowsBefore offset} :
      framing.readEnvelope limits.observation.ipc input offset = .ok .eos →
      offset + framing.prefixSize = input.len →
      StopWire limits framing input fields remaining ordinal rowsBefore offset (.eos offset)
  | envelope {remaining ordinal rowsBefore offset cause} :
      framing.readEnvelope limits.observation.ipc input offset = .error cause →
      StopWire limits framing input fields remaining ordinal rowsBefore offset
        (.error ordinal offset (.envelope cause))
  | trailing {remaining ordinal rowsBefore offset} :
      framing.readEnvelope limits.observation.ipc input offset = .ok .eos →
      offset + framing.prefixSize ≠ input.len →
      StopWire limits framing input fields remaining ordinal rowsBefore offset (.error ordinal offset .trailingBytes)
  | batchLimit {ordinal rowsBefore offset size} :
      framing.readEnvelope limits.observation.ipc input offset = .ok (.metadata size) →
      StopWire limits framing input fields 0 ordinal rowsBefore offset (.error ordinal offset .batchLimit)
  | record {fuel ordinal rowsBefore offset size cause} :
      framing.readEnvelope limits.observation.ipc input offset = .ok (.metadata size) →
      readRecord limits framing input fields rowsBefore offset size = .error cause →
      StopWire limits framing input fields (fuel + 1) ordinal rowsBefore offset (.error ordinal offset cause)

/-- Successful records advance ordinal, running rows, and the absolute byte
position in lockstep up to the checked terminal attempt. -/
inductive TraceWire (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes)
    (fields : List Field) : Nat → Nat → Nat → Nat → List Batch → Termination → Prop where
  | stop {remaining ordinal rowsBefore offset terminal} :
      StopWire limits framing input fields remaining ordinal rowsBefore offset terminal →
      TraceWire limits framing input fields remaining ordinal rowsBefore offset [] terminal
  | more {fuel ordinal rowsBefore offset size batch rest terminal} :
      framing.readEnvelope limits.observation.ipc input offset = .ok (.metadata size) →
      RecordWire limits framing input fields rowsBefore offset size batch →
      TraceWire limits framing input fields fuel (ordinal + 1)
        (rowsBefore + batch.observed.rowCount) batch.range.next rest terminal →
      TraceWire limits framing input fields (fuel + 1) ordinal rowsBefore offset (batch :: rest) terminal

def StreamWire (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes) (observed : Observed) : Prop :=
  input.wf = true ∧ ∃ size,
    framing.readEnvelope limits.observation.ipc input 0 = .ok (.metadata size) ∧
    LargeUtf8.readSchema limits.observation.ipc (input.slice framing.prefixSize size) = .ok observed.fields ∧
    TraceWire limits framing input observed.fields limits.observation.ipc.batches 0 0
      (framing.prefixSize + size) observed.trace.batches observed.trace.termination

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream
