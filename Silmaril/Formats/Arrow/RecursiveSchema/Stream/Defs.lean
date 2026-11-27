module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs

/-! Native recursive IPC streams with one checked Schema, ordered logical
RecordBatches and exact modern EOS. A terminal failure retains the completed
prefix and the original failing ordinal and cursor. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Stream

@[expose] public section

structure Completed where
  ordinal : Nat
  offset : Nat
  metadataSize : Nat
  bodyLength : Nat
  observed : Batch.Rows.Observation
  deriving BEq, Repr

def Completed.next (batch : Completed) : Nat :=
  batch.offset + 8 + batch.metadataSize + batch.bodyLength

def Completed.ofFrame {limits : Batch.Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (ordinal : Nat) (frame : Batch.Frame limits schema input offset)
    (observed : Batch.Rows.Observation) : Completed :=
  ⟨ordinal, offset, frame.metadataSize, frame.header.bodyLength, observed⟩

inductive Cause where
  | envelope (original : Arrow.Error)
  | batchLimit
  | trailingBytes
  | batch (original : Batch.Error)
  | rows (original : Batch.Rows.Error)
  deriving DecidableEq, Repr

inductive End where
  | eos (ordinal offset : Nat)
  | failed (ordinal offset : Nat) (cause : Cause)
  deriving DecidableEq, Repr

structure Trace where
  schema : Schema
  schemaEnd : Nat
  batches : List Completed
  terminal : End
  deriving BEq, Repr

/-- A completed batch spends one unit of fuel. Envelope inspection,
including the exact EOS check, still runs at zero remaining batches. -/
inductive Step : Nat → Type where
  | stop {remaining : Nat} (terminal : End) : Step remaining
  | yield {remaining : Nat} (batch : Completed) : Step (remaining + 1)

def pollRecord (limits : Batch.Limits) (schema : Schema) (input : KBytes) (wf : input.wf = true)
    (ordinal offset size : Nat)
    (envelope : Arrow.readEnvelope limits.schema.ipc input offset = .ok (.metadata size)) :
    (remaining : Nat) → Step remaining
  | 0 => .stop (.failed ordinal offset .batchLimit)
  | fuel + 1 =>
    match Batch.readMetadataFrame limits schema input offset size wf envelope with
    | .error cause => .stop (.failed ordinal offset (.batch cause))
    | .ok frame =>
      match Batch.Rows.decode frame with
      | .error cause => .stop (.failed ordinal offset (.rows cause))
      | .ok observed => .yield (remaining := fuel) (Completed.ofFrame ordinal frame observed)

def poll (limits : Batch.Limits) (schema : Schema) (input : KBytes) (wf : input.wf = true)
    (ordinal offset remaining : Nat) : Step remaining :=
  match envelope : Arrow.readEnvelope limits.schema.ipc input offset with
  | .error cause => .stop (.failed ordinal offset (.envelope cause))
  | .ok .eos =>
    if offset + 8 = input.len then .stop (.eos ordinal offset)
    else .stop (.failed ordinal offset .trailingBytes)
  | .ok (.metadata size) =>
    pollRecord limits schema input wf ordinal offset size envelope remaining

/-- Accumulate complete batches in reverse so the drain is tail recursive. -/
def drain (limits : Batch.Limits) (schema : Schema) (input : KBytes) (wf : input.wf = true) :
    Nat → Nat → Nat → List Completed → List Completed × End
  | 0, ordinal, offset, completed =>
    match poll limits schema input wf ordinal offset 0 with
    | .stop terminal => (completed.reverse, terminal)
  | fuel + 1, ordinal, offset, completed =>
    match poll limits schema input wf ordinal offset (fuel + 1) with
    | .stop terminal => (completed.reverse, terminal)
    | .yield batch => drain limits schema input wf fuel (ordinal + 1) batch.next (batch :: completed)

/-- A failed open yields the original schema error. Once it opens, the
result always contains a trace, even if its first record fails. -/
def readTrace (limits : Batch.Limits) (input : KBytes) : Except RecursiveSchema.Error Trace :=
  match opened : RecursiveSchema.readFrame limits.schema input with
  | .error error => .error error
  | .ok (schema, offset) =>
    let (batches, terminal) := drain limits schema input (RecursiveSchema.readFrame_source opened)
      limits.schema.ipc.batches 0 offset []
    .ok ⟨schema, offset, batches, terminal⟩

inductive Error where
  | schema (original : RecursiveSchema.Error)
  | failed (ordinal offset : Nat) (cause : Cause)
  deriving DecidableEq, Repr

/-- Strict success requires the explicit modern EOS to exhaust the input.
Use `readTrace` to retain completed batches after a terminal failure. -/
def read (limits : Batch.Limits) (input : KBytes) : Except Error Trace := do
  let trace ← (readTrace limits input).mapError .schema
  match trace.terminal with
  | .eos .. => return trace
  | .failed ordinal offset cause => .error (.failed ordinal offset cause)

/-- A complete batch binds to the original frame at this cursor and to the
single-batch logical and physical wire witnesses. -/
def RecordWire (limits : Batch.Limits) (schema : Schema) (input : KBytes) (ordinal offset : Nat)
    (record : Completed) : Prop :=
  ∃ (frame : Batch.Frame limits schema input offset) (observed : Batch.Rows.Observation),
    Batch.readFrame limits schema input offset = .ok frame ∧
    Batch.Rows.decode frame = .ok observed ∧
    Batch.Rows.ObservationWire frame observed ∧
    record = Completed.ofFrame ordinal frame observed

/-- The terminal cause at an original cursor, with the stage's exact result.
The budget is checked after the envelope and before any record metadata. -/
inductive FailureWire (limits : Batch.Limits) (schema : Schema) (input : KBytes) (offset : Nat) :
    Nat → Cause → Prop where
  | envelope {remaining cause} :
      Arrow.readEnvelope limits.schema.ipc input offset = .error cause →
      FailureWire limits schema input offset remaining (.envelope cause)
  | trailingBytes {remaining} :
      EnvelopeWire limits.schema.ipc input.toList offset .eos →
      offset + 8 ≠ input.len →
      FailureWire limits schema input offset remaining .trailingBytes
  | batchLimit {size} :
      EnvelopeWire limits.schema.ipc input.toList offset (.metadata size) →
      FailureWire limits schema input offset 0 .batchLimit
  | batch {remaining size cause} :
      EnvelopeWire limits.schema.ipc input.toList offset (.metadata size) →
      Batch.readFrame limits schema input offset = .error cause →
      FailureWire limits schema input offset (remaining + 1) (.batch cause)
  | rows {remaining} {frame : Batch.Frame limits schema input offset} {cause} :
      Batch.readFrame limits schema input offset = .ok frame →
      Batch.Rows.decode frame = .error cause →
      FailureWire limits schema input offset (remaining + 1) (.rows cause)

def EndWire (limits : Batch.Limits) (schema : Schema) (input : KBytes)
    (remaining ordinal offset : Nat) : End → Prop
  | .eos ended atByte =>
    ended = ordinal ∧ atByte = offset ∧
      EnvelopeWire limits.schema.ipc input.toList offset .eos ∧ offset + 8 = input.len
  | .failed failed atByte cause =>
    failed = ordinal ∧ atByte = offset ∧ FailureWire limits schema input offset remaining cause

def StepWire (limits : Batch.Limits) (schema : Schema) (input : KBytes)
    (ordinal offset : Nat) {remaining : Nat} : Step remaining → Prop
  | .stop terminal => EndWire limits schema input remaining ordinal offset terminal
  | .yield batch => RecordWire limits schema input ordinal offset batch

/-- Consecutive completed records before the first terminal outcome.
Each step consumes one batch and advances to its exact frame end. -/
inductive CursorChain (limits : Batch.Limits) (schema : Schema) (input : KBytes) :
    Nat → Nat → Nat → List Completed → End → Prop where
  | stop {remaining ordinal offset terminal} :
      EndWire limits schema input remaining ordinal offset terminal →
      CursorChain limits schema input remaining ordinal offset [] terminal
  | more {remaining ordinal offset batch batches terminal} :
      RecordWire limits schema input ordinal offset batch →
      CursorChain limits schema input remaining (ordinal + 1) batch.next batches terminal →
      CursorChain limits schema input (remaining + 1) ordinal offset (batch :: batches) terminal

structure TraceWire (limits : Batch.Limits) (input : KBytes) (trace : Trace) : Prop where
  source : input.wf = true
  schema :
    ∃ size, trace.schemaEnd = 8 + size ∧
      EnvelopeWire limits.schema.ipc input.toList 0 (.metadata size) ∧
      (input.slice 8 size).toList = (input.toList.drop 8).take size ∧
      SchemaWire limits.schema (input.slice 8 size) trace.schema
  chain : CursorChain limits trace.schema input limits.schema.ipc.batches 0 trace.schemaEnd
    trace.batches trace.terminal

end

end Silmaril.Formats.Arrow.RecursiveSchema.Stream
