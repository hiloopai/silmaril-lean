module

public import Silmaril.Formats.Arrow.Binary.Defs

/-! Exact ordered V5 IPC streams with one plain Binary field. The framing
profile applies to every message and to EOS. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.Binary.Stream

inductive Framing where
  | modern
  | legacy
  deriving DecidableEq, Repr

def Framing.prefixSize : Framing → Nat
  | .modern => 8
  | .legacy => 4

/-- Legacy V5 frames use a single signed i32 length word. Zero is EOS.
A nonempty metadata span includes the padding that aligns the body. -/
def readLegacyEnvelope (limits : Limits) (input : KBytes) (offset : Nat) :
    Except Arrow.Error Envelope :=
  if offset % 8 ≠ 0 then .error (.malformed .alignment)
  else
    match input.readLE offset 4 with
    | none => .error (.malformed .truncated)
    | some size =>
      if size = 0 then .ok .eos
      else if size ≥ 2^31 ∨ (4 + size) % 8 ≠ 0 then .error (.malformed .metadataLength)
      else if size > limits.metadataBytes then .error (.limit .metadataBytes)
      else if offset + 4 + size > input.len then .error (.malformed .truncated)
      else .ok (.metadata size)

def Framing.readEnvelope : Framing → Limits → KBytes → Nat → Except Arrow.Error Envelope
  | .modern => Arrow.readEnvelope
  | .legacy => readLegacyEnvelope

structure Range where
  offset : Nat
  prefixSize : Nat
  metadataSize : Nat
  bodyLength : Nat
  deriving DecidableEq, Repr

def Range.metadataStart (range : Range) : Nat := range.offset + range.prefixSize

def Range.bodyStart (range : Range) : Nat := range.metadataStart + range.metadataSize

def Range.next (range : Range) : Nat := range.bodyStart + range.bodyLength

structure Batch where
  range : Range
  values : Binary.Column

inductive SchemaFailure where
  | source
  | envelope (cause : Arrow.Error)
  | expectedSchema
  | metadata (cause : Binary.SchemaError)
  deriving DecidableEq, Repr

inductive Cause where
  | envelope (cause : Arrow.Error)
  | batchLimit
  | expectedRecordBatch
  | metadata (cause : Arrow.Error)
  | body (cause : Arrow.Error)
  | decode (cause : Binary.Error)
  | trailingBytes
  deriving DecidableEq, Repr

/-- Offset of the failing prefix in the original carrier, and zero-based
record ordinal. An error while expecting EOS uses the next record ordinal. -/
structure Failure where
  ordinal : Nat
  offset : Nat
  cause : Cause
  deriving DecidableEq, Repr

inductive Error where
  | schema (cause : SchemaFailure)
  | record (failure : Failure)
  deriving DecidableEq, Repr

structure Cursor where
  limits : Limits
  framing : Framing
  input : KBytes
  field : Binary.Field
  remaining : Nat
  ordinal : Nat
  offset : Nat

/-- Validate only the first envelope and schema. The cursor retains the
original immutable carrier for subsequent pulls. -/
def openInput (limits : Limits) (framing : Framing) (input : KBytes) :
    Except SchemaFailure Cursor :=
  if !input.wf then .error .source
  else do
    let envelope ← (framing.readEnvelope limits input 0).mapError .envelope
    let .metadata size := envelope | throw .expectedSchema
    let field ← (Binary.readSchema limits (input.slice framing.prefixSize size)).mapError .metadata
    return ⟨limits, framing, input, field, limits.batches, 0, framing.prefixSize + size⟩

def Cursor.advance (cursor : Cursor) (batch : Batch) : Cursor :=
  { cursor with
    remaining := cursor.remaining - 1
    ordinal := cursor.ordinal + 1
    offset := batch.range.next }

/-- Decode a record after its envelope has been admitted. All slices refer
to the retained carrier. The checked Binary batch reader owns column layout
and value admission. -/
def Cursor.readRecord (cursor : Cursor) (size : Nat) : Except Cause Batch := do
  let start := cursor.offset + cursor.framing.prefixSize
  let message ← (Arrow.readMessage cursor.limits (cursor.input.slice start size)).mapError .metadata
  let .recordBatch metadata := message.header | throw .expectedRecordBatch
  let range : Range := ⟨cursor.offset, cursor.framing.prefixSize, size, message.bodyLength⟩
  let body ← (Arrow.readBody cursor.limits cursor.input range.bodyStart range.bodyLength).mapError .body
  let (node, buffers) ← (Binary.bindBody cursor.limits metadata body).mapError .decode
  let values ← (Binary.readColumn cursor.limits cursor.field.nullable node buffers).mapError .decode
  return ⟨range, values⟩

/-- A batch reply certifies that the cursor can spend one unit of batch
budget. The budget does not prevent reading the terminal marker. -/
def Cursor.readNext (cursor : Cursor) :
    Except Cause (Option { _batch : Batch // 0 < cursor.remaining }) := do
  let envelope ← (cursor.framing.readEnvelope cursor.limits cursor.input cursor.offset).mapError .envelope
  match envelope with
  | .eos =>
    if cursor.offset + cursor.framing.prefixSize = cursor.input.len then .ok none
    else .error .trailingBytes
  | .metadata size =>
    if hits : 0 < cursor.remaining then
      return some ⟨← cursor.readRecord size, hits⟩
    else .error .batchLimit

def Cursor.failure (cursor : Cursor) (cause : Cause) : Failure :=
  ⟨cursor.ordinal, cursor.offset, cause⟩

/-- Yield one batch and its successor. EOS and failure return no cursor. -/
def Cursor.next (cursor : Cursor) : Except Failure (Option (Batch × Cursor)) :=
  (cursor.readNext.mapError cursor.failure).map
    (Option.map fun batch => (batch.val, cursor.advance batch.val))

inductive End where
  | eos (offset : Nat)
  | failed (failure : Failure)
  deriving DecidableEq, Repr

structure Trace where
  batches : List Batch
  terminal : End

/-- Drain the same steps as `next`, retaining all successful batches before
the terminal reply. A zero-row batch still occupies one step. -/
def Cursor.drain (cursor : Cursor) : Trace :=
  match cursor.readNext with
  | .error cause => ⟨[], .failed (cursor.failure cause)⟩
  | .ok none => ⟨[], .eos cursor.offset⟩
  | .ok (some batch) =>
    let rest := (cursor.advance batch.val).drain
    ⟨batch.val :: rest.batches, rest.terminal⟩
termination_by cursor.remaining
decreasing_by exact Nat.pred_lt (Nat.ne_of_gt batch.property)

def readAll (limits : Limits) (framing : Framing) (input : KBytes) :
    Except SchemaFailure (Binary.Field × Trace) :=
  (openInput limits framing input).map fun cursor => (cursor.field, cursor.drain)

structure Observed where
  field : Binary.Field
  batches : List Batch
  eosOffset : Nat

/-- Return an observation only after the final marker exhausts the carrier. -/
def read (limits : Limits) (framing : Framing) (input : KBytes) : Except Error Observed := do
  let (field, trace) ← (readAll limits framing input).mapError .schema
  match trace.terminal with
  | .eos offset => return ⟨field, trace.batches, offset⟩
  | .failed failure => .error (.record failure)

def SchemaWire (limits : Limits) (framing : Framing) (input : KBytes) (cursor : Cursor) : Prop :=
  input.wf = true ∧ ∃ size field,
    framing.readEnvelope limits input 0 = .ok (.metadata size) ∧
    Binary.readSchema limits (input.slice framing.prefixSize size) = .ok field ∧
    cursor = ⟨limits, framing, input, field, limits.batches, 0, framing.prefixSize + size⟩

/-- A completed record's metadata and body are the slices of its original
frame. The field was fixed by the one initial Schema message. -/
def RecordWire (cursor : Cursor) (size : Nat) (batch : Batch) : Prop :=
  ∃ metadata node buffers body,
    Arrow.readMessage cursor.limits
      (cursor.input.slice (cursor.offset + cursor.framing.prefixSize) size) =
      .ok ⟨.recordBatch metadata, batch.range.bodyLength⟩ ∧
    batch.range = ⟨cursor.offset, cursor.framing.prefixSize, size, batch.range.bodyLength⟩ ∧
    Arrow.readBody cursor.limits cursor.input batch.range.bodyStart batch.range.bodyLength = .ok body ∧
    Binary.BodyWire metadata body node buffers ∧
    Binary.checkColumn cursor.limits cursor.field.nullable node buffers = .ok () ∧
    Binary.ColumnWire node buffers batch.values

/-- Consecutive successful replies in their original source order. -/
inductive Prefix : Cursor → List Batch → Cursor → Prop where
  | stop (cursor) : Prefix cursor [] cursor
  | more {cursor batch rest final size} :
      cursor.framing.readEnvelope cursor.limits cursor.input cursor.offset = .ok (.metadata size) →
      0 < cursor.remaining →
      RecordWire cursor size batch →
      cursor.next = .ok (some (batch, cursor.advance batch)) →
      Prefix (cursor.advance batch) rest final →
      Prefix cursor (batch :: rest) final

def EndWire (cursor : Cursor) : End → Prop
  | .eos offset =>
    offset = cursor.offset ∧
      cursor.framing.readEnvelope cursor.limits cursor.input offset = .ok .eos ∧
      offset + cursor.framing.prefixSize = cursor.input.len ∧ cursor.next = .ok none
  | .failed failure =>
    failure.ordinal = cursor.ordinal ∧ failure.offset = cursor.offset ∧
      cursor.next = .error failure

def TraceWire (cursor : Cursor) (trace : Trace) : Prop :=
  ∃ final, Prefix cursor trace.batches final ∧ EndWire final trace.terminal

def StreamWire (limits : Limits) (framing : Framing) (input : KBytes) (observed : Observed) : Prop :=
  ∃ cursor final, SchemaWire limits framing input cursor ∧ cursor.field = observed.field ∧
    Prefix cursor observed.batches final ∧ EndWire final (.eos observed.eosOffset)

end Silmaril.Formats.Arrow.Binary.Stream
