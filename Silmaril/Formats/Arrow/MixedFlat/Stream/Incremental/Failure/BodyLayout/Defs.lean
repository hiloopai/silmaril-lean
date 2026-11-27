module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Defs

/-! Post-metadata layout rejections from checked complete RecordBatch frames. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

namespace BodyLayout

open MixedFlat.Events

/-- Shared post-metadata layout failures on an admitted complete body. -/
inductive Cause where
  | assignment (cause : MixedFlat.PlanError)
  | descriptors
  deriving DecidableEq, Repr

def Cause.decodeError : Cause → MixedFlat.Error
  | .assignment cause => .plan cause
  | .descriptors => .body (.malformed .batchLayout)

def feedError (ordinal offset : Nat) (cause : Cause) : Incremental.Error :=
  .batch ordinal offset (.record (.decode cause.decodeError))

/-- A complete frame and the exact original body supplied to both readers.
The incremental aggregate allowance and shared row/cell budgets passed
before the decoder reported the layout cause. -/
structure Wire (limits : Incremental.Limits) (input : KBytes) (fields : List MixedFlat.Field)
    (running : Running) (range : Stream.BatchRange) (cause : Cause) : Prop where
  envelope : readEnvelope limits.mixed.observation.ipc input range.offset = .ok (.metadata range.metadataSize)
  planned : Arrow.Framing.Incremental.plan limits.mixed.observation.ipc
    (range.metadataSlice input) = .ok range.bodyLength
  available : running.ordinal < limits.mixed.observation.ipc.batches
  rejected : ∃ metadata body,
    readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers limits.mixed.totalDataBuffers
      fields (range.metadataSlice input) = .ok metadata ∧
    metadata.bodyLength = range.bodyLength ∧
    readBody limits.mixed.observation.ipc input range.bodyStart range.bodyLength = .ok body ∧
    running.dataBuffers + metadata.counts.sum ≤ limits.totalDataBuffers ∧
    Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount) = .ok () ∧
    bindBatch limits.mixed fields metadata body = .error cause.decodeError

/-- Admitted fragments through a checked Schema and the successfully
published prefix. The final feed reports the shared layout rejection. -/
structure Run (limits : Incremental.Limits) (wire : KBytes) where
  fields : List MixedFlat.Field
  batches : List (Delivered fields)
  ordinal : Nat
  offset : Nat
  fault : Cause
  ran : ∃ opened final chunk,
    SchemaSteps wire.len (wire.read 0 wire.len) fields (start limits) opened ∧
    RecordSteps wire.len (wire.read 0 wire.len) fields opened batches final ∧
    Arrow.Framing.Incremental.Window (Portable.reference wire) final.position chunk ∧
    feed final chunk = .error (feedError ordinal offset fault)

def Run.ranges {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    List Stream.BatchRange :=
  run.batches.map (·.record.range)

def Run.cause {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Incremental.Error :=
  feedError run.ordinal run.offset run.fault

def Run.nativeCause {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Stream.Events.Error :=
  .message run.ordinal run.offset (.decode run.fault.decodeError)

def Run.trace {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Arrow.Events.EventStream MixedFlat.Field (fun _ : Unit => Cell) Incremental.Error :=
  .ok ⟨schema run.fields, ⟨run.batches.map Delivered.event, .readError run.cause⟩⟩

/-- The complete prefix replays on the immutable reader and stops at the
same layout cause in the same complete, rejected frame. -/
def Agreement (limits : Incremental.Limits) (wire : KBytes) (run : Run limits wire) : Prop :=
  let input := Portable.reference wire
  let fault := Stream.BatchError.decode run.fault.decodeError
  ∃ startOffset running range,
    Stream.readSchemaFrame limits.mixed.observation.ipc input = .ok (run.fields, startOffset) ∧
    Replay limits.mixed input run.fields (.ofRunning limits.mixed {} startOffset)
      (run.batches.map Delivered.published) (.ofRunning limits.mixed running run.offset) ∧
    running.ordinal = run.ordinal ∧ range.offset = run.offset ∧
    Wire limits input run.fields running range run.fault ∧
    (Position.ofRunning limits.mixed running run.offset).readNext limits.mixed input run.fields =
      .error (.message run.ordinal run.offset fault) ∧
    Stream.read limits.mixed input = .error (.batch run.ordinal fault)

end BodyLayout

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure
