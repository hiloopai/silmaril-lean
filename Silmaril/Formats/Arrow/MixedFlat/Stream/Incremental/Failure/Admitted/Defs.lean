module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.RecordMetadata.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Field.Defs

/-! Admitted rejections of complete mixed-flat RecordBatch frames. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

namespace Admitted

open MixedFlat.Events

/-- The shared rejection stages on a completely framed RecordBatch. -/
inductive Cause where
  | metadata (cause : MixedFlat.MetadataError)
  | layout (cause : BodyLayout.Cause)
  | column (index : Nat) (cause : MixedFlat.ColumnError)
  deriving DecidableEq, Repr

def Cause.batchError : Cause → Stream.BatchError
  | .metadata cause => .metadata cause
  | .layout cause => .decode cause.decodeError
  | .column index cause => .decode (.field index cause)

def feedError (ordinal offset : Nat) (cause : Cause) : Incremental.Error :=
  .batch ordinal offset (.record cause.batchError)

/-- Each case keeps its original admission witness. Metadata failures need
a complete frame and batch slot. Later cases also require accepted metadata
and running limits. -/
def Wire (limits : Incremental.Limits) (input : KBytes) (fields : List MixedFlat.Field)
    (running : Running) (range : Stream.BatchRange) : Cause → Prop
  | .metadata cause => RecordMetadata.Wire limits.mixed input fields running range cause
  | .layout cause => BodyLayout.Wire limits input fields running range cause
  | .column index cause => FieldFailureWire limits input fields running range index cause

/-- Admitted fragments through a checked Schema and the successfully
published prefix. The final feed reports the exact shared rejection. -/
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
  .message run.ordinal run.offset run.fault.batchError

def Run.trace {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Arrow.Events.EventStream MixedFlat.Field (fun _ : Unit => Cell) Incremental.Error :=
  .ok ⟨schema run.fields, ⟨run.batches.map Delivered.event, .readError run.cause⟩⟩

/-- The complete prefix replays on the immutable reader and stops at the
same typed cause in the same complete, rejected frame. -/
def Agreement (limits : Incremental.Limits) (wire : KBytes) (run : Run limits wire) : Prop :=
  let input := Portable.reference wire
  let fault := run.fault.batchError
  ∃ startOffset running range,
    Stream.readSchemaFrame limits.mixed.observation.ipc input = .ok (run.fields, startOffset) ∧
    Replay limits.mixed input run.fields (.ofRunning limits.mixed {} startOffset)
      (run.batches.map Delivered.published) (.ofRunning limits.mixed running run.offset) ∧
    running.ordinal = run.ordinal ∧ range.offset = run.offset ∧
    Wire limits input run.fields running range run.fault ∧
    (Position.ofRunning limits.mixed running run.offset).readNext limits.mixed input run.fields =
      .error (.message run.ordinal run.offset fault) ∧
    Stream.read limits.mixed input = .error (.batch run.ordinal fault)

end Admitted

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure
