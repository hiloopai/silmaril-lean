module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Defs

/-! Exact finalization failure at an admitted RecordBatch body cutoff. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff

open MixedFlat.Events

/-- The original ordinal accompanies the body request offset at finalization. -/
def cutoffError (ordinal bodyStart : Nat) : Incremental.Error :=
  .framing (some ordinal) ⟨.body, bodyStart, .malformed .truncated⟩

/-- The supplied carrier ends in a short body. The attempted batch must
have an available batch slot and admitted typed metadata declaring the
same length as the framing request. The covered prefix uses the actual
successful feed calls, including any waits inside the short body. -/
structure Run (limits : Incremental.Limits) (wire : KBytes) where
  fields : List MixedFlat.Field
  batches : List (Delivered fields)
  final : Cursor
  attempted : Stream.BatchRange
  ordinal : Nat
  ran : ∃ (opened : Cursor) (header : KBytes) (pending : Arrow.Framing.Incremental.Buffer attempted.bodyLength),
    SchemaSteps wire.len (wire.read 0 wire.len) fields (start limits) opened ∧
    RecordSteps wire.len (wire.read 0 wire.len) fields opened batches final ∧
    final.input = .body attempted.offset header attempted.bodyLength pending ∧
    header.len = attempted.metadataSize ∧ final.position = wire.len ∧
    pending.bytes.len < attempted.bodyLength ∧
    final.phase.ordinal = some ordinal ∧ ordinal < limits.mixed.observation.ipc.batches ∧
    ∃ metadata,
      MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
        limits.mixed.totalDataBuffers fields (attempted.metadataSlice (Portable.reference wire)) =
          .ok metadata ∧ metadata.bodyLength = attempted.bodyLength

def Run.ranges {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    List Stream.BatchRange :=
  run.batches.map (·.record.range)

def Run.cause {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Incremental.Error :=
  cutoffError run.ordinal run.attempted.bodyStart

def Run.trace {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Arrow.Events.EventStream MixedFlat.Field (fun _ : Unit => Cell) Incremental.Error :=
  .ok ⟨schema run.fields, ⟨run.batches.map Delivered.event, .readError run.cause⟩⟩

/-- The immutable reader reports the truncated body at the original message
offset. The incremental cause identifies the original body request offset. -/
def Agreement (limits : Incremental.Limits) (wire : KBytes) (run : Run limits wire) : Prop :=
  let input := Portable.reference wire
  ∃ startOffset stop,
    Stream.readSchemaFrame limits.mixed.observation.ipc input = .ok (run.fields, startOffset) ∧
    Replay limits.mixed input run.fields (.ofRunning limits.mixed {} startOffset)
      (run.batches.map Delivered.published) stop ∧
    stop.ordinal = run.ordinal ∧ stop.offset = run.attempted.offset ∧
    readEnvelope limits.mixed.observation.ipc input stop.offset = .ok (.metadata run.attempted.metadataSize) ∧
    readBody limits.mixed.observation.ipc input run.attempted.bodyStart run.attempted.bodyLength =
      .error (.malformed .truncated) ∧
    finish run.final = .error run.cause ∧
    stop.readNext limits.mixed input run.fields =
      .error (.message run.ordinal stop.offset (.body (.malformed .truncated))) ∧
    Stream.read limits.mixed input = .error (.batch run.ordinal (.body (.malformed .truncated)))

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff
