module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Defs

/-! Field-node count rejection after complete RecordBatch framing. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

namespace NodeCount

open MixedFlat.Events

def batchError (expected actual : Nat) : Stream.BatchError :=
  .metadata (.nodeCount expected actual)

def feedError (ordinal offset expected actual : Nat) : Incremental.Error :=
  .batch ordinal offset (.record (batchError expected actual))

/-- The original complete frame passed common framing and the batch slot check.
Its schema-aware metadata parser rejected the declared node vector length. -/
structure Wire (limits : MixedFlat.Limits) (input : KBytes) (fields : List MixedFlat.Field)
    (running : Running) (range : Stream.BatchRange) (expected actual : Nat) : Prop where
  envelope : readEnvelope limits.observation.ipc input range.offset = .ok (.metadata range.metadataSize)
  planned : Arrow.Framing.Incremental.plan limits.observation.ipc (range.metadataSlice input) = .ok range.bodyLength
  body : ∃ bytes, readBody limits.observation.ipc input range.bodyStart range.bodyLength = .ok bytes
  available : running.ordinal < limits.observation.ipc.batches
  rejected : readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers
    fields (range.metadataSlice input) = .error (.nodeCount expected actual)

/-- Admitted fragments through a checked Schema and the successfully
published prefix. The final feed reports the typed metadata rejection. -/
structure Run (limits : Incremental.Limits) (wire : KBytes) where
  fields : List MixedFlat.Field
  batches : List (Delivered fields)
  ordinal : Nat
  offset : Nat
  expected : Nat
  actual : Nat
  ran : ∃ opened final chunk,
    SchemaSteps wire.len (wire.read 0 wire.len) fields (start limits) opened ∧
    RecordSteps wire.len (wire.read 0 wire.len) fields opened batches final ∧
    Arrow.Framing.Incremental.Window (Portable.reference wire) final.position chunk ∧
    feed final chunk = .error (feedError ordinal offset expected actual)

def Run.ranges {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    List Stream.BatchRange :=
  run.batches.map (·.record.range)

def Run.cause {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Incremental.Error :=
  feedError run.ordinal run.offset run.expected run.actual

def Run.nativeCause {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Stream.Events.Error :=
  .message run.ordinal run.offset (batchError run.expected run.actual)

def Run.trace {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Arrow.Events.EventStream MixedFlat.Field (fun _ : Unit => Cell) Incremental.Error :=
  .ok ⟨schema run.fields, ⟨run.batches.map Delivered.event, .readError run.cause⟩⟩

/-- The complete prefix replays on the immutable reader and stops at the
same node count cause in the same complete, rejected frame. -/
def Agreement (limits : Incremental.Limits) (wire : KBytes) (run : Run limits wire) : Prop :=
  let input := Portable.reference wire
  let fault := batchError run.expected run.actual
  ∃ startOffset running range,
    Stream.readSchemaFrame limits.mixed.observation.ipc input = .ok (run.fields, startOffset) ∧
    Replay limits.mixed input run.fields (.ofRunning limits.mixed {} startOffset)
      (run.batches.map Delivered.published) (.ofRunning limits.mixed running run.offset) ∧
    running.ordinal = run.ordinal ∧ range.offset = run.offset ∧
    Wire limits.mixed input run.fields running range run.expected run.actual ∧
    (Position.ofRunning limits.mixed running run.offset).readNext limits.mixed input run.fields =
      .error (.message run.ordinal run.offset fault) ∧
    Stream.read limits.mixed input = .error (.batch run.ordinal fault)

end NodeCount

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure
