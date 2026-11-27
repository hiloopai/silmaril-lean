module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Defs

/-! Exact field errors from checked complete RecordBatch frames. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

/-- An actual semantic field failure after the framing, metadata and running
checks. The complete frame still refers to the original carrier. -/
def FieldFailureWire (limits : Incremental.Limits) (input : KBytes) (fields : List MixedFlat.Field)
    (running : Running) (range : Stream.BatchRange) (index : Nat) (cause : MixedFlat.ColumnError) : Prop :=
  readEnvelope limits.mixed.observation.ipc input range.offset = .ok (.metadata range.metadataSize) ∧
  running.ordinal < limits.mixed.observation.ipc.batches ∧
  ∃ metadata body,
    MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
      limits.mixed.totalDataBuffers fields (range.metadataSlice input) = .ok metadata ∧
    metadata.bodyLength = range.bodyLength ∧
    readBody limits.mixed.observation.ipc input range.bodyStart range.bodyLength = .ok body ∧
    running.dataBuffers + metadata.counts.sum ≤ limits.totalDataBuffers ∧
    Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount) = .ok () ∧
    MixedFlat.readParsed limits.mixed fields metadata body = .error (.field index cause)

namespace Field

open MixedFlat.Events

def fieldError (ordinal offset field : Nat) (fault : MixedFlat.ColumnError) : Incremental.Error :=
  .batch ordinal offset (.record (.decode (.field field fault)))

/-- Admitted fragments through a checked Schema and the successfully
published prefix. The final feed reports the first semantic failure. -/
structure Run (limits : Incremental.Limits) (wire : KBytes) where
  fields : List MixedFlat.Field
  batches : List (Delivered fields)
  ordinal : Nat
  offset : Nat
  field : Nat
  fault : MixedFlat.ColumnError
  ran : ∃ opened final chunk,
    SchemaSteps wire.len (wire.read 0 wire.len) fields (start limits) opened ∧
    RecordSteps wire.len (wire.read 0 wire.len) fields opened batches final ∧
    Arrow.Framing.Incremental.Window (Portable.reference wire) final.position chunk ∧
    feed final chunk = .error (fieldError ordinal offset field fault)

def Run.ranges {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    List Stream.BatchRange :=
  run.batches.map (·.record.range)

def Run.cause {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Incremental.Error :=
  fieldError run.ordinal run.offset run.field run.fault

def Run.nativeCause {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Stream.Events.Error :=
  .message run.ordinal run.offset (.decode (.field run.field run.fault))

def Run.trace {limits : Incremental.Limits} {wire : KBytes} (run : Run limits wire) :
    Arrow.Events.EventStream MixedFlat.Field (fun _ : Unit => Cell) Incremental.Error :=
  .ok ⟨schema run.fields, ⟨run.batches.map Delivered.event, .readError run.cause⟩⟩

/-- The complete prefix replays on the immutable reader and stops at the
same column cause in the same complete, rejected frame. -/
def Agreement (limits : Incremental.Limits) (wire : KBytes) (run : Run limits wire) : Prop :=
  let input := Portable.reference wire
  let fault := Stream.BatchError.decode (.field run.field run.fault)
  ∃ startOffset running range,
    Stream.readSchemaFrame limits.mixed.observation.ipc input = .ok (run.fields, startOffset) ∧
    Replay limits.mixed input run.fields (.ofRunning limits.mixed {} startOffset)
      (run.batches.map Delivered.published) (.ofRunning limits.mixed running run.offset) ∧
    running.ordinal = run.ordinal ∧ range.offset = run.offset ∧
    FieldFailureWire limits input run.fields running range run.field run.fault ∧
    (Position.ofRunning limits.mixed running run.offset).readNext limits.mixed input run.fields =
      .error (.message run.ordinal run.offset fault) ∧
    Stream.read limits.mixed input = .error (.batch run.ordinal fault)

end Field

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure
