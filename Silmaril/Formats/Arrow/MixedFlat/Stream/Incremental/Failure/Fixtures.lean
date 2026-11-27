module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Defs
public import Silmaril.Formats.Arrow.MixedFlat.StreamWriter.Defs

/-! Shared observations for synthetic incremental failure controls. -/

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Fixtures

private structure PublishedBatch where
  range : Stream.BatchRange
  observed : StreamWriter.BatchObservation
  deriving DecidableEq

private def observe (batch : Stream.Batch) : PublishedBatch :=
  ⟨batch.range, StreamWriter.observeBatch batch⟩

private inductive Terminal where
  | finished (offset : Nat)
  | failed (cause : Incremental.Error)
  deriving DecidableEq

private structure Trace where
  fields : Option (List MixedFlat.Field) := none
  batches : List PublishedBatch := []
  terminal : Option Terminal := none

private def pump : Nat → Cursor → KBytes → Trace → Cursor × Trace
  | 0, cursor, _, trace => (cursor, trace)
  | fuel + 1, cursor, chunk, trace =>
    match feed cursor chunk with
    | .error cause => (cursor, { trace with terminal := some (.failed cause) })
    | .ok (.wait next) => (next, trace)
    | .ok (.advance next rest) => pump fuel next rest trace
    | .ok (.schema fields _ next rest) => pump fuel next rest { trace with fields := some fields }
    | .ok (.batch _ value next rest) =>
      pump fuel next rest { trace with batches := observe value.record :: trace.batches }

private def drain : Cursor → Trace → List KBytes → Trace
  | cursor, trace, chunks =>
    if trace.terminal.isSome then trace
    else
      match chunks with
      | [] =>
        let terminal := match finish cursor with
          | .ok offset => Terminal.finished offset
          | .error cause => .failed cause
        { trace with terminal := some terminal }
      | chunk :: chunks =>
        let (next, trace) := pump (3 * chunk.len + 8) cursor chunk trace
        drain next trace chunks

def singleBytes (wire : KBytes) : List KBytes :=
  (List.range wire.len).map fun i => wire.slice i 1

def uneven (wire : KBytes) (range : Stream.BatchRange) : List KBytes :=
  let cuts := [0, 3, 7, range.offset - 1, range.offset + 5,
    range.bodyStart - 1, range.bodyStart, range.bodyStart + 1, range.next - 1]
  let (front, last) := cuts.foldl (fun (pieces, start) stop =>
    (wire.slice start (stop - start) :: pieces, stop)) ([], 0)
  front.reverse ++ [wire.slice last (wire.len - last)]

def stopsAs (limits : Incremental.Limits) (expected : Stream.Observed)
    (ordinal : Nat) (error : Incremental.Error) (chunks : List KBytes) : Bool :=
  let trace := drain (start limits) {} chunks
  decide (trace.fields = some expected.fields ∧
    trace.batches.reverse = (expected.batches.take ordinal).map observe ∧
    trace.terminal = some (.failed error))

def rejectsRecord (limits : Incremental.Limits) (good damaged : KBytes)
    (ordinal : Nat) (fault : Stream.BatchError) : Bool := Id.run do
  let .ok expected := Stream.read limits.mixed good | return false
  let some batch := expected.batches[ordinal]? | return false
  let range := batch.range
  let .ok (.metadata size) := readEnvelope limits.mixed.observation.ipc damaged range.offset | return false
  let .ok planned := Arrow.Framing.Incremental.plan limits.mixed.observation.ipc
    (range.metadataSlice damaged) | return false
  let .ok _ := readBody limits.mixed.observation.ipc damaged range.bodyStart range.bodyLength | return false
  let .error eager := Stream.read limits.mixed damaged | return false
  let .ok ⟨_, pulled⟩ := Stream.Events.readAll limits.mixed damaged | return false
  let .readError pullError := pulled.termination | return false
  let error := Incremental.Error.batch ordinal range.offset (.record fault)
  return decide (size = range.metadataSize ∧ planned = range.bodyLength ∧ eager = .batch ordinal fault ∧
    pullError = .message ordinal range.offset fault ∧
    pulled.batches.map (·.rowCount) = (expected.batches.take ordinal).map (·.observed.rowCount)) &&
    stopsAs limits expected ordinal error (singleBytes damaged) &&
    stopsAs limits expected ordinal error (uneven damaged range)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Fixtures
