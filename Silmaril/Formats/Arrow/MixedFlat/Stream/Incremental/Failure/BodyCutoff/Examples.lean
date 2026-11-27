module

import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff

private structure PublishedBatch where
  range : Stream.BatchRange
  observed : StreamWriter.BatchObservation
  deriving DecidableEq

private def observe (batch : Stream.Batch) : PublishedBatch :=
  ⟨batch.range, StreamWriter.observeBatch batch⟩

private structure Prefix where
  fields : Option (List MixedFlat.Field) := none
  batches : List PublishedBatch := []

private def pump : Nat → Cursor → KBytes → Prefix → Except Incremental.Error (Cursor × Prefix)
  | 0, cursor, _, _ => .error (.expectedSchema cursor.position)
  | fuel + 1, cursor, chunk, result => do
    match ← feed cursor chunk with
    | .wait next => return (next, result)
    | .advance next rest => pump fuel next rest result
    | .schema fields _ next rest => pump fuel next rest { result with fields := some fields }
    | .batch _ value next rest =>
      pump fuel next rest { result with batches := observe value.record :: result.batches }

-- Returning the live cursor leaves finalization entirely to the caller.
private def supply (limits : Incremental.Limits) (chunks : List KBytes) :
    Except Incremental.Error (Cursor × Prefix) :=
  chunks.foldlM (fun (cursor, prefixRead) chunk => pump (3 * chunk.len + 8) cursor chunk prefixRead)
    (start limits, {})

private def singleBytes (wire : KBytes) : List KBytes :=
  (List.range wire.len).map fun i => wire.slice i 1

private def split (wire : KBytes) (cuts : List Nat) : List KBytes :=
  let (front, last) := cuts.foldl (fun (pieces, start) stop =>
    (wire.slice start (stop - start) :: pieces, stop)) ([], 0)
  front.reverse ++ [wire.slice last (wire.len - last)]

private def observes (expected : Stream.Observed) (next : Nat) (value : Prefix) : Bool :=
  decide (value.fields = some expected.fields ∧ value.batches.reverse = (expected.batches.take next).map observe)

private def finishesAs (limits : Incremental.Limits) (expected : Stream.Observed) (next : Nat)
    (cause : Incremental.Error) (chunks : List KBytes) (extent : Nat) : Bool := Id.run do
  let .ok (cursor, results) := supply limits chunks | return false
  let .error observed := finish cursor | return false
  return observes expected next results && decide (cursor.position = extent ∧ observed = cause)

private def cutoffAgrees (limits : Incremental.Limits) (good : KBytes) (ordinal : Nat) : Bool := Id.run do
  let .ok expected := Stream.read limits.mixed good | return false
  let some record := expected.batches[ordinal]? | return false
  let range := record.range
  let cutoff := good.slice 0 (range.next - 1)
  let uneven := split cutoff [0, 3, 7, range.offset - 1, range.offset + 5,
    range.bodyStart - 1, range.bodyStart + 1, range.next - 2]
  let .error eager := Stream.read limits.mixed cutoff | return false
  let .ok ⟨_, pulled⟩ := Stream.Events.readAll limits.mixed cutoff | return false
  let .readError pullError := pulled.termination | return false
  let error := cutoffError ordinal range.bodyStart
  return decide (eager = .batch ordinal (.body (.malformed .truncated)) ∧
    pullError = .message ordinal range.offset (.body (.malformed .truncated))) &&
    finishesAs limits expected ordinal error (singleBytes cutoff) cutoff.len &&
    finishesAs limits expected ordinal error uneven cutoff.len

-- PyArrow's original third body ends at 1744. The synthetic carrier ends one byte earlier.
#guard cutoffAgrees {} multi 2

-- End exactly at the last complete body, then finalize without an EOS.
#guard Id.run do
  let .ok expected := Stream.read {} multi | return false
  let noEos := multi.slice 0 multiEos
  return finishesAs {} expected 3 (.framing (some 3) ⟨.prefix, multiEos, .malformed .truncated⟩)
    (singleBytes noEos) noEos.len

-- The same internal cutoff can resume before finish and consume the real EOS.
#guard Id.run do
  let .ok expected := Stream.read {} multi | return false
  let cut := lateTruncated.len
  let .ok (cursor, results) := supply {} [lateTruncated] | return false
  let .body .. := cursor.input | return false
  let .ok (resumed, finished) := pump 32 cursor (multi.slice cut (multi.len - cut)) results | return false
  let .ok last := finish resumed | return false
  return observes expected 2 results && observes expected 3 finished && decide (last = multi.len)

-- Exhausting the batch budget is earlier in the immutable reader. The
-- incremental reader is still waiting for the body, so finish reports truncation.
#guard Id.run do
  let .ok expected := Stream.read {} multi | return false
  let limits : Incremental.Limits := { mixed := { observation := { ipc := { batches := 2 } } } }
  let .error (.batch 2 .batchLimit) := Stream.read limits.mixed lateTruncated | return false
  return finishesAs limits expected 2 (cutoffError 2 1616) (singleBytes lateTruncated) lateTruncated.len

-- A native stream with a larger final body tests both sides of its exact cap.
#guard Id.run do
  let batches : List OrderedWriter.BatchInput := [
    ⟨1, [.int32 "i" false [some 1], .binary "b" true [none]]⟩,
    ⟨0, [.int32 "i" false [], .binary "b" true []]⟩,
    ⟨2, [.int32 "i" false [some (-4), some 9], .binary "b" true [some (.leaf 64 0xf1), some .empty]]⟩]
  let fields := (batches.headD ⟨0, []⟩).fields
  let .ok wire := OrderedWriter.emit {} fields batches | return false
  let .ok expected := Stream.read {} wire | return false
  let some last := expected.batches[2]? | return false
  let cap := last.range.bodyLength
  let atCap : Incremental.Limits := { mixed := { observation := { ipc := { bodyBytes := cap } } } }
  let below : Incremental.Limits := { mixed := { observation := { ipc := { bodyBytes := cap - 1 } } } }
  let cutoff := wire.slice 0 (last.range.next - 1)
  let .error (.framing (some 2) ⟨.metadata, offset, .limit .bodyBytes⟩) :=
    supply below (singleBytes cutoff) | return false
  let .error (.batch 2 (.body (.limit .bodyBytes))) := Stream.read below.mixed cutoff | return false
  return cutoffAgrees atCap wire 2 && decide (offset = last.range.offset)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyCutoff
