module

import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
import Silmaril.Prelude.Bytes.Write.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Prelude.Bytes.Write.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure

private structure Batch where
  range : Stream.BatchRange
  observed : StreamWriter.BatchObservation
  deriving DecidableEq

private def observe (record : Stream.Batch) : Batch :=
  ⟨record.range, StreamWriter.observeBatch record⟩

private inductive Outcome where
  | success (last : Nat)
  | failed (cause : Incremental.Error)
  deriving DecidableEq

private structure Trace where
  fields : Option (List MixedFlat.Field) := none
  batches : List Batch := []
  outcome : Option Outcome := none

private def pump : Nat → Cursor → KBytes → Trace → Cursor × Trace
  | 0, cursor, _, trace => (cursor, trace)
  | fuel + 1, cursor, chunk, trace =>
    match feed cursor chunk with
    | .error cause => (cursor, { trace with outcome := some (.failed cause) })
    | .ok (.wait next) => (next, trace)
    | .ok (.advance next rest) => pump fuel next rest trace
    | .ok (.schema fields _ next rest) => pump fuel next rest { trace with fields := some fields }
    | .ok (.batch _ record next rest) =>
      pump fuel next rest { trace with batches := observe record.record :: trace.batches }

private def collect : Cursor → Trace → List KBytes → Trace
  | cursor, trace, chunks =>
    if trace.outcome.isSome then trace
    else
      match chunks with
      | [] =>
        let outcome := match finish cursor with
          | .ok atEnd => Outcome.success atEnd
          | .error cause => .failed cause
        { trace with outcome := some outcome }
      | chunk :: rest =>
        let (next, trace) := pump (3 * chunk.len + 8) cursor chunk trace
        collect next trace rest

private def singleBytes (wire : KBytes) : List KBytes :=
  (List.range wire.len).map fun i => wire.slice i 1

private def uneven (wire : KBytes) (cuts : List Nat) : List KBytes :=
  let (front, last) := cuts.foldl (fun (pieces, start) stop =>
    (wire.slice start (stop - start) :: pieces, stop)) ([], 0)
  front.reverse ++ [wire.slice last (wire.len - last)]

private def agrees (limits : Incremental.Limits) (expected : Stream.Observed)
    (batches : Nat) (cause : Incremental.Error) (chunks : List KBytes) : Bool :=
  let trace := collect (start limits) {} chunks
  decide (trace.fields = some expected.fields ∧
    trace.batches.reverse = (expected.batches.take batches).map observe ∧
    trace.outcome = some (.failed cause))

-- Synthetic tail octets are appended after the producer's complete marker.
-- The one-byte schedule recognizes EOS before receiving the tail. The uneven
-- schedule sends the last marker bytes and the tail together.
private def rejectsTail (limits : Incremental.Limits) (valid : KBytes) : Bool := Id.run do
  let .ok expected := Stream.read limits.mixed valid | return false
  let ordinal := expected.batches.length
  let wire := valid ++ .leaf 2 0xcb01
  let .error (.batch observed .trailingBytes) := Stream.read limits.mixed wire | return false
  let .ok ⟨_, pull⟩ := Stream.Events.readAll limits.mixed wire | return false
  let .readError (.message pulled marker .trailingBytes) := pull.termination | return false
  let .ok .eos := readEnvelope limits.mixed.observation.ipc wire marker | return false
  let expectedCause := tailError ordinal valid.len
  return decide (observed = ordinal ∧ pulled = ordinal ∧ marker + 8 = valid.len) &&
    agrees limits expected ordinal expectedCause (singleBytes wire) &&
    agrees limits expected ordinal expectedCause
      (uneven wire [0, 3, 4, 17, valid.len - 10, valid.len - 6, valid.len - 3]) &&
    agrees limits expected ordinal expectedCause [valid, .empty, .leaf 2 0xcb01]

#guard rejectsTail { mixed := { observation := { totalRows := 6, totalCells := 24 } } } multi

#guard Id.run do
  let batches : List OrderedWriter.BatchInput := [
    ⟨2, [.int32 "i" false [some 3, some (-8)], .binary "b" true [some (.leaf 13 0x1234), none]]⟩,
    ⟨0, [.int32 "i" false [], .binary "b" true []]⟩,
    ⟨1, [.int32 "i" false [some 9], .binary "b" true [some (.leaf 1 255)]]⟩]
  let fields := (batches.headD ⟨0, []⟩).fields
  let limits : Incremental.Limits := {
    mixed := { observation := { ipc := { batches := 3 }, totalRows := 3, totalCells := 6 } }
    totalDataBuffers := 1 }
  let .ok wire := OrderedWriter.emit limits.mixed fields batches | return false
  return rejectsTail limits wire

-- Synthetic cutoff and edit controls retain their distinct original causes.
#guard Id.run do
  let .ok expected := Stream.read {} multi | return false
  let cutoff : Incremental.Error := .framing (some 2) ⟨.body, 1616, .malformed .truncated⟩
  let badPrefix := multi.write lastViewPrefix 4 0
  let semantic : Incremental.Error :=
    .batch 2 lastRecordOffset (.record (.decode (.field 3 (.view (.slot 0 .prefixMismatch)))))
  return agrees {} expected 2 cutoff (singleBytes lateTruncated) &&
    agrees {} expected 2 cutoff (uneven lateTruncated [3, 7, 1247, 1615, 1617]) &&
    agrees {} expected 2 semantic (singleBytes badPrefix) &&
    agrees {} expected 2 semantic (uneven badPrefix [3, 7, 1247, 1615, lastViewPrefix + 1])

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure
