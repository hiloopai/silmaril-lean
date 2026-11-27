module

import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
import Silmaril.Prelude.Bytes.Write.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Prelude.Bytes.Write.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch

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

private def singleBytes (wire : KBytes) : List KBytes :=
  (List.range wire.len).map fun i => wire.slice i 1

private def uneven (wire : KBytes) (range : Stream.BatchRange) : List KBytes :=
  let cuts := [0, 3, 7, range.offset - 1, range.offset + 5,
    range.bodyStart - 1, range.bodyStart, range.bodyStart + 1, range.next - 1]
  let (front, last) := cuts.foldl (fun (pieces, start) stop =>
    (wire.slice start (stop - start) :: pieces, stop)) ([], 0)
  front.reverse ++ [wire.slice last (wire.len - last)]

private def stopsAs (limits : Incremental.Limits) (expected : Stream.Observed)
    (ordinal : Nat) (error : Incremental.Error) (chunks : List KBytes) : Bool :=
  let trace := drain (start limits) {} chunks
  decide (trace.fields = some expected.fields ∧
    trace.batches.reverse = (expected.batches.take ordinal).map observe ∧
    trace.terminal = some (.failed error))

private def rejectsField (limits : Incremental.Limits) (good damaged : KBytes)
    (ordinal field : Nat) (cause : MixedFlat.ColumnError) : Bool := Id.run do
  let .ok expected := Stream.read limits.mixed good | return false
  let some batch := expected.batches[ordinal]? | return false
  let range := batch.range
  let .ok (.metadata size) := readEnvelope limits.mixed.observation.ipc damaged range.offset | return false
  let .ok _ := readBody limits.mixed.observation.ipc damaged range.bodyStart range.bodyLength | return false
  let .error eager := Stream.read limits.mixed damaged | return false
  let .ok ⟨_, pulled⟩ := Stream.Events.readAll limits.mixed damaged | return false
  let .readError pullError := pulled.termination | return false
  let fault := Stream.BatchError.decode (.field field cause)
  let error := Field.fieldError ordinal range.offset field cause
  return decide (size = range.metadataSize ∧ eager = .batch ordinal fault ∧
    pullError = .message ordinal range.offset fault ∧
    pulled.batches.map (·.rowCount) = (expected.batches.take ordinal).map (·.observed.rowCount)) &&
    stopsAs limits expected ordinal error (singleBytes damaged) &&
    stopsAs limits expected ordinal error (uneven damaged range)

private def exactLimits : Incremental.Limits :=
  { mixed := { observation := { ipc := { batches := 3 }, totalRows := 6, totalCells := 24 } }
    totalDataBuffers := 5 }

-- Synthetic edit to the external prefix in the pinned PyArrow third record.
private def damagedPyArrow : KBytes := multi.write lastViewPrefix 4 0

#guard rejectsField exactLimits multi damagedPyArrow 2 3 (columnCause 0)

-- The native writer controls the layout. Locate and edit its external
-- prefix through the admitted fourth descriptor in the original frame.
#guard Id.run do
  let batches : List OrderedWriter.BatchInput := [
    ⟨1, [.int32 "i" false [some 3], .binary "b" true [some (.leaf 1 255)]]⟩,
    ⟨0, [.int32 "i" false [], .binary "b" true []]⟩,
    ⟨2, [.int32 "i" false [some (-8), some 9],
      .binary "b" true [some .empty, some (.leaf 13 0x1234)]]⟩]
  let fields := (batches.headD ⟨0, []⟩).fields
  let limits : Incremental.Limits := {
    mixed := { observation := { ipc := { batches := 3 }, totalRows := 3, totalCells := 6 } }
    totalDataBuffers := 1 }
  let .ok wire := OrderedWriter.emit limits.mixed fields batches | return false
  let .ok expected := Stream.read limits.mixed wire | return false
  let some last := expected.batches[2]? | return false
  let .ok metadata := MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
    limits.mixed.totalDataBuffers fields (last.range.metadataSlice wire) | return false
  let some views := metadata.batch.buffers[3]? | return false
  let absolute := last.range.bodyStart + views.offset + 16 + 4
  return decide (wire.read absolute 4 = 0x1234) &&
    rejectsField limits wire (wire.write absolute 4 0) 2 1 (columnCause 1)

-- Synthetic edit to an inline BinaryView slot in the pinned PyArrow stream.
-- Keep the slot's length and value intact and set its first padding octet.
#guard Id.run do
  let .ok expected := Stream.read exactLimits.mixed multi | return false
  let some last := expected.batches[2]? | return false
  let .ok metadata := MixedFlat.readMetadata exactLimits.mixed.observation.ipc
    exactLimits.mixed.view.dataBuffers exactLimits.mixed.totalDataBuffers expected.fields
    (last.range.metadataSlice multi) | return false
  let some views := metadata.batch.buffers[3]? | return false
  let slot := last.range.bodyStart + views.offset + 16
  return decide (multi.read slot 5 = 0xff00000001 ∧ multi.read (slot + 5) 1 = 0) &&
    rejectsField exactLimits multi (multi.write (slot + 5) 1 1) 2 1 (.view (.slot 1 .invalidPadding))

-- Synthetic edit to the native Int32 validity bitmap. The final field node
-- still declares one null. The complete preceding batches have 1 and 0 rows.
#guard Id.run do
  let batches : List OrderedWriter.BatchInput := [
    ⟨1, [.int32 "i" true [some 3]]⟩,
    ⟨0, [.int32 "i" true []]⟩,
    ⟨2, [.int32 "i" true [some (-8), none]]⟩]
  let fields := (batches.headD ⟨0, []⟩).fields
  let limits : Incremental.Limits :=
    { mixed := { observation := { ipc := { batches := 3 }, totalRows := 3, totalCells := 3 } }
      totalDataBuffers := 0 }
  let .ok wire := OrderedWriter.emit limits.mixed fields batches | return false
  let .ok expected := Stream.read limits.mixed wire | return false
  let some last := expected.batches[2]? | return false
  let .ok metadata := MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
    limits.mixed.totalDataBuffers fields (last.range.metadataSlice wire) | return false
  let some bitmap := metadata.batch.buffers[0]? | return false
  let absolute := last.range.bodyStart + bitmap.offset
  return decide (bitmap.length > 0 ∧ wire.read absolute 1 = 1) &&
    rejectsField limits wire (wire.write absolute 1 3) 2 0 (.primitive (.malformed .validityBitmap))

private def budgetControl (limits : Incremental.Limits) (error : Incremental.BatchError)
    (native : Stream.BatchError) : Bool := Id.run do
  let .ok expected := Stream.read {} multi | return false
  let some batch := expected.batches[2]? | return false
  let .error observed := Stream.read limits.mixed damagedPyArrow | return false
  let error := Incremental.Error.batch 2 batch.range.offset error
  return decide (observed = .batch 2 native) &&
    stopsAs limits expected 2 error (singleBytes damagedPyArrow) &&
    stopsAs limits expected 2 error (uneven damagedPyArrow batch.range)

#guard budgetControl { mixed := { observation := { ipc := { batches := 2 } } } }
  (.record .batchLimit) .batchLimit
#guard budgetControl { mixed := { observation := { totalRows := 5 } } }
  (.record (.budget (.limit .totalRows))) (.budget (.limit .totalRows))
#guard budgetControl { mixed := { observation := { totalCells := 23 } } }
  (.record (.budget (.limit .totalCells))) (.budget (.limit .totalCells))

-- The aggregate variadic count cap is an incremental check. Both
-- schedules hit it before the semantic check at this lower cap.
#guard budgetControl { totalDataBuffers := 4 } .dataBufferLimit
  (.decode (.field 3 (columnCause 0)))

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.PrefixMismatch
