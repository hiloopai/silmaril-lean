module

import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Fixtures
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
import Silmaril.Prelude.Bytes.Write.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Fixtures
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Prelude.Bytes.Write.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout

open Failure.Fixtures

private def damageNode (range : Stream.BatchRange) : Option KBytes := do
  let metadata := range.metadataSlice multi
  let vector ← recordVectorAt metadata 1
  let length := vector + 4
  if metadata.readLE length 8 != some 2 then none
  else return multi.write (range.offset + 8 + length) 8 1

private def damageDescriptor (range : Stream.BatchRange) : Option KBytes := do
  let metadata := range.metadataSlice multi
  let vector ← recordVectorAt metadata 2
  if metadata.readLE vector 4 != some 11 then none else do
    let last := vector + 4 + 16 * 10
    let offset ← metadata.readLE last 8
    let length ← metadata.readLE (last + 8) 8
    if offset + length > range.bodyLength then none
    else return multi.write (range.offset + 8 + last + 8) 8 (range.bodyLength - offset + 1)

-- Synthetic edit to the pinned PyArrow stream. The nonnegative node
-- length is accepted as metadata but does not match the record row count.
#guard Id.run do
  let .ok clean := Stream.read {} multi | return false
  let some last := clean.batches[2]? | return false
  let some damaged := damageNode last.range | return false
  return rejectsRecord {} multi damaged 2 (.decode (.plan (.field 0 .invalidNode)))

-- The final descriptor remains signed-valid and its cardinality is unchanged.
-- Its last byte is now outside the complete framed body.
#guard Id.run do
  let .ok clean := Stream.read {} multi | return false
  let some last := clean.batches[2]? | return false
  let some damaged := damageDescriptor last.range | return false
  return rejectsRecord {} multi damaged 2 (.decode (.body (.malformed .batchLayout)))

-- With both common limits exceeded, rows win over cells. If the
-- incremental-only aggregate allowance also fails, it wins only on feed.
#guard Id.run do
  let .ok clean := Stream.read {} multi | return false
  let some last := clean.batches[2]? | return false
  let some damaged := damageDescriptor last.range | return false
  let mixed : MixedFlat.Limits := { observation := { totalRows := 5, totalCells := 23 } }
  let rows : Stream.BatchError := .budget (.limit .totalRows)
  let shared := Incremental.Error.batch 2 last.range.offset (.record rows)
  let aggregate := Incremental.Error.batch 2 last.range.offset .dataBufferLimit
  let .error eager := Stream.read mixed damaged | return false
  let .ok ⟨_, pulled⟩ := Stream.Events.readAll mixed damaged | return false
  let .readError pullError := pulled.termination | return false
  let bytes := singleBytes damaged
  let split := uneven damaged last.range
  return decide (eager = .batch 2 rows ∧ pullError = .message 2 last.range.offset rows) &&
    stopsAs { mixed, totalDataBuffers := 5 } clean 2 shared bytes &&
    stopsAs { mixed, totalDataBuffers := 5 } clean 2 shared split &&
    stopsAs { mixed, totalDataBuffers := 4 } clean 2 aggregate bytes &&
    stopsAs { mixed, totalDataBuffers := 4 } clean 2 aggregate split

-- Admit the exact row count and fail the common cell limit before layout.
#guard Id.run do
  let .ok clean := Stream.read {} multi | return false
  let some last := clean.batches[2]? | return false
  let some damaged := damageNode last.range | return false
  let limits : Incremental.Limits :=
    { mixed := { observation := { totalRows := 6, totalCells := 23 } }, totalDataBuffers := 5 }
  let cells : Stream.BatchError := .budget (.limit .totalCells)
  let error := Incremental.Error.batch 2 last.range.offset (.record cells)
  let .error eager := Stream.read limits.mixed damaged | return false
  return decide (eager = .batch 2 cells) &&
    stopsAs limits clean 2 error (singleBytes damaged) &&
    stopsAs limits clean 2 error (uneven damaged last.range)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.BodyLayout
