module

import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Fixtures
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
import Silmaril.Prelude.Bytes.Write.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Fixtures
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Prelude.Bytes.Write.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount

open Failure.Fixtures

-- Locate the node vector's length word in the known-good fixture metadata.
-- The vtable displacement is signed because FlatBuffers can share vtables.
private def referenceAt (metadata : KBytes) (table slot : Nat) : Option Nat := do
  let delta ← metadata.readLE table 4
  let vtable := if delta < 2^31 then table - delta else table + (2^32 - delta)
  let entry := vtable + 4 + slot * 2
  let width ← metadata.readLE vtable 2
  if entry + 2 > vtable + width then none
  else do
    let field ← metadata.readLE entry 2
    if field = 0 then none
    else do
      let position := table + field
      let offset ← metadata.readLE position 4
      return position + offset

private def shortenNodes (wire : KBytes) (range : Stream.BatchRange) (expected : Nat) : Option KBytes := do
  let metadata := range.metadataSlice wire
  let root ← metadata.readLE 0 4
  let batch ← referenceAt metadata root 2
  let nodes ← referenceAt metadata batch 1
  if expected = 0 || metadata.readLE nodes 4 != some expected then none
  else return wire.write (range.offset + 8 + nodes) 4 (expected - 1)

private def native : Except OrderedWriter.Error KBytes :=
  let batches : List OrderedWriter.BatchInput := [
    ⟨1, [.int32 "i" false [some 3]]⟩,
    ⟨0, [.int32 "i" false []]⟩,
    ⟨3, [.int32 "i" false [some 5, some 6, some 7]]⟩]
  OrderedWriter.emit {} (batches.headD ⟨0, []⟩).fields batches

-- Synthetic native control. Keep the original record extent and body but
-- shorten the final node vector from one to zero.
#guard Id.run do
  let .ok wire := native | return false
  let .ok clean := Stream.read {} wire | return false
  let some last := clean.batches[2]? | return false
  let some damaged := shortenNodes wire last.range 1 | return false
  return rejectsRecord { totalDataBuffers := 0 } wire damaged 2 (batchError 1 0)

-- Synthetic pinned PyArrow 26.0.1 control. The final metadata advertises
-- three nodes for the unchanged four-field Schema.
#guard Id.run do
  let .ok clean := Stream.read {} multi | return false
  let some last := clean.batches[2]? | return false
  let some damaged := shortenNodes multi last.range 4 | return false
  return rejectsRecord {} multi damaged 2 (batchError 4 3)

-- Batch slots are checked before typed metadata by both readers. The
-- running row and cell checks occur later in each reader.
#guard Id.run do
  let .ok wire := native | return false
  let .ok clean := Stream.read {} wire | return false
  let some last := clean.batches[2]? | return false
  let some damaged := shortenNodes wire last.range 1 | return false
  let tight := { observation := { totalRows := 1, totalCells := 1 } : MixedFlat.Limits }
  let two := { observation := { ipc := { batches := 2 } } : MixedFlat.Limits }
  let error := feedError 2 last.range.offset 1 0
  let batchLimit := Incremental.Error.batch 2 last.range.offset (.record .batchLimit)
  let bytes := singleBytes damaged
  let split := uneven damaged last.range
  let .error tightRead := Stream.read tight damaged | return false
  let .error limitRead := Stream.read two damaged | return false
  return decide (tightRead = .batch 2 (batchError 1 0) ∧ limitRead = .batch 2 .batchLimit) &&
    stopsAs { mixed := tight } clean 2 error bytes &&
    stopsAs { mixed := tight } clean 2 error split &&
    stopsAs { mixed := two } clean 2 batchLimit bytes &&
    stopsAs { mixed := two } clean 2 batchLimit split

-- The incremental body cap is part of framing. The immutable reader
-- rejects the typed metadata before consulting that cap for this frame.
#guard Id.run do
  let .ok wire := native | return false
  let .ok clean := Stream.read {} wire | return false
  let some last := clean.batches[2]? | return false
  let some damaged := shortenNodes wire last.range 1 | return false
  let limits : Incremental.Limits :=
    { mixed := { observation := { ipc := { bodyBytes := last.range.bodyLength - 1 } } } }
  let error := Incremental.Error.framing (some 2) ⟨.metadata, last.range.offset, .limit .bodyBytes⟩
  let .error immutable := Stream.read limits.mixed damaged | return false
  return decide (immutable = .batch 2 (batchError 1 0)) &&
    stopsAs limits clean 2 error (singleBytes damaged) &&
    stopsAs limits clean 2 error (uneven damaged last.range)

-- An incremental-only aggregate variadic-buffer cap can stop the valid
-- first record, before reaching the later metadata failure.
#guard Id.run do
  let .ok clean := Stream.read {} multi | return false
  let some first := clean.batches[0]? | return false
  let some last := clean.batches[2]? | return false
  let some damaged := shortenNodes multi last.range 4 | return false
  let limits : Incremental.Limits := { totalDataBuffers := 0 }
  let error := Incremental.Error.batch 0 first.range.offset .dataBufferLimit
  let .error immutable := Stream.read limits.mixed damaged | return false
  return decide (immutable = .batch 2 (batchError 4 3)) &&
    stopsAs limits clean 0 error (singleBytes damaged) &&
    stopsAs limits clean 0 error (uneven damaged last.range)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.NodeCount
