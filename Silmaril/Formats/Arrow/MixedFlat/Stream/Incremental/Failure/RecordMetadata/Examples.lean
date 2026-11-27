module

import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Fixtures
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
import Silmaril.Prelude.Bytes.Write.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Fixtures
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Prelude.Bytes.Write.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.Stream.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.RecordMetadata

open Failure.Fixtures

private def rejectsPinned (fault : MixedFlat.MetadataError)
    (edit : KBytes → Option (Nat × Nat × Nat)) (limits : Incremental.Limits := {}) : Bool := Id.run do
  let .ok clean := Stream.read {} multi | return false
  let some last := clean.batches[2]? | return false
  let some (offset, width, word) := edit (last.range.metadataSlice multi) | return false
  let damaged := multi.write (last.range.offset + 8 + offset) width word
  return rejectsRecord limits multi damaged 2 (.metadata fault)

-- Shorten the descriptor vector while leaving counts, nodes and framing intact.
#guard rejectsPinned (.descriptorCount 11 10) fun metadata => do
  let vector ← recordVectorAt metadata 2
  if metadata.readLE vector 4 != some 11 then none else some (vector, 4, 10)

-- Clear the final record's variadic counts section. The Schema still has
-- two view fields and therefore requires two count words, including zero.
#guard rejectsPinned (.countCardinality 2 0) fun metadata => do
  let entry ← recordVtableEntry metadata 4
  let field ← metadata.readLE entry 2
  if field = 0 then none else some (entry, 2, 0)

-- Set the first field node's length to the signed Int64 minimum.
-- The shared metadata parser rejects the scalar before any layout binding.
#guard rejectsPinned (.metadata (.malformed .flatbuffer)) fun metadata => do
  let vector ← recordVectorAt metadata 1
  let length := vector + 4
  if metadata.readLE length 8 != some 2 then none else some (length, 8, 2^63)

-- The shared per-record sum check returns its own metadata error, even when
-- the same candidate sum would exceed the incremental running allowance.
#guard rejectsPinned .totalDataBufferLimit (limits := { mixed := { totalDataBuffers := 3 }, totalDataBuffers := 5 })
    fun metadata => do
  let vector ← recordVectorAt metadata 4
  let count := vector + 4
  if metadata.readLE count 8 != some 1 then none else some (count, 8, 3)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.RecordMetadata
