module

import Silmaril.Formats.Arrow.Binary.Defs
import Silmaril.Formats.Arrow.Binary.Fixture
meta import Silmaril.Formats.Arrow.Binary.Defs
meta import Silmaril.Formats.Arrow.Binary.Fixture

namespace Silmaril.Formats.Arrow.Binary

private def schema := Fixture.stream.slice 8 Fixture.schemaSize

private def expected : List (List (Option (List UInt8))) :=
  let longValue : List UInt8 := (List.replicate 3 [97, 98, 99, 0, 120, 121, 122]).flatten
  [[some [255, 0, 128], none, some [], some longValue], [], [none, none], [some []]]

private def observes (limits : Limits) (ranges : Nat × Nat × Nat)
    (values : List (Option (List UInt8))) : Bool :=
  let (start, metaSize, bodySize) := ranges
  match readBatch limits schema (Fixture.stream.slice start metaSize)
      (Fixture.stream.slice (start + metaSize) bodySize) with
  | .ok observed =>
    decide (observed.field = ⟨"payload", true⟩) &&
      observed.values.map (Option.map KBytes.toList) == values
  | .error _ => false

#guard (List.zipWith (observes {}) Fixture.batches expected).length == 4
#guard (List.zipWith (observes {}) Fixture.batches expected).all id

-- The existing Schema profiles still reject plain Binary's tag 4.
#guard match Arrow.readMessage {} schema with
  | .error (.unsupported (.fieldType 4)) => true
  | _ => false

#guard match SchemaReader.readMessage {} schema with
  | .error (.unsupported (.fieldType 4)) => true
  | _ => false


#guard match MixedFlat.readSchema {} schema with
  | .error (.unsupported (.fieldType 4)) => true
  | _ => false

-- The producer supplies the envelope ranges for these paired-message tests.
private def fixtureBatch (limits : Limits) (index : Nat) (bodySize : Nat → Nat := id) :
    Except Error Observed := do
  let some (start, metadataLength, length) := Fixture.batches[index]? |
    throw (.ipc (.malformed .truncated))
  readBatch limits schema (Fixture.stream.slice start metadataLength)
    (Fixture.stream.slice (start + metadataLength) (bodySize length))

private def batchFails (attempt : Except Error Observed) (expectedError : Error) : Bool :=
  match attempt with
  | .error actual => decide (actual = expectedError)
  | .ok _ => false

#guard batchFails (fixtureBatch { rows := 3 } 0) (.ipc (.limit .rows))
#guard batchFails (fixtureBatch { bodyBytes := 1 } 0) (.ipc (.limit .bodyBytes))
#guard batchFails (fixtureBatch { fields := 0 } 0) (.schema (.metadata (.limit .fields)))
#guard batchFails (fixtureBatch { metadataBytes := 1 } 0)
  (.schema (.metadata (.limit .metadataBytes)))
#guard match fixtureBatch {} 0 (· - 1) with
  | .error (.bodyLength declared actual) => declared = actual + 1
  | _ => false

private def fails (attempt : Except Error Column) (expectedError : Error) : Bool :=
  match attempt with
  | .error actual => decide (actual = expectedError)
  | .ok _ => false

-- Synthetic physical controls. The two words in each 8-byte leaf are i32 LE.
private def bytes : KBytes := .leaf 3 0xff80aa

#guard match readColumn {} true ⟨1, 0⟩ ⟨.empty, .leaf 8 0x0000000300000001, bytes⟩ with
  | .ok [some result] => result.toList == [128, 255]
  | _ => false

#guard fails (readColumn {} true ⟨1, 0⟩ ⟨.empty, .leaf 8 0x8000000000000000, bytes⟩)
  (.offsetNegative 1 0x80000000)
#guard fails (readColumn {} true ⟨1, 1⟩ ⟨.leaf 1 0, .leaf 8 0x0000000100000002, bytes⟩)
  (.offsetDescending 1 2 1)
#guard fails (readColumn {} true ⟨1, 0⟩ ⟨.empty, .leaf 8 0x0000000400000000, bytes⟩)
  (.offsetOutsideData 1 4 3)
#guard fails (readColumn {} true ⟨1, 0⟩ ⟨.empty, .leaf 4 0, bytes⟩)
  (.offsetMissing 1)
#guard fails (readColumn {} true ⟨0, 0⟩ ⟨.empty, .empty, .empty⟩)
  (.offsetMissing 0)
#guard fails (readColumn {} true ⟨0, 0⟩ ⟨.empty, .leaf 4 0xffffffff, .empty⟩)
  (.offsetNegative 0 0xffffffff)
#guard fails (readColumn {} true ⟨9, 0⟩ ⟨.leaf 1 0xff, .leaf 40 0, .empty⟩)
  (.ipc (.malformed .validityBitmap))
#guard fails (readColumn {} true ⟨1, 1⟩ ⟨.empty, .leaf 8 0, .empty⟩)
  (.ipc (.malformed .validityBitmap))
#guard fails (readColumn {} false ⟨1, 1⟩ ⟨.leaf 1 0, .leaf 8 0, .empty⟩)
  (.ipc (.malformed .validityBitmap))

-- A physical descriptor cannot reach past the body even if logical offsets fit.
#guard match bindBody {} ⟨1, [⟨1, 0⟩], [⟨0, 0⟩, ⟨0, 8⟩, ⟨8, 1⟩]⟩ (.leaf 8 0) with
  | .error (.ipc (.malformed .batchLayout)) => true
  | _ => false

end Silmaril.Formats.Arrow.Binary
