module

import Silmaril.Formats.Arrow.LargeBinary.Stream.Defs
import Silmaril.Formats.Arrow.LargeBinary.Stream.Fixture
import Silmaril.Formats.Arrow.Binary.Fixture
meta import Silmaril.Formats.Arrow.LargeBinary.Stream.Defs
meta import Silmaril.Formats.Arrow.LargeBinary.Stream.Fixture
meta import Silmaril.Formats.Arrow.Binary.Fixture

namespace Silmaril.Formats.Arrow.LargeBinary.Stream

private def input : Framing → KBytes
  | .modern => Fixture.modern
  | .legacy => Fixture.legacy

private def schemaSize : Framing → Nat
  | .modern => Fixture.modernSchemaSize
  | .legacy => Fixture.legacySchemaSize

private def ranges (framing : Framing) : List Range :=
  let spans := match framing with
    | .modern => Fixture.modernRanges
    | .legacy => Fixture.legacyRanges
  spans.map fun (offset, metadataSize, bodyLength) =>
    ⟨offset, framing.prefixSize, metadataSize, bodyLength⟩

private def eosOffset : Framing → Nat
  | .modern => Fixture.modernEos
  | .legacy => Fixture.legacyEos

private def expected : List (List (Option (List UInt8))) :=
  let longValue : List UInt8 := (List.replicate 3 [97, 98, 0, 99, 100]).flatten
  [[some [255, 0, 128], none, some [], some longValue],
   [], [some [97, 98, 99, 100], none, some [122]], [none, none]]

private def observes (framing : Framing) : Bool :=
  match read { batches := 4 } framing (input framing) with
  | .ok observed =>
    decide (observed.field = ⟨"payload", true⟩ ∧ observed.batches.map (·.range) = ranges framing) &&
      observed.eosOffset == eosOffset framing &&
      (observed.batches.map fun batch => batch.values.map (Option.map KBytes.toList)) == expected
  | .error _ => false

#guard observes .modern
#guard observes .legacy

-- PyArrow independently emits the schema-only spans for both framings.
private def schemaOnly (framing : Framing) : Bool :=
  let wire := input framing
  let start := framing.prefixSize + schemaSize framing
  let empty := wire.slice 0 start ++ wire.slice (eosOffset framing) framing.prefixSize
  match read { batches := 0 } framing empty with
  | .ok observed =>
    decide (observed.field = ⟨"payload", true⟩) &&
      observed.batches.isEmpty && observed.eosOffset == start
  | .error _ => false

#guard schemaOnly .modern
#guard schemaOnly .legacy

private def fails (attempt : Except Error Observed) (expectedError : Error) : Bool :=
  match attempt with
  | .error actual => decide (actual = expectedError)
  | .ok _ => false

-- Synthetic controls patch one LE i64 word of the third producer batch.
private def patched (framing : Framing) (index word : Nat) (cause : LargeBinary.Error) : Bool :=
  let wire := input framing
  match (ranges framing)[2]? with
  | none => false
  | some range => Id.run do
    let .ok message := Arrow.readMessage {} (wire.slice range.metadataStart range.metadataSize)
      | return false
    let .recordBatch batch := message.header | return false
    let [_, offsets, data] := batch.buffers | return false
    let position := range.bodyStart + offsets.offset + 8 * index
    if data.length != 5 || position + 8 > range.bodyStart + offsets.offset + offsets.length then
      return false
    let malformed := wire.slice 0 position ++ KBytes.leaf 8 word ++
      wire.slice (position + 8) (wire.len - position - 8)
    return fails (read {} framing malformed) (.record ⟨2, range.offset, .decode cause⟩)

-- Signed offset refusal at the high bit of an i64 word.
#guard patched .modern 2 0x8000000000000000 (.offsetNegative 2 0x8000000000000000)
#guard patched .legacy 2 0x8000000000000000 (.offsetNegative 2 0x8000000000000000)

-- Monotonicity refusal under a null slot.
#guard patched .modern 2 3 (.offsetDescending 2 4 3)
#guard patched .legacy 2 3 (.offsetDescending 2 4 3)

-- The final word crosses the five-byte data descriptor into body padding.
#guard patched .modern 3 6 (.offsetOutsideData 3 6 5)
#guard patched .legacy 3 6 (.offsetOutsideData 3 6 5)

private def endErrors (framing : Framing) : Bool :=
  let wire := input framing
  fails (read {} framing (wire ++ .leaf 1 0)) (.record ⟨4, eosOffset framing, .trailingBytes⟩) &&
    fails (read {} framing (wire.slice 0 (wire.len - 1)))
      (.record ⟨4, eosOffset framing, .envelope (.malformed .truncated)⟩)

#guard endErrors .modern
#guard endErrors .legacy

#guard fails (read { batches := 1 } .modern Fixture.modern) (.record ⟨1, 352, .batchLimit⟩)
#guard fails (read {} .modern Binary.Fixture.stream) (.schema (.metadata (.metadata (.unsupported (.fieldType 4)))))

#guard match Binary.Stream.read {} .modern Fixture.modern with
  | .error (.schema (.metadata (.metadata (.unsupported (.fieldType 19))))) => true
  | _ => false

-- A compact synthetic zero buffer permits a nonnegative i64 offset whose
-- low word has the i32 sign bit set. It has no large allocated octet array.
#guard match LargeBinary.readColumn { bodyBytes := 2^32 } true ⟨1, 0⟩
    ⟨.empty, .leaf 16 0x00000000800000010000000080000000, .leaf (2^31 + 1) 0⟩ with
  | .ok [some value] => value.toList == [0]
  | _ => false

#guard match LargeBinary.readColumn {} true ⟨0, 0⟩ ⟨.empty, .leaf 4 0, .empty⟩ with
  | .error (.offsetMissing 0) => true
  | _ => false

end Silmaril.Formats.Arrow.LargeBinary.Stream
