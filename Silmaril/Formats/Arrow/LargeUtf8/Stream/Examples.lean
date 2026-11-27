module

import Silmaril.Formats.Arrow.LargeUtf8.Stream.Defs
import Silmaril.Formats.Arrow.LargeUtf8.Stream.Fixture
import Silmaril.Formats.Arrow.LargeBinary.Stream.Defs
import Silmaril.Formats.Arrow.LargeBinary.Stream.Fixture
meta import Silmaril.Formats.Arrow.LargeUtf8.Stream.Defs
meta import Silmaril.Formats.Arrow.LargeUtf8.Stream.Fixture
meta import Silmaril.Formats.Arrow.LargeBinary.Stream.Defs
meta import Silmaril.Formats.Arrow.LargeBinary.Stream.Fixture

namespace Silmaril.Formats.Arrow.LargeUtf8.Stream

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

private def expected : List LargeUtf8.Column :=
  [[some "雪", none, some "", some (("é".push (Char.ofNat 0)) ++ "🙂")],
   [], [none, some "", some "é"], [none, none]]

private def observes (framing : Framing) (wire : KBytes) : Bool :=
  match read { batches := 4 } framing wire with
  | .ok observed =>
    decide (observed.field = ⟨"payload", true⟩) &&
      decide (observed.batches.map (·.range) = ranges framing) &&
      observed.eosOffset == eosOffset framing && observed.batches.map (·.values) == expected
  | .error _ => false

#guard observes .modern Fixture.modern
#guard observes .legacy Fixture.legacy

private def schemaOnly (framing : Framing) : Bool :=
  let wire := input framing
  let offset := framing.prefixSize + schemaSize framing
  let empty := wire.slice 0 offset ++ wire.slice (eosOffset framing) framing.prefixSize
  match read { batches := 0 } framing empty with
  | .ok observed =>
    decide (observed.field = ⟨"payload", true⟩) &&
      observed.batches.isEmpty && observed.eosOffset == offset
  | .error _ => false

#guard schemaOnly .modern
#guard schemaOnly .legacy

private def fails (result : Except Error Observed) (expectedError : Error) : Bool :=
  match result with
  | .error actual => decide (actual = expectedError)
  | .ok _ => false

-- Every synthetic control is derived from the same admitted producer frame.
private def patchThird (framing : Framing) (descriptor inner width word : Nat) :
    Option (Nat × KBytes) := do
  let wire := input framing
  let range ← (ranges framing)[2]?
  let .ok message := Arrow.readMessage {} (wire.slice range.metadataStart range.metadataSize) |
    none
  let .recordBatch batch := message.header | none
  let buffer ← batch.buffers[descriptor]?
  if inner + width > buffer.length then none
  else
    let position := range.bodyStart + buffer.offset + inner
    return (range.offset, wire.slice 0 position ++ KBytes.leaf width word ++
      wire.slice (position + width) (wire.len - position - width))

private def rejectsPatch (framing : Framing) (descriptor inner width word : Nat) (cause : Cause) : Bool :=
  match patchThird framing descriptor inner width word with
  | some (offset, amended) => fails (read {} framing amended) (.record 2 offset cause)
  | none => false

-- Validity: adding a present bit conflicts with the declared null count.
#guard rejectsPatch .modern 0 0 1 7 (.ipc (.decode (.ipc (.malformed .validityBitmap))))
#guard rejectsPatch .legacy 0 0 1 7 (.ipc (.decode (.ipc (.malformed .validityBitmap))))

-- Geometry: a negative i64 under a null remains invalid.
#guard rejectsPatch .modern 1 8 8 (2^63) (.ipc (.decode (.offsetNegative 1 (2^63))))
#guard rejectsPatch .legacy 1 8 8 (2^63) (.ipc (.decode (.offsetNegative 1 (2^63))))

-- Geometry: the final offset cannot use body padding as data.
#guard rejectsPatch .modern 1 24 8 4 (.ipc (.decode (.offsetOutsideData 3 4 3)))
#guard rejectsPatch .legacy 1 24 8 4 (.ipc (.decode (.offsetOutsideData 3 4 3)))

-- UTF-8: the invalid leading byte is in the present third slot.
#guard rejectsPatch .modern 2 1 1 255 (.invalidUtf8 2)
#guard rejectsPatch .legacy 2 1 1 255 (.invalidUtf8 2)

-- UTF-8: the allocated one-byte span of the null first slot is unobserved.
private def nullBytes (framing : Framing) : Bool :=
  match patchThird framing 2 0 1 255 with
  | some (_, amended) => observes framing amended
  | none => false

#guard nullBytes .modern
#guard nullBytes .legacy

private def endErrors (framing : Framing) : Bool :=
  let wire := input framing
  fails (read {} framing (wire ++ .leaf 1 0)) (.record 4 (eosOffset framing) (.ipc .trailingBytes)) &&
    fails (read {} framing (wire.slice 0 (wire.len - 1)))
      (.record 4 (eosOffset framing) (.ipc (.envelope (.malformed .truncated))))

#guard endErrors .modern
#guard endErrors .legacy

#guard fails (read { batches := 1 } .modern Fixture.modern) (.record 1 344 (.ipc .batchLimit))
#guard fails (read {} .modern LargeBinary.Stream.Fixture.modern)
  (.schema (.metadata (.metadata (.unsupported (.fieldType 19)))))

#guard match LargeBinary.Stream.read {} .modern Fixture.modern with
  | .error (.schema (.metadata (.metadata (.unsupported (.fieldType 20))))) => true
  | _ => false

end Silmaril.Formats.Arrow.LargeUtf8.Stream
