module

import Silmaril.Formats.Arrow.Binary.Stream.Defs
import Silmaril.Formats.Arrow.Binary.Fixture
import Silmaril.Formats.Arrow.Binary.Stream.Fixture
meta import Silmaril.Formats.Arrow.Binary.Stream.Defs
meta import Silmaril.Formats.Arrow.Binary.Fixture
meta import Silmaril.Formats.Arrow.Binary.Stream.Fixture

namespace Silmaril.Formats.Arrow.Binary.Stream

private def input : Framing → KBytes
  | .modern => Binary.Fixture.stream
  | .legacy => Fixture.stream

private def schemaSize : Framing → Nat
  | .modern => Binary.Fixture.schemaSize
  | .legacy => Fixture.schemaSize

private def ranges (framing : Framing) : List Range :=
  let spans := match framing with
    | .modern => Binary.Fixture.batches
    | .legacy => Fixture.batches
  spans.map fun (start, metadata, body) =>
    ⟨start - framing.prefixSize, framing.prefixSize, metadata, body⟩

private def eosOffset (framing : Framing) : Nat := (input framing).len - framing.prefixSize

private def expected : List (List (Option (List UInt8))) :=
  let longValue : List UInt8 := (List.replicate 3 [97, 98, 99, 0, 120, 121, 122]).flatten
  [[some [255, 0, 128], none, some [], some longValue], [], [none, none], [some []]]

private def observes (batches : List Batch) (frames : List Range)
    (values : List (List (Option (List UInt8)))) : Bool :=
  decide (batches.map Batch.range = frames) &&
    batches.map (fun batch => batch.values.map (Option.map KBytes.toList)) == values

private def exact (framing : Framing) : Bool :=
  match read { batches := 4 } framing (input framing) with
  | .ok observed =>
    decide (observed.field = ⟨"payload", true⟩) &&
      observed.eosOffset == eosOffset framing && observes observed.batches (ranges framing) expected
  | .error _ => false

#guard exact .modern
#guard exact .legacy

-- PyArrow independently emits these exact schema-only bytes.
private def schemaOnly (framing : Framing) : Bool :=
  let stop := framing.prefixSize + schemaSize framing
  let wire := (input framing).slice 0 stop ++
    (input framing).slice (eosOffset framing) framing.prefixSize
  match read { batches := 0 } framing wire with
  | .ok observed => decide (observed.field = ⟨"payload", true⟩) &&
      observed.batches.isEmpty && observed.eosOffset == stop
  | .error _ => false

#guard schemaOnly .modern
#guard schemaOnly .legacy

private def failsAfter (limits : Limits) (framing : Framing) (wire : KBytes)
    (count : Nat) (failure : Failure) : Bool :=
  match readAll limits framing wire, read limits framing wire with
  | .ok (field, trace), .error (.record eager) =>
    decide (field = ⟨"payload", true⟩ ∧ trace.terminal = .failed failure ∧ eager = failure) &&
      observes trace.batches ((ranges framing).take count) (expected.take count)
  | _, _ => false

-- Synthetic suffix and truncation controls. Earlier batches remain observable.
private def terminalErrors (framing : Framing) : Bool :=
  let wire := input framing
  let stop := eosOffset framing
  failsAfter {} framing (wire ++ .leaf 1 0) 4 ⟨4, stop, .trailingBytes⟩ &&
    failsAfter {} framing (wire.slice 0 (wire.len - 1)) 4
      ⟨4, stop, .envelope (.malformed .truncated)⟩

#guard terminalErrors .modern
#guard terminalErrors .legacy

private def pullFailsAfterTwo (framing : Framing) (wire : KBytes) (failure : Failure) : Bool := Id.run do
  let .ok cursor := openInput {} framing wire | return false
  let .ok (some (first, cursor)) := cursor.next | return false
  let .ok (some (empty, cursor)) := cursor.next | return false
  let .error actual := cursor.next | return false
  return decide (actual = failure) &&
    observes [first, empty] ((ranges framing).take 2) (expected.take 2)

private def recordErrors (framing : Framing) : Bool := Id.run do
  let wire := input framing
  let some third := (ranges framing)[2]? | return false
  let .ok message := Arrow.readMessage {} (wire.slice third.metadataStart third.metadataSize)
    | return false
  let .recordBatch batch := message.header | return false
  let some offsets := batch.buffers[1]? | return false
  -- Change the second i32 word of the all-null third batch.
  let position := third.bodyStart + offsets.offset + 4
  let negative := wire.slice 0 position ++ KBytes.leaf 4 0x80000000 ++
    wire.slice (position + 4) (wire.len - position - 4)
  let earlySchema := wire.slice 0 third.offset ++ wire.slice 0 (framing.prefixSize + schemaSize framing)
  let failure : Failure := ⟨2, third.offset, .decode (.offsetNegative 1 0x80000000)⟩
  return
    pullFailsAfterTwo framing negative failure &&
    failsAfter {} framing negative 2 failure &&
    failsAfter {} framing (wire.slice 0 (third.next - 1)) 2
      ⟨2, third.offset, .body (.malformed .truncated)⟩ &&
    failsAfter {} framing earlySchema 2 ⟨2, third.offset, .metadata (.unsupported (.fieldType 4))⟩ &&
    failsAfter { batches := 2 } framing negative 2 ⟨2, third.offset, .batchLimit⟩

#guard recordErrors .modern
#guard recordErrors .legacy

#guard match openInput {} .modern (input .legacy), openInput {} .legacy (input .modern) with
  | .error (.envelope (.unsupported .legacyFraming)), .error (.envelope (.malformed .metadataLength)) =>
    true
  | _, _ => false

#guard match openInput {} .legacy (.leaf 4 0), openInput {} .modern (.leaf 8 0xffffffff) with
  | .error .expectedSchema, .error .expectedSchema => true
  | _, _ => false

-- Legacy framing remains opt-in at the new entry point.
#guard match Arrow.readStream {} (input .legacy) with
  | .error (.unsupported .legacyFraming) => true
  | _ => false

end Silmaril.Formats.Arrow.Binary.Stream
