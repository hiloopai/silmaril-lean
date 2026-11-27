module

import Silmaril.Formats.Arrow.Binary.Stream.Events.Defs
import Silmaril.Formats.Arrow.Binary.Fixture
import Silmaril.Formats.Arrow.Binary.Stream.Fixture
meta import Silmaril.Formats.Arrow.Binary.Stream.Events.Defs
meta import Silmaril.Formats.Arrow.Binary.Fixture
meta import Silmaril.Formats.Arrow.Binary.Stream.Fixture

namespace Silmaril.Formats.Arrow.Binary.Stream.Events

private def fixture : Framing → KBytes
  | .modern => Binary.Fixture.stream
  | .legacy => Stream.Fixture.stream

private def schemaSize : Framing → Nat
  | .modern => Binary.Fixture.schemaSize
  | .legacy => Stream.Fixture.schemaSize

private def spans : Framing → List (Nat × Nat × Nat)
  | .modern => Binary.Fixture.batches
  | .legacy => Stream.Fixture.batches

private def expected : List (List (Option (List UInt8))) :=
  let longValue : List UInt8 := (List.replicate 3 [97, 98, 99, 0, 120, 121, 122]).flatten
  [[some [255, 0, 128], none, some [], some longValue], [], [none, none], [some []]]

private def observes (result : EventStream) (batches : List (List (Option (List UInt8))))
    (terminal : Arrow.Events.Termination Stream.Error) : Bool :=
  match result with
  | .error _ => false
  | .ok ⟨signature, trace⟩ =>
    decide (List.ofFn signature.kind = [(⟨"payload", true⟩, .binary)]) &&
      trace.batches.map (·.rowCount) == batches.map List.length &&
      (trace.batches.map fun batch =>
        List.ofFn fun i => (batch.values i).map (Option.map KBytes.toList)) ==
        batches.map (fun column => [column]) &&
      decide (trace.termination = terminal)

private def intact (framing : Framing) : Bool :=
  observes (readAll { batches := 4 } framing (fixture framing)) expected .eos

#guard intact .modern
#guard intact .legacy

private def schemaOnly (framing : Framing) : Bool :=
  let wire := fixture framing
  let width := framing.prefixSize
  observes (readAll { batches := 0 } framing
    (wire.slice 0 (width + schemaSize framing) ++ wire.slice (wire.len - width) width)) [] .eos

#guard schemaOnly .modern
#guard schemaOnly .legacy

-- Derive a malformed carrier from each pinned producer stream. The all-null
-- third batch must still validate both words of its first offset interval.
private def lateOffset (framing : Framing) : Bool := Id.run do
  let wire := fixture framing
  let some (start, size, _) := (spans framing)[2]? | return false
  let .ok message := Arrow.readMessage {} (wire.slice start size) | return false
  let .recordBatch batch := message.header | return false
  let some buffer := batch.buffers[1]? | return false
  let position := start + size + buffer.offset + 4
  let malformed := wire.slice 0 position ++ KBytes.leaf 4 0x80000000 ++
    wire.slice (position + 4) (wire.len - position - 4)
  let failure : Stream.Failure :=
    ⟨2, start - framing.prefixSize, .decode (.offsetNegative 1 0x80000000)⟩
  return observes (readAll {} framing malformed) (expected.take 2) (.readError (.record failure))

#guard lateOffset .modern
#guard lateOffset .legacy

private def limitsAndTail (framing : Framing) : Bool :=
  let wire := fixture framing
  let tailFailure : Stream.Failure := ⟨4, wire.len - framing.prefixSize, .trailingBytes⟩
  match (spans framing)[2]? with
  | none => false
  | some (start, _, _) =>
    let limitFailure : Stream.Failure := ⟨2, start - framing.prefixSize, .batchLimit⟩
    observes (readAll {} framing (wire ++ .leaf 1 0)) expected (.readError (.record tailFailure)) &&
      observes (readAll { batches := 2 } framing wire) (expected.take 2)
        (.readError (.record limitFailure)) &&
      observes ((reader {} framing).read 2 wire) (expected.take 2) .closed

#guard limitsAndTail .modern
#guard limitsAndTail .legacy

#guard match readAll {} .modern (fixture .legacy), readAll {} .legacy (fixture .modern) with
  | .error (.schema (.envelope (.unsupported .legacyFraming))),
    .error (.schema (.envelope (.malformed .metadataLength))) => true
  | _, _ => false

end Silmaril.Formats.Arrow.Binary.Stream.Events
