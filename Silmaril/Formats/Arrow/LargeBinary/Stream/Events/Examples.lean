module

public import Silmaril.Formats.Arrow.LargeBinary.Stream.Events.Defs
public import Silmaril.Formats.Arrow.LargeBinary.Stream.Fixture
meta import Silmaril.Formats.Arrow.LargeBinary.Stream.Events.Defs
meta import Silmaril.Formats.Arrow.LargeBinary.Stream.Fixture

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeBinary.Stream.Events.Examples

def inputs : List (String × Framing × KBytes) :=
  [("modern", .modern, Fixture.modern), ("legacy", .legacy, Fixture.legacy)]

private def expected : List (List (Option (List UInt8))) :=
  let longValue : List UInt8 := (List.replicate 3 [97, 98, 0, 99, 100]).flatten
  [[some [255, 0, 128], none, some [], some longValue],
   [], [some [97, 98, 99, 100], none, some [122]], [none, none]]

private def observes (events : EventStream) (batches : List (List (Option (List UInt8))))
    (terminal : Arrow.Events.Termination Stream.Error) : Bool :=
  match observe events with
  | .error _ => false
  | .ok ⟨signature, trace⟩ =>
    decide (List.ofFn signature.kind = [(⟨"payload", true⟩, .largeBinary)]) &&
      trace.batches.map (·.rowCount) == batches.map List.length &&
      (trace.batches.map fun batch => List.ofFn batch.values) == batches.map (fun column => [column]) &&
      decide (trace.termination = terminal)

private def roundtrip (framing : Framing) (wire : KBytes)
    (batches : List (List (Option (List UInt8)))) : Bool :=
  let source := readAll {} framing wire
  observes source batches .eos &&
    match emit {} source with
    | .error _ => false
    | .ok output =>
      observes (readAll {} .modern output) batches .eos &&
        (output.slice (output.len - 8) 8).toList == [255, 255, 255, 255, 0, 0, 0, 0]

#guard inputs.all fun (_, framing, wire) => roundtrip framing wire expected

private def schemaOnly (framing : Framing) (wire : KBytes) : KBytes :=
  let size := match framing with
    | .modern => Fixture.modernSchemaSize
    | .legacy => Fixture.legacySchemaSize
  wire.slice 0 (framing.prefixSize + size) ++
    wire.slice (wire.len - framing.prefixSize) framing.prefixSize

#guard inputs.all fun (_, framing, wire) => roundtrip framing (schemaOnly framing wire) []

private def refuses (source : EventStream) (expectedError : SinkError) : Bool :=
  match emit {} source with
  | .error error => decide (error = expectedError)
  | .ok _ => false

-- Synthetic control: mutate the third batch's second interval at its
-- original i64 offset word, leaving the two preceding batches complete.
private def lateOffset (framing : Framing) (wire : KBytes) : Bool := Id.run do
  let ranges := match framing with
    | .modern => Fixture.modernRanges
    | .legacy => Fixture.legacyRanges
  let some (offset, size, _) := ranges[2]? | return false
  let .ok message := Arrow.readMessage {} (wire.slice (offset + framing.prefixSize) size) |
    return false
  let .recordBatch record := message.header | return false
  let some offsets := record.buffers[1]? | return false
  let word := offset + framing.prefixSize + size + offsets.offset + 16
  let damaged := wire.slice 0 word ++ KBytes.leaf 8 0x8000000000000000 ++
    wire.slice (word + 8) (wire.len - word - 8)
  let cause : Stream.Error := .record ⟨2, offset, .decode (.offsetNegative 2 0x8000000000000000)⟩
  let source := readAll {} framing damaged
  return observes source (expected.take 2) (.readError cause) &&
    refuses source (.termination (.readError cause))

#guard inputs.all fun (_, framing, wire) => lateOffset framing wire

private def tail (framing : Framing) (wire : KBytes) : Bool :=
  let source := readAll {} framing (wire ++ .leaf 1 0)
  let cause : Stream.Error := .record ⟨4, wire.len - framing.prefixSize, .trailingBytes⟩
  observes source expected (.readError cause) && refuses source (.termination (.readError cause))

#guard inputs.all fun (_, framing, wire) => tail framing wire

#guard inputs.all fun (_, framing, wire) =>
  let closed := (reader {} framing).read 2 wire
  observes closed (expected.take 2) .closed && refuses closed (.termination .closed)

#guard refuses (readAll {} .modern Fixture.legacy)
  (.openError (.schema (.envelope (.unsupported .legacyFraming))))

#guard refuses (.ok ⟨⟨0, Fin.elim0⟩, ⟨[], .eos⟩⟩) (.fieldCount 0)

end Silmaril.Formats.Arrow.LargeBinary.Stream.Events.Examples
