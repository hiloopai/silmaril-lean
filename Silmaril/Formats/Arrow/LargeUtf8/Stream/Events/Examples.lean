module

public import Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Defs
public import Silmaril.Formats.Arrow.LargeUtf8.Stream.Fixture
meta import Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Defs
meta import Silmaril.Formats.Arrow.LargeUtf8.Stream.Fixture

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Examples

def schemaOnly (framing : Framing) (wire : KBytes) : KBytes :=
  let schemaSize := match framing with
    | .modern => Fixture.modernSchemaSize
    | .legacy => Fixture.legacySchemaSize
  wire.slice 0 (framing.prefixSize + schemaSize) ++
    wire.slice (wire.len - framing.prefixSize) framing.prefixSize

def inputs : List (String × Framing × KBytes) :=
  [("modern", .modern, Fixture.modern), ("legacy", .legacy, Fixture.legacy)]

def schemaInputs : List (String × Framing × KBytes) :=
  inputs.map fun (name, framing, wire) => (name ++ "_schema_only", framing, schemaOnly framing wire)

private def field : LargeUtf8.Field := ⟨"payload", true⟩

private def expected : List LargeUtf8.Column :=
  [[some "雪", none, some "", some (("é".push (Char.ofNat 0)) ++ "🙂")],
   [], [none, some "", some "é"], [none, none]]

private def observes (events : EventStream) (batches : List LargeUtf8.Column)
    (terminal : Arrow.Events.Termination Stream.Error) : Bool :=
  match events with
  | .error _ => false
  | .ok ⟨signature, trace⟩ =>
    decide (List.ofFn signature.kind = [(field, .largeUtf8)]) &&
      trace.batches.map (·.rowCount) == batches.map List.length &&
      (trace.batches.map fun batch => List.ofFn batch.values) == batches.map (fun column => [column]) &&
      decide (trace.termination = terminal)

private def roundtrip (limits : Limits) (framing : Framing) (wire : KBytes)
    (batches : List LargeUtf8.Column) : Bool :=
  let source := readAll limits framing wire
  observes source batches .eos &&
    match emit limits source with
    | .error _ => false
    | .ok output =>
      observes (readAll limits .modern output) batches .eos &&
        (output.slice (output.len - 8) 8).toList == [255, 255, 255, 255, 0, 0, 0, 0]

#guard inputs.all fun (_, framing, wire) => roundtrip { batches := 4 } framing wire expected
#guard schemaInputs.all fun (_, framing, wire) => roundtrip { batches := 0 } framing wire []

private def refuses (source : EventStream) (expectedError : SinkError) : Bool :=
  match emit {} source with
  | .error error => decide (error = expectedError)
  | .ok _ => false

private def failed (source : EventStream) (delivered : List LargeUtf8.Column)
    (cause : Stream.Error) : Bool :=
  observes source delivered (.readError cause) && refuses source (.termination (.readError cause))

-- Synthetic control: change one present byte in record 2, after both a
-- populated and an empty record. The UTF-8 cause retains its slot index.
private def lateUtf8 (framing : Framing) (wire : KBytes) : Bool := Id.run do
  let ranges := match framing with
    | .modern => Fixture.modernRanges
    | .legacy => Fixture.legacyRanges
  let some (offset, size, _) := ranges[2]? | return false
  let .ok message := Arrow.readMessage {} (wire.slice (offset + framing.prefixSize) size) |
    return false
  let .recordBatch record := message.header | return false
  let some data := record.buffers[2]? | return false
  let firstPresent := offset + framing.prefixSize + size + data.offset + 1
  let damaged := wire.slice 0 firstPresent ++ KBytes.leaf 1 255 ++
    wire.slice (firstPresent + 1) (wire.len - firstPresent - 1)
  return failed (readAll {} framing damaged) (expected.take 2) (.record 2 offset (.invalidUtf8 2))

#guard inputs.all fun (_, framing, wire) => lateUtf8 framing wire

private def endErrors (framing : Framing) (wire : KBytes) : Bool :=
  let eos := wire.len - framing.prefixSize
  failed (readAll {} framing (wire ++ .leaf 1 0)) expected (.record 4 eos (.ipc .trailingBytes)) &&
    failed (readAll {} framing (wire.slice 0 (wire.len - 1))) expected
      (.record 4 eos (.ipc (.envelope (.malformed .truncated))))

#guard inputs.all fun (_, framing, wire) => endErrors framing wire

#guard inputs.all fun (_, framing, wire) =>
  let closed := (reader {} framing).read 2 wire
  observes closed (expected.take 2) .closed && refuses closed (.termination .closed)

#guard inputs.all fun (_, framing, wire) =>
  failed (readAll { batches := 2 } framing wire) (expected.take 2) (.record 2 504 (.ipc .batchLimit))

#guard refuses (readAll {} .modern Fixture.legacy)
  (.openError (.schema (.envelope (.unsupported .legacyFraming))))

#guard refuses (.ok ⟨⟨0, Fin.elim0⟩, ⟨[], .eos⟩⟩) (.fieldCount 0)

private def writeRead (batches : List LargeUtf8.Column) : Option EventStream :=
  let events : EventStream := .ok ⟨schema field, ⟨batches.map (ofValues field), .eos⟩⟩
  match emit {} events with
  | .ok wire => some (readAll {} .modern wire)
  | .error _ => none

private def projectZero (events : EventStream) (batchCounts : List Nat) : Bool :=
  match events.scan (fun signature => Silmaril.Relational.Scan.Projection.ofArray (source := signature) #[])
      (fun _ _ => true) with
  | .ok ⟨signature, trace⟩ =>
    signature.width == 0 && trace.batches.map (·.rowCount) == batchCounts &&
      trace.collect.table.rowCount == 9 && decide (trace.termination = .eos)
  | .error _ => false

-- Logical scans retain all nine row positions across the two distinct
-- batch partitions. Exact event readback still distinguishes the partitions.
#guard
  match writeRead expected, writeRead [expected.flatten] with
  | some split, some joined =>
    observes split expected .eos && observes joined [expected.flatten] .eos &&
      projectZero split [4, 0, 3, 2] && projectZero joined [9]
  | _, _ => false

end Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Examples
