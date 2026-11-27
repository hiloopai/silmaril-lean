module

import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Defs
import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream

private inductive Slots where
  | primitive (values : Arrow.Column)
  | text (values : Arrow.LargeUtf8.Column)
  | binaryView (values : List (Option (List UInt8)))
  deriving DecidableEq

private def observeColumn : Column → Option Slots
  | .existing (.primitive values) => some (.primitive values)
  | .existing (.binaryView values) => some (.binaryView (values.map (Option.map KBytes.toList)))
  | .largeUtf8 values => some (.text values)
  | .existing (.utf8View _) => none

private def ints (values : List (Option Int32)) : Slots :=
  .primitive (values.map (Option.map Value.int32))

private def number (nullable : Bool) : Field := ⟨"number", nullable, .existing (.primitive .int32)⟩
private def text (nullable : Bool) : Field := ⟨"text", nullable, .largeUtf8⟩
private def inlineView : Field := ⟨"inline", true, .existing (.view .binary)⟩
private def externalView : Field := ⟨"external", true, .existing (.view .binary)⟩

private def wideText : String := ("é".push (Char.ofNat 0)) ++ "🙂"

private def expectedIntFirst : List (List Slots) :=
  [[ints [some (-7), some 0, some 9, some 2147483647], .text [some "雪", none, some "", some wideText]],
   [ints [], .text []],
   [ints [some (-2147483648), some 12, some 6], .text [some "", some "β", none]]]

private def expectedTextFirst : List (List Slots) :=
  [[.text [some "雪", some "", some wideText, some "x"], ints [none, some (-7), some 0, some 9]],
   [.text [], ints []],
   [.text [some "", some "β", some "z"], ints [none, some (-2147483648), some 6]]]

private def expectedViews : List (List Slots) :=
  [[.binaryView [none, some [], some [97], some [255]], .text [some "雪", none, some "", some wideText],
    ints [some (-7), some 0, some 9, some 2147483647],
    .binaryView [some ("0123456789abcdef".toByteArray.data.toList), none, some [], some [120]]],
   [.binaryView [], .text [], ints [], .binaryView []]]

private structure FixtureCase where
  framing : Framing
  wire : KBytes
  schemaSize : Nat
  ranges : List (Nat × Nat × Nat)
  buffers : List (List (Nat × Nat))
  eos : Nat

private def intCases : List FixtureCase :=
  [⟨.modern, Fixture.intFirstModern, Fixture.intFirstModernSchemaSize, Fixture.intFirstModernRanges,
    Fixture.intFirstModernBuffers, Fixture.intFirstModernEos⟩,
   ⟨.legacy, Fixture.intFirstLegacy, Fixture.intFirstLegacySchemaSize, Fixture.intFirstLegacyRanges,
    Fixture.intFirstLegacyBuffers, Fixture.intFirstLegacyEos⟩]

private def textCases : List FixtureCase :=
  [⟨.modern, Fixture.textFirstModern, Fixture.textFirstModernSchemaSize, Fixture.textFirstModernRanges,
    Fixture.textFirstModernBuffers, Fixture.textFirstModernEos⟩,
   ⟨.legacy, Fixture.textFirstLegacy, Fixture.textFirstLegacySchemaSize, Fixture.textFirstLegacyRanges,
    Fixture.textFirstLegacyBuffers, Fixture.textFirstLegacyEos⟩]

private def viewCase : FixtureCase :=
  ⟨.modern, Fixture.withViews, Fixture.withViewsSchemaSize, Fixture.withViewsRanges,
    Fixture.withViewsBuffers, Fixture.withViewsEos⟩

private def observes (fields : List Field) (batches : List Batch) (rows : List Nat)
    (ranges : List (Nat × Nat × Nat)) (expected : List (List Slots)) : Bool :=
  batches.map (·.observed.rowCount) == rows &&
    batches.map (fun batch => (batch.range.offset, batch.range.metadataSize, batch.range.bodyLength)) == ranges &&
    decide (batches.map (fun batch => batch.observed.columns.map Prod.fst) = batches.map (fun _ => fields)) &&
    decide (batches.map (fun batch => batch.observed.columns.map (observeColumn ∘ Prod.snd)) =
      expected.map (List.map some))

private def checkFrame (fixture : FixtureCase) (fields : List Field) (batch : Batch)
    (buffers : List (Nat × Nat)) (counts : List Nat) (widths : List Nat) : Bool := Id.run do
  let recordBytes := fixture.wire.slice batch.range.metadataStart batch.range.metadataSize
  let body := fixture.wire.slice batch.range.bodyStart batch.range.bodyLength
  let .ok metadata := LargeUtf8.readMetadata {} fields recordBytes | return false
  let .ok plan := MixedFlat.bindBatch {} (fields.map Field.layout) metadata body | return false
  let sizes := plan.assignment.groups.map (·.buffers.length)
  let .ok standalone := readBatch {} (fixture.wire.slice fixture.framing.prefixSize fixture.schemaSize)
    recordBytes body | return false
  return decide (standalone.columns.map Prod.fst = fields) &&
    decide (standalone.columns.map (observeColumn ∘ Prod.snd) = batch.observed.columns.map (observeColumn ∘ Prod.snd)) &&
    metadata.batch.buffers.map (fun buffer => (buffer.offset, buffer.length)) == buffers &&
    metadata.batch.nodes.map (·.length) == fields.map (fun _ => standalone.rowCount) &&
    metadata.counts == counts && sizes == widths

private def checks (fixture : FixtureCase) (limits : MixedFlat.Limits) (fields : List Field)
    (rows : List Nat) (expected : List (List Slots)) (counts widths : List (List Nat)) : Bool :=
  match read limits fixture.framing fixture.wire with
  | .ok observed =>
    decide (observed.fields = fields ∧ observed.trace.termination = .eos fixture.eos) &&
      observes fields observed.trace.batches rows fixture.ranges expected &&
      (observed.trace.batches.zip (fixture.buffers.zip (counts.zip widths))).all
        (fun (batch, buffers, count, width) => checkFrame fixture fields batch buffers count width)
  | .error _ => false

private def exactLimits : MixedFlat.Limits :=
  { observation := {
      ipc := { batches := 3, rows := 4, fields := 2, bodyBytes := 80 }
      totalRows := 7
      totalCells := 14 } }

#guard intCases.all fun fixture =>
  checks fixture exactLimits [number false, text true] [4, 0, 3] expectedIntFirst
    [[], [], []] (List.replicate 3 [2, 3])

#guard textCases.all fun fixture =>
  checks fixture exactLimits [text false, number true] [4, 0, 3] expectedTextFirst
    [[], [], []] (List.replicate 3 [3, 2])

#guard checks viewCase { totalDataBuffers := 1, view := { dataBuffers := 1 } }
    [inlineView, text true, number false, externalView] [4, 0] expectedViews [[0, 1], [0, 0]]
    [[2, 3, 2, 3], [2, 3, 2, 2]]

private def stopped (limits : MixedFlat.Limits) (fixture : FixtureCase) (wire : KBytes)
    (fields : List Field) (expected : List (List Slots)) (prior : List Nat) (terminal : Termination) : Bool :=
  match read limits fixture.framing wire with
  | .ok result =>
    decide (result.fields = fields ∧ result.trace.termination = terminal) &&
      observes fields result.trace.batches prior (fixture.ranges.take prior.length) (expected.take prior.length)
  | .error _ => false

-- Synthetic control on the third original frame. A completed empty record
-- stays in the prefix, and the terminal error identifies the selected slot.
private def late (fixture : FixtureCase) (textFirst : Bool) : Bool := Id.run do
  let some (offset, metadataSize, _) := fixture.ranges[2]? | return false
  let some buffers := fixture.buffers[2]? | return false
  let some (data, length) := buffers[if textFirst then 2 else 4]? | return false
  if length = 0 then return false
  let atByte := offset + fixture.framing.prefixSize + metadataSize + data
  let damaged := fixture.wire.slice 0 atByte ++ KBytes.leaf 1 255 ++
    fixture.wire.slice (atByte + 1) (fixture.wire.len - atByte - 1)
  let fields := if textFirst then [text false, number true] else [number false, text true]
  let expected := if textFirst then expectedTextFirst else expectedIntFirst
  let index := if textFirst then 0 else 1
  return stopped {} fixture damaged fields expected [4, 0]
    (.error 2 offset (.decode (.field index (.largeUtf8 (.invalidUtf8 1)))))

#guard intCases.all fun fixture => late fixture false
#guard textCases.all fun fixture => late fixture true

-- Synthetic control: the final word still constrains a null text slot.
#guard intCases.all fun fixture => Id.run do
  let some (offset, size, _) := fixture.ranges[2]? | return false
  let some buffers := fixture.buffers[2]? | return false
  let some (offsets, 32) := buffers[3]? | return false
  let word := offset + fixture.framing.prefixSize + size + offsets + 24
  let damaged := fixture.wire.slice 0 word ++ KBytes.leaf 8 (2^63) ++
    fixture.wire.slice (word + 8) (fixture.wire.len - word - 8)
  return stopped {} fixture damaged [number false, text true] expectedIntFirst [4, 0]
    (.error 2 offset (.decode (.field 1 (.largeUtf8 (.binary (.offsetNegative 3 (2^63)))))))

-- Assemble a required-column node with a declared null on the original body.
#guard textCases.all fun fixture => Id.run do
  let fields := [text false, number true]
  let some (offset, size, bodyLength) := fixture.ranges[2]? | return false
  let start := offset + fixture.framing.prefixSize
  let .ok metadata := LargeUtf8.readMetadata {} fields (fixture.wire.slice start size) | return false
  let node :: rest := metadata.batch.nodes | return false
  let malformed := { metadata with batch := { metadata.batch with nodes := { node with nullCount := 1 } :: rest } }
  let body := fixture.wire.slice (start + size) bodyLength
  return match readParsed {} fields malformed body with
  | .error (.binding (.plan (.field 0 .invalidNode))) => true
  | _ => false

private def firstInt := intCases[0]

#guard intCases.all fun fixture =>
  let schemaEnd := fixture.framing.prefixSize + fixture.schemaSize
  let marker := fixture.wire.slice fixture.eos fixture.framing.prefixSize
  stopped { observation := { ipc := { batches := 0 } } } fixture
    (fixture.wire.slice 0 schemaEnd ++ marker) [number false, text true] expectedIntFirst [] (.eos schemaEnd)

#guard intCases.all fun fixture =>
  stopped {} fixture (fixture.wire ++ KBytes.leaf 1 0)
    [number false, text true] expectedIntFirst [4, 0, 3] (.error 3 fixture.eos .trailingBytes)

#guard stopped { observation := { totalRows := 6 } } firstInt firstInt.wire
  [number false, text true] expectedIntFirst [4, 0] (.error 2 696 (.budget (.limit .totalRows)))

#guard stopped { observation := { totalCells := 13 } } firstInt firstInt.wire
  [number false, text true] expectedIntFirst [4, 0] (.error 2 696 (.budget (.limit .totalCells)))

#guard stopped { observation := { ipc := { batches := 2 } } } firstInt firstInt.wire
  [number false, text true] expectedIntFirst [4, 0] (.error 2 696 .batchLimit)

#guard stopped { view := { dataBuffers := 0 } } viewCase viewCase.wire
  [inlineView, text true, number false, externalView] expectedViews [] (.error 0 288 (.metadata (.dataBufferLimit 1)))

#guard stopped { totalDataBuffers := 0 } viewCase viewCase.wire
  [inlineView, text true, number false, externalView] expectedViews [] (.error 0 288 (.metadata .totalDataBufferLimit))

-- The old mixed schema admission still rejects tag 20.
#guard match MixedFlat.readSchema {} (Fixture.intFirstModern.slice 8 Fixture.intFirstModernSchemaSize) with
  | .error (.unsupported (.fieldType 20)) => true
  | _ => false

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream
