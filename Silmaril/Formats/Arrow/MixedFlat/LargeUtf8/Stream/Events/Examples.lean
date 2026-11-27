module

import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events.Defs
import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Fixture
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events

open Silmaril.Relational
open MixedFlat.LargeUtf8.Events

private inductive Slot where
  | primitive (value : Arrow.Value)
  | binaryView (bytes : List UInt8)
  | utf8View (text : String)
  | largeUtf8 (text : String)
  deriving DecidableEq

private def observeCell : (kind : Kind) → Cell kind → Slot
  | .existing _, .primitive value => .primitive value
  | .existing _, .binaryView bytes => .binaryView bytes.toList
  | .existing _, .utf8View text => .utf8View text
  | .largeUtf8, text => .largeUtf8 text

private def ints (values : List (Option Int32)) : List (Option Slot) :=
  values.map (Option.map (Slot.primitive ∘ Value.int32))

private def texts (values : List (Option String)) : List (Option Slot) :=
  values.map (Option.map Slot.largeUtf8)

private def number (nullable : Bool) : Field := ⟨"number", nullable, .existing (.primitive .int32)⟩
private def text (nullable : Bool) : Field := ⟨"text", nullable, .largeUtf8⟩

private def wideText : String := ("é".push (Char.ofNat 0)) ++ "🙂"

private def intFirst : List (List (List (Option Slot))) :=
  [[ints [some (-7), some 0, some 9, some 2147483647], texts [some "雪", none, some "", some wideText]],
   [[], []],
   [ints [some (-2147483648), some 12, some 6], texts [some "", some "β", none]]]

private def textFirst : List (List (List (Option Slot))) :=
  [[texts [some "雪", some "", some wideText, some "x"], ints [none, some (-7), some 0, some 9]],
   [[], []],
   [texts [some "", some "β", some "z"], ints [none, some (-2147483648), some 6]]]

private def observes (source : EventStream) (fields : List Field) (rows : List Nat)
    (values : List (List (List (Option Slot)))) (terminal : Arrow.Events.Termination Error) : Bool :=
  match source with
  | .error _ => false
  | .ok ⟨signature, trace⟩ =>
    decide (List.ofFn signature.kind = fields.map (fun field => (field, field.kind))) &&
      trace.batches.map (·.rowCount) == rows &&
      decide (trace.batches.map (fun batch =>
        List.ofFn (fun i => (batch.values i).map (Option.map (observeCell (signature.kind i).2)))) = values) &&
      decide (trace.termination = terminal)

private def intInputs : List (Framing × KBytes) :=
  [(.modern, Fixture.intFirstModern), (.legacy, Fixture.intFirstLegacy)]

private def textInputs : List (Framing × KBytes) :=
  [(.modern, Fixture.textFirstModern), (.legacy, Fixture.textFirstLegacy)]

#guard intInputs.all fun (framing, input) =>
  observes (readAll {} framing input) [number false, text true] [4, 0, 3] intFirst .eos

#guard textInputs.all fun (framing, input) =>
  observes (readAll {} framing input) [text false, number true] [4, 0, 3] textFirst .eos

private def view (name : String) : Field := ⟨name, true, .existing (.view .binary)⟩

#guard observes (readAll {} .modern Fixture.withViews) [view "inline", text true, number false, view "external"]
  [4, 0]
  [[ [none, some (.binaryView []), some (.binaryView [97]), some (.binaryView [255])],
     texts [some "雪", none, some "", some wideText],
     ints [some (-7), some 0, some 9, some 2147483647],
     [some (.binaryView "0123456789abcdef".toByteArray.data.toList), none,
      some (.binaryView []), some (.binaryView [120])] ],
   [[], [], [], []]] .eos

private def widthZero (source : Signature) : Scan.Projection source := .ofArray #[]

private def reordered (source : Signature) : Scan.Projection source :=
  if second : 1 < source.width then
    let first : Fin source.width := ⟨0, Nat.lt_trans Nat.zero_lt_one second⟩
    .ofArray #[⟨1, second⟩, first, ⟨1, second⟩]
  else widthZero source

private def selectRepeated (columns : List (List (Option Slot))) : List (List (Option Slot)) :=
  [columns[1]?.getD [], columns[0]?.getD [], columns[1]?.getD []]

#guard intInputs.all fun (framing, input) =>
  observes (readProjected {} framing input reordered) [text true, number false, text true] [4, 0, 3]
    (intFirst.map selectRepeated) .eos

#guard textInputs.all fun (framing, input) =>
  observes (readProjected {} framing input reordered) [number true, text false, number true] [4, 0, 3]
    (textFirst.map selectRepeated) .eos

#guard intInputs.all fun (framing, input) =>
  observes (readProjected {} framing input widthZero) [] [4, 0, 3] [[], [], []] .eos

-- Genuine PyArrow zero-column input from the pre-existing mixed fixture.
#guard observes (readAll {} .modern MixedFlat.Stream.Fixture.zeroColumns) [] [3, 0] [[], []] .eos
#guard observes (readProjected {} .modern MixedFlat.Stream.Fixture.zeroColumns widthZero)
  [] [3, 0] [[], []] .eos

private def schemaOnly (framing : Framing) (input : KBytes) :=
  let size := match framing with
    | .modern => Fixture.intFirstModernSchemaSize
    | .legacy => Fixture.intFirstLegacySchemaSize
  input.slice 0 (framing.prefixSize + size) ++ input.slice (input.len - framing.prefixSize) framing.prefixSize

#guard intInputs.all fun (framing, input) =>
  observes (readAll { observation := { ipc := { batches := 0 } } } framing (schemaOnly framing input))
    [number false, text true] [] [] .eos

-- Synthetic corruption of the first data octet in the third text column
-- frame. Keep the two completed batches, including the explicit empty one.
private def late (framing : Framing) (input : KBytes) : Bool := Id.run do
  let (ranges, buffers) := match framing with
    | .modern => (Fixture.intFirstModernRanges, Fixture.intFirstModernBuffers)
    | .legacy => (Fixture.intFirstLegacyRanges, Fixture.intFirstLegacyBuffers)
  let some (offset, size, _) := ranges[2]? | return false
  let some descriptors := buffers[2]? | return false
  let some (data, _) := descriptors[4]? | return false
  let pos := offset + framing.prefixSize + size + data
  let damaged := input.slice 0 pos ++ KBytes.leaf 1 255 ++ input.slice (pos + 1) (input.len - pos - 1)
  let error : Error := .record 2 offset (.decode (.field 1 (.largeUtf8 (.invalidUtf8 1))))
  return observes (readAll {} framing damaged) [number false, text true] [4, 0]
      (intFirst.take 2) (.readError error) &&
    observes (readProjected {} framing damaged reordered) [text true, number false, text true] [4, 0]
      ((intFirst.take 2).map selectRepeated) (.readError error) &&
    observes (readProjected {} framing damaged widthZero) [] [4, 0] [[], []] (.readError error)

#guard intInputs.all fun (framing, input) => late framing input

#guard intInputs.all fun (framing, input) =>
  let terminal : Error := .record 3 (input.len - framing.prefixSize) .trailingBytes
  observes (readProjected {} framing (input ++ KBytes.leaf 1 0) widthZero)
    [] [4, 0, 3] [[], [], []] (.readError terminal)

#guard intInputs.all fun (framing, input) =>
  observes ((reader {} framing).read 2 input) [number false, text true] [4, 0]
    (intFirst.take 2) .closed

#guard match readProjected {} .modern Fixture.intFirstLegacy widthZero with
  | .error (.schema (.envelope (.unsupported .legacyFraming))) => true
  | _ => false

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events
