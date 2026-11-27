module

import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Fixture
import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Fixture

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable

private def repeatByte (byte size : Nat) : KBytes :=
  .leaf size (KBytes.leVal (List.replicate size (UInt8.ofNat byte)))

private def wide : List OrderedWriter.BatchInput :=
  [⟨2, [.binary "a" true [some (repeatByte 65 13), none], .int32 "i" false [some 7, some (-2)],
    .binary "b" true [some (.leaf 5 0x74726f6873), some .empty],
    .binary "c" true [some (repeatByte 67 17), some (.leaf 1 255)]]⟩,
  ⟨2, [.binary "a" true [some (.leaf 1 97), none], .int32 "i" false [some 9, some 0],
    .binary "b" true [some (repeatByte 66 14), none], .binary "c" true [none, some .empty]]⟩,
  ⟨0, [.binary "a" true [], .int32 "i" false [], .binary "b" true [], .binary "c" true []]⟩]

private def wideFields : List MixedFlat.Field := (wide.headD ⟨0, []⟩).fields

private def zeroWidth : List OrderedWriter.BatchInput := [⟨3, []⟩, ⟨0, []⟩]

private def wideLimits : Incremental.Limits :=
  { mixed := {
      observation := { ipc := { batches := 3, rows := 2, fields := 4 }, totalRows := 4, totalCells := 16 }
      totalDataBuffers := 2 }
    totalDataBuffers := 3 }

private def zeroLimits : Incremental.Limits :=
  { mixed := {
      observation := { ipc := { batches := 2, rows := 3, fields := 0 }, totalRows := 3, totalCells := 0 }
      totalDataBuffers := 0 }
    totalDataBuffers := 0 }

private inductive Value where
  | primitive (value : Arrow.Value)
  | binary (octets : List UInt8)
  | text (value : String)
  deriving DecidableEq

private def observe : MixedFlat.Events.Cell → Value
  | .primitive value => .primitive value
  | .binaryView value => .binary value.toList
  | .utf8View value => .text value

private abbrev Rows := List (List (Option Value))

private def projected {fields : List MixedFlat.Field} (positions : List Nat)
    (event : MixedFlat.Events.Batch (MixedFlat.Events.schema fields)) : Option Rows := do
  let checked ← positions.mapM fun position =>
    if fits : position < fields.length then some (⟨position, fits⟩ : Fin fields.length) else none
  let projection : Scan.Projection (MixedFlat.Events.schema fields) := .ofArray checked.toArray
  return ((projection.projectColumns event).toRows).map fun row =>
    List.ofFn fun position => (row position).map observe

private structure Result where
  fields : Option (List MixedFlat.Field) := none
  ranges : List Stream.BatchRange := []
  rows : List Rows := []

private def pump (positions : List Nat) :
    Nat → Cursor → KBytes → Result → Except Incremental.Error (Cursor × Result)
  | 0, cursor, _, _ => .error (.expectedSchema cursor.position)
  | fuel + 1, cursor, chunk, result => do
    match ← feed cursor chunk with
    | .wait pending => return (pending, result)
    | .advance pending rest => pump positions fuel pending rest result
    | .schema fields _ pending rest => pump positions fuel pending rest { result with fields := some fields }
    | .batch _ delivered pending rest =>
      let some rows := projected positions delivered.event | throw (.expectedSchema pending.position)
      let next := { result with
        ranges := delivered.record.range :: result.ranges
        rows := rows :: result.rows }
      pump positions fuel pending rest next

private def run (limits : Incremental.Limits) (positions : List Nat) (chunks : List KBytes) :
    Except Incremental.Error (Nat × Result) := do
  let (cursor, result) ← chunks.foldlM
    (fun (cursor, result) chunk => pump positions (3 * chunk.len + 8) cursor chunk result) (start limits, {})
  let last ← finish cursor
  return (last, { result with ranges := result.ranges.reverse, rows := result.rows.reverse })

private def rangeTriple (range : Stream.BatchRange) : Nat × Nat × Nat :=
  (range.offset, range.metadataSize, range.bodyLength)

private def singleBytes (wire : KBytes) : List KBytes :=
  (List.range wire.len).map fun index => wire.slice index 1

private def uneven (wire : KBytes) (ranges : List Stream.BatchRange) : List KBytes :=
  let cuts := [0, 3, 4, 7, 8] ++ ranges.flatMap (fun range =>
    [range.offset, range.offset + 1, range.offset + 4, range.offset + 7,
     range.bodyStart - 1, range.bodyStart, min range.next (range.bodyStart + 1)]) ++
    [wire.len - 8, wire.len - 5, wire.len - 4, wire.len - 1, wire.len]
  let (pieces, last) := cuts.foldl (fun (pieces, start) stop =>
    (wire.slice start (stop - start) :: pieces, stop)) ([], 0)
  pieces.reverse ++ [wire.slice last (wire.len - last)]

private def readCounts (limits : MixedFlat.Limits) (wire : KBytes) (decoded : Stream.Observed) :
    Option (List (List Nat)) :=
  decoded.batches.mapM fun record =>
    match MixedFlat.readMetadata limits.observation.ipc limits.view.dataBuffers limits.totalDataBuffers
        decoded.fields (record.range.metadataSlice wire) with
    | .ok metadata => some metadata.counts
    | .error _ => none

private def agrees (limits : Incremental.Limits) (wire : KBytes) (fields : List MixedFlat.Field)
    (positions : List Nat) (rows : List Rows) (counts : List (List Nat)) (batches : List OrderedWriter.BatchInput)
    (pinnedRanges : Option (List (Nat × Nat × Nat)) := none) : Bool := Id.run do
  let .ok eager := Stream.read limits.mixed wire | return false
  let ranges := eager.batches.map (·.range)
  let .ok (endA, a) := run limits positions (singleBytes wire) | return false
  let .ok (endB, b) := run limits positions (uneven wire ranges) | return false
  let .ok .eos := readEnvelope limits.mixed.observation.ipc wire (wire.len - 8) | return false
  return decide (endA = wire.len ∧ endB = wire.len ∧ a.fields = some fields ∧ b.fields = a.fields ∧
    a.ranges = ranges ∧ b.ranges = a.ranges ∧ a.rows = rows ∧ b.rows = a.rows ∧
    readCounts limits.mixed wire eager = some counts ∧
    (pinnedRanges.isSome → pinnedRanges = some (ranges.map rangeTriple))) &&
    checkWriterReadback limits.mixed wire fields batches

private def expectedWide : List Rows :=
  let ascii := fun byte size => some (Value.binary (List.replicate size byte))
  let int := fun value => some (Value.primitive (.int32 value))
  [[[ascii 67 17, ascii 65 13, ascii 67 17, int 7], [ascii 255 1, none, ascii 255 1, int (-2)]],
   [[none, ascii 97 1, none, int 9], [ascii 0 0, none, ascii 0 0, int 0]], []]

private def wideCounts : List (List Nat) := [[1, 0, 1], [0, 1, 0], [0, 0, 0]]

#guard agrees wideLimits Fixture.threeViews wideFields [3, 0, 3, 1] expectedWide wideCounts wide
  (some Fixture.ranges)

#guard Id.run do
  let .ok wire := OrderedWriter.emit wideLimits.mixed wideFields wide | return false
  return agrees wideLimits wire wideFields [3, 0, 3, 1] expectedWide wideCounts wide

#guard agrees zeroLimits MixedFlat.Stream.Fixture.zeroColumns [] [] [[[], [], []], []] [[], []] zeroWidth
  (some [(56, 72, 0), (136, 64, 0)])

#guard Id.run do
  let .ok wire := OrderedWriter.emit zeroLimits.mixed [] zeroWidth | return false
  return agrees zeroLimits wire [] [] [[[], [], []], []] [[], []] zeroWidth

#guard Id.run do
  let .ok wire := OrderedWriter.emit wideLimits.mixed wideFields wide | return false
  let .ok eager := Stream.read wideLimits.mixed wire | return false
  let .error (.batch 1 offset .dataBufferLimit) :=
    run { wideLimits with totalDataBuffers := 2 } [3, 0, 3, 1] (singleBytes wire) | return false
  return eager.batches[1]?.any (fun record => offset == record.range.offset)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable
