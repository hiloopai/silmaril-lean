module

public import Silmaril.Formats.Compression.Deflate.WithHistory
public import Silmaril.Raw.Formats.Compression.Deflate.Stored

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Deflate.WithHistory`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

/-- Aligning away final-byte padding preserves this byte-list observation. -/
theorem resultWithHistory_align (history : List UInt8)
    (result : Except DecompressError (List UInt8 × LSBReader)) :
    resultWithHistory history (result.map fun pair => (pair.1, pair.2.alignToByte)) =
      resultWithHistory history result := by
  cases result with
  | error error => rfl
  | ok pair => cases pair; rfl

theorem resultWithHistory_error (history : List UInt8) (error : DecompressError) :
    resultWithHistory history (.error error) = .error error := rfl

theorem resultWithHistory_ok (history output : List UInt8) (reader : LSBReader) :
    resultWithHistory history (.ok (output, reader)) =
      .ok (output.drop history.length, reader.input) := rfl

/-- Once the decoder has preserved its seeded prefix, the observed output is
exactly the newly appended data. -/
theorem resultWithHistory_append (history data : List UInt8) (reader : LSBReader) :
    resultWithHistory history (.ok (history ++ data, reader)) = .ok (data, reader.input) := by
  simp only [resultWithHistory, Except.map, List.drop_left]

/-- The dictionary-free shared specification is the empty-history instance. -/
theorem deflateTakeWithHistory_empty (input : List UInt8) :
    deflateTakeWithHistory [] input = deflateTake input := by
  dsimp only [deflateTakeWithHistory, deflateTake, resultWithHistory]
  cases decompressBlocks ((LSBReader.mk 0 0 input 0).bitsLeft + 1)
      (LSBReader.mk 0 0 input 0) [] with
  | error error => rfl
  | ok pair => cases pair; rfl

/-- Expose the exact canonical-reader execution behind a successful seeded
byte-list result. No claim of output-prefix preservation is assumed here. -/
theorem deflateTakeWithHistory_eq_ok_iff (history input data tail : List UInt8) :
    deflateTakeWithHistory history input = .ok (data, tail) ↔
      ∃ output reader,
        decompressBlocks ((LSBReader.mk 0 0 input 0).bitsLeft + 1)
          (LSBReader.mk 0 0 input 0) history = .ok (output, reader) ∧
        output.drop history.length = data ∧ reader.input = tail := by
  dsimp only [deflateTakeWithHistory]
  cases hdecode : decompressBlocks ((LSBReader.mk 0 0 input 0).bitsLeft + 1)
      (LSBReader.mk 0 0 input 0) history with
  | error error => simp [resultWithHistory, Except.map]
  | ok pair =>
    obtain ⟨output, reader⟩ := pair
    simp only [resultWithHistory, Except.map, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨output, reader, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨otherOutput, otherReader, ⟨rfl, rfl⟩, h⟩
      exact h

/-- Initial history changes output interpretation, not the fact that decoding
consumes an input prefix and leaves a genuine input suffix untouched. -/
theorem deflateTakeWithHistory_suffix {history input data tail : List UInt8}
    (h : deflateTakeWithHistory history input = .ok (data, tail)) : tail <:+ input := by
  obtain ⟨output, reader, hdecode, _, htail⟩ :=
    (deflateTakeWithHistory_eq_ok_iff history input data tail).mp h
  rw [← htail]
  exact decompressBlocks_suffix hdecode

/-- Stored streams append their payload after any initial history. The history
is omitted from the observation, and an arbitrary following suffix survives. -/
theorem deflateTakeWithHistory_storedBytes (history data tail : List UInt8) :
    deflateTakeWithHistory history (storedBytes data ++ tail) = .ok (data, tail) := by
  have hfuel : data.length + 1 ≤
      (LSBReader.bitsLeft ⟨0, 0, storedBytes data ++ tail, 0⟩) + 1 := by
    have := storedBytes_length_le data
    simp only [LSBReader.bitsLeft, List.length_append]
    omega
  obtain ⟨total, hdecode⟩ := decompressBlocks_storedBytes _ data tail history 0 hfuel
  dsimp only [deflateTakeWithHistory]
  rw [hdecode]
  exact resultWithHistory_append history data ⟨0, 0, tail, total⟩

/-- A nonempty seed is not exposed as emitted data, even with a following
container suffix. This also checks a concrete successful decoder execution. -/
theorem seeded_stored_byte_checked :
    deflateTakeWithHistory [65, 66] [1, 1, 0, 254, 255, 67, 85, 102] =
      .ok ([67], [85, 102]) := rfl

set_option maxRecDepth 16384 in
/-- Python's zlib, with dictionary `AB`, encoded `ABABAB` as these four raw
bytes. A distance-two match uses dictionary history and then overlaps newly
emitted output. The following bytes remain untouched. -/
theorem seeded_fixed_match_checked :
    deflateTakeWithHistory [65, 66] [115, 4, 67, 0, 85, 102] =
      .ok ([65, 66, 65, 66, 65, 66], [85, 102]) := rfl

set_option maxRecDepth 16384 in
/-- The same bytes fail without the dictionary: the match's distance is not
available after the first literal. This witnesses actual history dependence. -/
theorem unseeded_fixed_match_rejected :
    deflateTakeWithHistory [] [115, 4, 67, 0, 85, 102] = .error .decodeOverrun := rfl

end Silmaril.Formats.Compression.Deflate
