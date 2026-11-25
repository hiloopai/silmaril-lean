module

public import Silmaril.Machine.DecodeGraph.Decoder.Defs
public import Silmaril.Machine.DecodeGraph.Thms

public section

namespace Silmaril.Machine.DecodeGraph.Proofs

open Silmaril.Parse.DecodeGraph

variable {Context Source : Type*}

private theorem window_length (bytes : List UInt8) (pos stop : Nat) :
    (decoderWindow bytes pos stop).length = min (stop - pos) (bytes.length - pos) := by
  simp only [decoderWindow, List.extract_eq_take_drop, List.length_map, List.length_take, List.length_drop]

private theorem window_shorten (bytes : List UInt8) {pos stop endPos : Nat} (inside : endPos ≤ stop) :
    decoderWindow bytes pos endPos = (decoderWindow bytes pos stop).take (endPos - pos) := by
  simp only [decoderWindow, List.extract_eq_take_drop, List.map_take, List.take_take]
  rw [Nat.min_eq_left (by omega : endPos - pos ≤ stop - pos)]

private theorem window_after (bytes : List UInt8) {pos nextPos endPos : Nat} (advance : pos ≤ nextPos) :
    (decoderWindow bytes pos endPos).drop (nextPos - pos) = decoderWindow bytes nextPos endPos := by
  simp only [decoderWindow, List.extract_eq_take_drop, List.map_take, List.drop_take, ← List.map_drop, List.drop_drop]
  rw [show pos + (nextPos - pos) = nextPos by omega, show endPos - pos - (nextPos - pos) = endPos - nextPos by omega]

theorem ofDecoder_deterministic (decoder : Decoder Source) :
    Deterministic (ofDecoder (Context := Context) decoder) := by
  rintro input ⟨left, leftEnd⟩ ⟨right, rightEnd⟩ ⟨_, leftWidth, hl, rfl⟩ ⟨_, rightWidth, hr, rfl⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hl.symm.trans hr))
  rfl

theorem ofDecoder_exact (decoder : Decoder Source) : ofDecoder (Context := Context) decoder =
    ofGrammar (fun _ span value => decoder.decode (span.map UInt8.toBitVec) = some (value, span.length)) := by
  ext ⟨input, value, endPos⟩
  constructor
  · rintro ⟨valid, width, decoded, rfl⟩
    have pos := decoder.decode_length_pos decoded
    have fits := decoder.decode_length_le decoded
    rw [window_length] at fits
    have inside : input.pos + width ≤ input.stop := by omega
    refine ⟨by omega, inside, valid, ?_⟩
    change decoder.decode (decoderWindow input.bytes input.pos (input.pos + width)) =
      some (value, (input.bytes.extract input.pos (input.pos + width)).length)
    have length : (input.bytes.extract input.pos (input.pos + width)).length = width := by
      rw [← List.length_map (f := UInt8.toBitVec), ← decoderWindow, window_length]
      omega
    rw [length, window_shorten _ inside, Nat.add_sub_cancel_left]
    exact decoder.decode_take decoded
  · rintro ⟨advance, inside, valid, decoded⟩
    refine ⟨valid, endPos - input.pos, ?_, by omega⟩
    have length : (input.bytes.extract input.pos endPos).length = endPos - input.pos := by
      rw [← List.length_map (f := UInt8.toBitVec), ← decoderWindow, window_length]
      omega
    apply decoder.decode_eq_some_iff_take.mpr
    refine ⟨?_, ?_⟩
    · rw [window_length]; omega
    · change decoder.decode (decoderWindow input.bytes input.pos endPos) = _ at decoded
      rw [length, window_shorten _ inside] at decoded
      exact decoded

private theorem sequential_step (decoder : Decoder Source) {fuel pos : Nat} {bytes : List (BitVec 8)}
    {instr : Source} {width : Nat} (decoded : decoder.decode bytes = some (instr, width)) :
    decoder.decodeBlock (fuel + 1) pos bytes =
      (decoder.decodeBlock fuel (pos + width) (bytes.drop width)).map ((pos, instr) :: ·) := by
  cases bytes with
  | nil => exact (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le (decoder.decode_length_pos decoded)
      (decoder.decode_length_le decoded))).elim
  | cons byte rest => simp [Decoder.decodeBlock, decoded]

theorem blocks_subset_sequentialPrefixes (decoder : Decoder Source) (ends : Context → Nat → Source → Prop)
    (fuel : Nat) : blocks (ofDecoder decoder) ends fuel ⊆ sequentialPrefixes decoder fuel := by
  rintro ⟨input, code, endPos⟩ (path : Path (ofDecoder decoder) ends fuel input code endPos)
  induction path with
  | @last fuel input instr endPos decoded advance inside _ =>
    obtain ⟨valid, width, head, rfl⟩ := decoded
    refine ⟨by omega, inside, valid, ?_⟩
    rw [window_shorten _ inside, Nat.add_sub_cancel_left, sequential_step decoder (decoder.decode_take head),
      List.drop_take_self, Decoder.decodeBlock_nil]
    rfl
  | @next fuel input instr nextPos rest endPos decoded advance _ _ _ ih =>
    obtain ⟨valid, width, head, rfl⟩ := decoded
    obtain ⟨nextBound, endBound, _, scan⟩ := ih
    simp only [Input.atPos] at nextBound endBound scan
    have widthBound := decoder.decode_length_le head
    rw [window_length] at widthBound
    have headPrefix : decoder.decode (decoderWindow input.bytes input.pos endPos) = some (instr, width) := by
      apply decoder.decode_eq_some_iff_take.mpr
      refine ⟨by rw [window_length]; omega, ?_⟩
      rw [window_shorten _ endBound, List.take_take, Nat.min_eq_left (by omega : width ≤ endPos - input.pos)]
      exact decoder.decode_take head
    refine ⟨by omega, endBound, valid, ?_⟩
    rw [sequential_step decoder headPrefix, ← Nat.add_sub_cancel_left input.pos width,
      window_after _ (by omega : input.pos ≤ input.pos + width)]
    rw [Nat.add_sub_cancel_left]
    obtain ⟨entries, scanned, listing⟩ := Option.map_eq_some_iff.mp scan
    rw [scanned]
    exact congrArg (fun tail => some (instr :: tail)) listing

end Silmaril.Machine.DecodeGraph.Proofs
