module

public import Silmaril.Formats.Compression.Inflate.Stream.ReaderOffset
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawRuns

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.ReaderOffset`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.ReaderOffset

open Silmaril.Formats.Compression

theorem readBit_shift (offset : Nat) (reader : LSBReader) :
    (shift offset reader).readBit =
      reader.readBit.map (fun pair => (pair.1, shift offset pair.2)) := by
  obtain ⟨buffer, count, input, total⟩ := reader
  cases count with
  | zero =>
    cases input with
    | nil => rfl
    | cons byte rest =>
      simp [shift, LSBReader.readBit, LSBReader.refill, Nat.add_right_comm]
      rfl
  | succ count =>
    simp [shift, LSBReader.readBit, Nat.add_right_comm]
    rfl

theorem readBits_shift (offset count : Nat) (reader : LSBReader) :
    (shift offset reader).readBits count =
      (reader.readBits count).map (fun pair => (pair.1, shift offset pair.2)) := by
  induction count generalizing reader with
  | zero => rfl
  | succ count ih =>
    simp only [LSBReader.readBits, readBit_shift]
    cases reader.readBit with
    | none => rfl
    | some pair =>
      obtain ⟨bit, middle⟩ := pair
      simp only [Option.map_some, ih]
      cases middle.readBits count <;> rfl

theorem align_shift (offset : Nat) (reader : LSBReader) :
    (shift offset reader).alignToByte = shift offset reader.alignToByte := by
  simp only [shift, LSBReader.alignToByte, Nat.add_right_comm]

theorem eval_shift {α : Type} (parser : Parser α) (offset : Nat) (reader : LSBReader) :
    parser.eval (shift offset reader) =
      (parser.eval reader).map (fun pair => (pair.1, shift offset pair.2)) := by
  induction parser generalizing reader with
  | pure value => rfl
  | fail err => rfl
  | bits count err next ih =>
    simp only [Parser.eval, readBits_shift]
    cases reader.readBits count with
    | none => rfl
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      exact ih value rest
  | align next ih =>
    simpa only [Parser.eval, align_shift] using ih reader.alignToByte

theorem blocks_shift (offset fuel : Nat) (reader : LSBReader) (output : List UInt8) :
    Deflate.decompressBlocks fuel (shift offset reader) output =
      (Deflate.decompressBlocks fuel reader output).map
        (fun pair => (pair.1, shift offset pair.2)) := by
  have equality := eval_shift (Blocks.blocks (Blocks.body131 (reader.bitsLeft + 1)) fuel output)
    offset reader
  rw [Blocks.blocks131_eval _ _ _ _ (by exact Nat.le_refl _),
    Blocks.blocks131_eval _ _ _ _ (Nat.le_refl _)] at equality
  exact equality

theorem format_shift (offset : Nat) (reader : LSBReader) (output : List UInt8) :
    RawSemantics.format (shift offset reader) output =
      (RawSemantics.format reader output).map (fun pair => (pair.1, shift offset pair.2)) := by
  simp only [RawSemantics.format]
  change RawSemantics.alignResult
      (Deflate.decompressBlocks (reader.bitsLeft + 1) (shift offset reader) output) = _
  rw [blocks_shift]
  cases Deflate.decompressBlocks (reader.bitsLeft + 1) reader output with
  | error err => rfl
  | ok pair =>
    obtain ⟨bytes, rest⟩ := pair
    simp only [RawSemantics.alignResult, Except.map, align_shift]

theorem format_aligned_inputView (input : List UInt8) (total : Nat) :
    Blocks.inputView (RawSemantics.format ⟨0, 0, input, total⟩ []) =
      Deflate.deflateTake input := by
  have shifted := congrArg Blocks.inputView (format_shift total (Blocks.initialReader input) [])
  have observed : Blocks.inputView
      ((RawSemantics.format (Blocks.initialReader input) []).map
        (fun pair => (pair.1, shift total pair.2))) =
      Blocks.inputView (RawSemantics.format (Blocks.initialReader input) []) := by
    cases RawSemantics.format (Blocks.initialReader input) [] <;> rfl
  simpa only [shift, Blocks.initialReader, Nat.zero_add] using
    shifted.trans (observed.trans (RawRuns.format_inputView input))

end Silmaril.Formats.Compression.Inflate.Stream.ReaderOffset
