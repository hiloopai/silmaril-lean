module

public import Silmaril.Formats.Compression.Inflate.Stream.RawSemantics
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawMachine
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.TokenContinuation
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Progress
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.StoredContinuation

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.RawSemantics`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.RawSemantics

open Silmaril.Formats.Compression

theorem format_unfold (reader : LSBReader) (output : List UInt8) :
    format reader output =
      match Blocks.header.eval reader with
      | .error err => .error err
      | .ok ((last, kind), rest) =>
        afterDecodedBlock last (Deflate.decompressBlockBody kind rest output) := by
  rw [format, Deflate.decompressBlocks_bitsLeft_unfold, Blocks.header_eval]
  cases hf : reader.readBit with
  | none => rfl
  | some pair =>
    obtain ⟨last, r1⟩ := pair
    dsimp only
    cases hk : r1.readBits 2 with
    | none => rfl
    | some pair =>
      obtain ⟨kind, r2⟩ := pair
      dsimp only
      cases hb : Deflate.decompressBlockBody kind r2 output with
      | error err => rfl
      | ok pair =>
        obtain ⟨bytes, rest⟩ := pair
        cases last <;> rfl

theorem afterToken_unfold (last : Bool) (litLen dist : HuffmanTable)
    (reader : LSBReader) (output : List UInt8) :
    afterToken last litLen dist (Deflate.decodeStep litLen dist reader output) =
      afterDecodedBlock last (Deflate.decodeSymbol litLen dist reader output) := by
  rw [Deflate.decodeSymbol_unfold]
  cases Deflate.decodeStep litLen dist reader output with
  | error err => rfl
  | ok step => cases step <;> rfl

end Silmaril.Formats.Compression.Inflate.Stream.RawSemantics
