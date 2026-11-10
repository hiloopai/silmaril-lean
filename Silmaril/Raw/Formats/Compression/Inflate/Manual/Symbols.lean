module

public import Silmaril.Formats.Compression.Inflate.Manual.Symbols
public import Silmaril.Raw.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Raw.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Raw.Formats.Compression.Deflate.Stored
public import Silmaril.Raw.Formats.Compression.Deflate.WithHistory
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Raw.Formats.Compression.Deflate.LZ77
public import Silmaril.Raw.Formats.Compression.Bits.ByteFields
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32
public import Silmaril.Raw.Formats.Compression.Checksum.CRC32
public import Silmaril.Raw.Formats.Compression.Zlib.Basic
public import Silmaril.Raw.Formats.Compression.Zlib.Take
public import Silmaril.Raw.Formats.Compression.Zlib.Dictionary
public import Silmaril.Raw.Formats.Compression.Gzip.Basic

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Manual.Symbols`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual

open Silmaril.Formats.Compression

/-- Factoring parsing and token application preserves the exact error, reader
and output behavior of the existing symbol specification. -/
theorem decodeStep_eq_spec (litLen dist : HuffmanTable) (r : LSBReader)
    (output : List UInt8) :
    decodeStep litLen dist r output = Deflate.decodeStep litLen dist r output := by
  unfold decodeStep parseToken Deflate.decodeStep
  cases hs : litLen.readSymbolLSB r with
  | none => rfl
  | some pair =>
    rcases pair with ⟨symbol, r1⟩
    by_cases hlit : symbol < 256
    · simp only [hlit, ite_true, applyToken]
    · simp only [hlit, ite_false]
      by_cases hend : symbol = 256
      · simp only [hend, ite_true, applyToken]
      · simp only [hend, ite_false]
        by_cases hlength : symbol ≤ 285
        · simp only [hlength, ite_true]
          unfold parseMatch
          cases he : r1.readBits (Deflate.lengthExtraBits.getD (symbol - 257) 0) with
          | none => simp only [he]
          | some pair =>
            rcases pair with ⟨lengthExtra, r2⟩
            simp only [he]
            cases hd : dist.readSymbolLSB r2 with
            | none => rfl
            | some pair =>
              rcases pair with ⟨distanceSymbol, r3⟩
              by_cases hreserved : 30 ≤ distanceSymbol
              · simp only [hreserved, ite_true]
              · simp only [hreserved, ite_false]
                cases hv : r3.readBits (Deflate.distanceExtraBits.getD distanceSymbol 0) with
                | none => rfl
                | some pair =>
                  rcases pair with ⟨distanceExtra, r4⟩
                  rfl
        · simp only [hlength, ite_false]

/-- Exact correspondence for every fuel, including insufficient fuel. -/
theorem decodeSymbolsFuel_eq_spec (litLen dist : HuffmanTable) (fuel : Nat)
    (r : LSBReader) (output : List UInt8) :
    decodeSymbolsFuel litLen dist fuel r output =
      Deflate.decodeSymbolsFuel litLen dist fuel r output := by
  induction fuel generalizing r output with
  | zero => rfl
  | succ fuel ih =>
    cases hs : Deflate.decodeStep litLen dist r output with
    | error error =>
      simp only [decodeSymbolsFuel, Deflate.decodeSymbolsFuel, decodeStep_eq_spec, hs]
    | ok step =>
      cases step with
      | done bytes r' =>
        simp only [decodeSymbolsFuel, Deflate.decodeSymbolsFuel, decodeStep_eq_spec, hs]
      | more bytes r' =>
        simpa only [decodeSymbolsFuel, Deflate.decodeSymbolsFuel, decodeStep_eq_spec, hs]
          using ih r' bytes

theorem decodeSymbol_eq_spec (litLen dist : HuffmanTable) (r : LSBReader)
    (output : List UInt8) :
    decodeSymbol litLen dist r output = Deflate.decodeSymbol litLen dist r output :=
  decodeSymbolsFuel_eq_spec litLen dist (r.bitsLeft + 1) r output

end Silmaril.Formats.Compression.Inflate.Manual
