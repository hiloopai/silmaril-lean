module

public import Silmaril.Formats.Compression.Inflate.Manual.Dynamic
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

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Manual.Dynamic`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual

open Silmaril.Formats.Compression

theorem scatterCodeLengths_eq (remaining index : Nat) (lengths : List Nat)
    (r : LSBReader) :
    scatterCodeLengths remaining index lengths r =
      Deflate.readCLLengths remaining index lengths r := by
  induction remaining generalizing index lengths r with
  | zero => rfl
  | succ remaining ih =>
    simp only [scatterCodeLengths, Deflate.readCLLengths]
    cases r.readBits 3 with
    | none => rfl
    | some pair => exact ih _ _ _

theorem expandCodeLengths_eq (table : HuffmanTable) (total fuel : Nat)
    (lengths : List Nat) (r : LSBReader) :
    expandCodeLengths table total fuel lengths r =
      Deflate.readCodeLengths table total fuel lengths r := by
  induction fuel generalizing lengths r with
  | zero => rfl
  | succ fuel ih =>
    simp only [expandCodeLengths, Deflate.readCodeLengths]
    by_cases hlength : total ≤ lengths.length
    · simp only [ite_eq_left hlength]
    · simp only [ite_eq_right hlength]
      cases table.readSymbolLSB r with
      | none => rfl
      | some pair =>
        obtain ⟨symbol, afterSymbol⟩ := pair
        by_cases hliteral : symbol < 16
        · simp only [codeLengthRun, ite_eq_left hliteral]
          exact ih _ _
        · by_cases hrepeat : symbol = 16
          · simp only [codeLengthRun, ite_eq_right hliteral, ite_eq_left hrepeat]
            cases lengths.getLast? with
            | none => rfl
            | some length =>
              cases afterSymbol.readBits 2 with
              | none => rfl
              | some pair => exact ih _ _
          · by_cases hzero : symbol = 17
            · simp only [codeLengthRun, ite_eq_right hliteral, ite_eq_right hrepeat,
                ite_eq_left hzero]
              cases afterSymbol.readBits 3 with
              | none => rfl
              | some pair => exact ih _ _
            · by_cases hlong : symbol = 18
              · simp only [codeLengthRun, ite_eq_right hliteral, ite_eq_right hrepeat,
                  ite_eq_right hzero, ite_eq_left hlong]
                cases afterSymbol.readBits 7 with
                | none => rfl
                | some pair => exact ih _ _
              · simp only [codeLengthRun, ite_eq_right hliteral, ite_eq_right hrepeat,
                  ite_eq_right hzero, ite_eq_right hlong]

/-- Missing end-of-block is rejected before constructing either table. -/
theorem buildDynamicTables_missing_endBlock (literalCount : Nat) (lengths : List Nat)
    (r : LSBReader) (hmissing : (lengths.take literalCount).getD 256 0 = 0) :
    buildDynamicTables literalCount lengths r = .error .badDynamicHuffman := by
  simp only [buildDynamicTables, hmissing, ↓reduceIte]

/-- Every successful construction includes a nonzero end-of-block code length. -/
theorem buildDynamicTables_endBlock_nonzero (literalCount : Nat) (lengths : List Nat)
    (r rest : LSBReader) (literals distances : HuffmanTable)
    (hsuccess : buildDynamicTables literalCount lengths r = .ok (literals, distances, rest)) :
    (lengths.take literalCount).getD 256 0 ≠ 0 := by
  intro hmissing
  rw [buildDynamicTables_missing_endBlock literalCount lengths r hmissing] at hsuccess
  cases hsuccess

/-- Exact equality includes malformed input and reader state, not just accepted
payloads or the existence of some table satisfying an abstract predicate. -/
theorem readDynamicTables_eq (r : LSBReader) :
    readDynamicTables r = Deflate.readDynamicTables r := by
  simp only [readDynamicTables, readDynamicCounts, Deflate.readDynamicTables]
  cases r.readBits 5 with
  | none => rfl
  | some pair =>
    obtain ⟨hlit, r1⟩ := pair
    dsimp only
    cases r1.readBits 5 with
    | none => rfl
    | some pair =>
      obtain ⟨hdist, r2⟩ := pair
      dsimp only
      cases r2.readBits 4 with
      | none => rfl
      | some pair =>
        obtain ⟨hclen, r3⟩ := pair
        dsimp only
        by_cases hcounts : 286 < hlit + 257 ∨ 30 < hdist + 1
        · simp only [ite_eq_left hcounts]
        · simp only [ite_eq_right hcounts, readDynamicAfterCounts, scatterCodeLengths_eq]
          cases Deflate.readCLLengths (hclen + 4) 0 (List.replicate 19 0) r3 with
          | error error => rfl
          | ok pair =>
            obtain ⟨lengths, afterLengths⟩ := pair
            dsimp only
            split
            · rfl
            · cases HuffmanTable.ofLengths lengths 7 with
              | none => rfl
              | some table =>
                dsimp only
                simp only [expandCodeLengths_eq]
                cases Deflate.readCodeLengths table (hlit + 257 + (hdist + 1))
                    (hlit + 257 + (hdist + 1) + 1) [] afterLengths with
                | error error => rfl
                | ok pair => rfl

end Silmaril.Formats.Compression.Inflate.Manual
