module

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

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

open Silmaril.Formats.Compression

/-!
# A stable fuel bound for Huffman decoding

These laws concern the existing mathematical DEFLATE decoder. They impose no
well-formedness hypothesis on a Huffman table: `lookupEntry` already excludes
zero-length entries. Every successfully decoded literal/length symbol therefore
consumes at least one input bit, including for malformed tables.
-/

theorem readBit_bitsLeft {r r' : LSBReader} {b : Bool}
    (h : r.readBit = some (b, r')) : r'.bitsLeft + 1 = r.bitsLeft := by
  unfold LSBReader.readBit at h
  split at h
  · next hc =>
    cases hi : r.input with
    | nil => simp [LSBReader.refill, hi, hc] at h
    | cons byte rest =>
      simp only [LSBReader.refill, hi] at h
      simp only [Nat.reduceEqDiff, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      simp [LSBReader.bitsLeft, hc, hi]
      omega
  · next hc =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    simp only [LSBReader.bitsLeft]
    omega

theorem readBits_bitsLeft {n : Nat} {r r' : LSBReader} {v : Nat}
    (h : r.readBits n = some (v, r')) : r'.bitsLeft + n = r.bitsLeft := by
  induction n generalizing r r' v with
  | zero =>
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    omega
  | succ n ih =>
    rw [LSBReader.readBits] at h
    cases hb : r.readBit with
    | none => simp [hb] at h
    | some p =>
      obtain ⟨b, r1⟩ := p
      rw [hb] at h
      dsimp only at h
      cases hn : r1.readBits n with
      | none => simp [hn] at h
      | some p =>
        obtain ⟨v1, r2⟩ := p
        rw [hn] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        have hbit := readBit_bitsLeft hb
        have hrest := ih hn
        omega

theorem decodeSymbolLSBAux_bitsLeft_le {entries : List CodeEntry} {r r' : LSBReader}
    {code len fuel sym : Nat}
    (h : decodeSymbolLSBAux entries r code len fuel = some (sym, r')) :
    r'.bitsLeft ≤ r.bitsLeft := by
  induction fuel generalizing r code len r' sym with
  | zero => simp [decodeSymbolLSBAux] at h
  | succ fuel ih =>
    rw [decodeSymbolLSBAux] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact Nat.le_refl _
    · cases hb : r.readBit with
      | none => simp [hb] at h
      | some p =>
        obtain ⟨b, r1⟩ := p
        rw [hb] at h
        dsimp only at h
        have hrest := ih h
        have hbit := readBit_bitsLeft hb
        omega

theorem readSymbolLSB_bitsLeft_lt {table : HuffmanTable} {r r' : LSBReader} {sym : Nat}
    (h : table.readSymbolLSB r = some (sym, r')) : r'.bitsLeft < r.bitsLeft := by
  unfold HuffmanTable.readSymbolLSB at h
  rw [decodeSymbolLSBAux] at h
  have hzero : lookupEntry table.entries 0 0 = none :=
    lookupEntry_go_eq_none_of_len_zero 0 table.entries
  rw [hzero] at h
  dsimp only at h
  cases hb : r.readBit with
  | none => simp [hb] at h
  | some p =>
    obtain ⟨b, r1⟩ := p
    rw [hb] at h
    dsimp only at h
    have hrest := decodeSymbolLSBAux_bitsLeft_le h
    have hbit := readBit_bitsLeft hb
    omega

theorem decodeStep_more_bitsLeft_lt {litLen dist : HuffmanTable}
    {r r' : LSBReader} {output out : List UInt8}
    (h : decodeStep litLen dist r output = .ok (.more out r')) :
    r'.bitsLeft < r.bitsLeft := by
  unfold decodeStep at h
  cases h0 : litLen.readSymbolLSB r with
  | none => simp [h0] at h
  | some p =>
    obtain ⟨sym, r1⟩ := p
    rw [h0] at h
    dsimp only at h
    have hs1 := readSymbolLSB_bitsLeft_lt h0
    split at h
    · simp only [Except.ok.injEq, SymbolStep.more.injEq] at h
      rw [← h.2]
      exact hs1
    · split at h
      · simp at h
      · split at h
        · cases h2 : r1.readBits (lengthExtraBits.getD (sym - 257) 0) with
          | none => rw [h2] at h; cases h
          | some p =>
            obtain ⟨ev, r2⟩ := p
            rw [h2] at h
            dsimp only at h
            cases h3 : dist.readSymbolLSB r2 with
            | none => simp [h3] at h
            | some p =>
              obtain ⟨ds, r3⟩ := p
              rw [h3] at h
              dsimp only at h
              split at h
              · simp at h
              · cases h4 : r3.readBits (distanceExtraBits.getD ds 0) with
                | none => rw [h4] at h; cases h
                | some p =>
                  obtain ⟨dv, r4⟩ := p
                  rw [h4] at h
                  dsimp only at h
                  split at h
                  · simp at h
                  · simp only [Except.ok.injEq, SymbolStep.more.injEq] at h
                    rw [← h.2]
                    have hs2 := readBits_bitsLeft h2
                    have hs3 := readSymbolLSB_bitsLeft_lt h3
                    have hs4 := readBits_bitsLeft h4
                    omega
        · simp at h

/-- Once the fuel exceeds the unread-bit count, more fuel cannot change the
result, including its errors and returned reader. -/
theorem decodeSymbolsFuel_stable (litLen dist : HuffmanTable) (r : LSBReader)
    (output : List UInt8) (fuel₁ fuel₂ : Nat)
    (h₁ : r.bitsLeft + 1 ≤ fuel₁) (h₂ : r.bitsLeft + 1 ≤ fuel₂) :
    decodeSymbolsFuel litLen dist fuel₁ r output =
      decodeSymbolsFuel litLen dist fuel₂ r output := by
  induction fuel₁ generalizing r output fuel₂ with
  | zero => omega
  | succ fuel₁ ih =>
    cases fuel₂ with
    | zero => omega
    | succ fuel₂ =>
      rw [decodeSymbolsFuel, decodeSymbolsFuel]
      cases hs : decodeStep litLen dist r output with
      | error e => rfl
      | ok st =>
        cases st with
        | done out r' => rfl
        | more out r' =>
          have hlt := decodeStep_more_bitsLeft_lt hs
          exact ih r' out fuel₂ (by omega) (by omega)

theorem decodeSymbolsFuel_eq_decodeSymbol (litLen dist : HuffmanTable) (r : LSBReader)
    (output : List UInt8) (fuel : Nat) (hfuel : r.bitsLeft + 1 ≤ fuel) :
    decodeSymbolsFuel litLen dist fuel r output = decodeSymbol litLen dist r output :=
  decodeSymbolsFuel_stable litLen dist r output fuel (r.bitsLeft + 1) hfuel (Nat.le_refl _)

end Silmaril.Formats.Compression.Deflate
