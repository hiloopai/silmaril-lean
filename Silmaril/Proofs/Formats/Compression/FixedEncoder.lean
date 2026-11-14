module

public import Silmaril.Formats.Compression.Deflate.Defs
public import Silmaril.Raw.Formats.Compression.Deflate.RoundTrip
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Proofs.Formats.Compression.Deflate
public import Silmaril.Proofs.Formats.Compression.DeflateLocal

/-!
Proofs for the compressing (fixed-Huffman) encoder of
`Silmaril.Formats.Compression.Deflate.Thms`: the output of `compress` is a
complete DEFLATE member, so the list-level decoder reads it back and stops
exactly at its end. The token-level specifications of `Deflate.RoundTrip` are
restated here with the final reader position, which the byte-level `decompress`
statement does not need.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.FixedEncoder

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

section Tokens

variable {litLen dist : HuffmanTable} (hl : ∀ s < 286, litLen.SymOK s)
  (hd : ∀ s < 30, dist.SymOK s)

include hl in
theorem writeToken_eob_spec' {out : List UInt8} {w : LSBWriter} {bs : List Bool} (hw : w.Rep bs) :
    ∃ w' bits, writeToken litLen dist w .eob = some w' ∧ w'.Rep (bs ++ bits) ∧
      ∀ (r : LSBReader) rest, r.Rep (bits ++ rest) → ∃ r', r'.Rep rest ∧
        ∀ fuel, decodeSymbolsFuel litLen dist (fuel + 1) r out = .ok (out, r') := by
  obtain ⟨w', bits, hwr, hrep, _, hread⟩ := (hl 256 (by decide)).writeSymbolLSB hw
  refine ⟨w', bits, by simpa [writeToken] using hwr, hrep, fun r rest hr => ?_⟩
  obtain ⟨r', hr', hrr⟩ := hread r rest hr
  exact ⟨r', hrr, fun fuel => by simp [decodeSymbolsFuel, decodeStep, hr']⟩

include hl hd in
/-- `encodeTokens_spec` with the reader after the end-of-block code. -/
theorem encodeTokens_spec' {ts : List Token} {out : List UInt8} (hts : TokensValid out ts)
    {w : LSBWriter} {bs : List Bool} (hw : w.Rep bs) :
    ∃ w' bits, encodeTokens litLen dist w (ts ++ [.eob]) = some w' ∧ w'.Rep (bs ++ bits) ∧
      ∀ (r : LSBReader) rest fuel, r.Rep (bits ++ rest) → bits.length + rest.length < fuel →
        ∃ r', r'.Rep rest ∧
          decodeSymbolsFuel litLen dist fuel r out = .ok (applyTokens out ts, r') := by
  induction ts generalizing out w bs with
  | nil =>
    obtain ⟨w', bits, hwr, hrep, hread⟩ := writeToken_eob_spec' hl (dist := dist) (out := out) hw
    refine ⟨w', bits, by simp [encodeTokens, hwr], hrep, fun r rest fuel hr hf => ?_⟩
    obtain ⟨r', hrr, hr'⟩ := hread r rest hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact ⟨r', hrr, by simpa using hr' f⟩
  | cons t ts ih =>
    obtain ⟨ht, hts⟩ := hts
    obtain ⟨w1, bits1, hw1, hrep1, hlen1, hread1⟩ := writeToken_spec hl hd ht hw
    obtain ⟨w2, bits2, hw2, hrep2, hread2⟩ := ih hts hrep1
    refine ⟨w2, bits1 ++ bits2, by simp [encodeTokens, hw1, hw2], by simpa using hrep2,
      fun r rest fuel hr hf => ?_⟩
    rw [List.append_assoc] at hr
    obtain ⟨r1, hrr1, hdec1⟩ := hread1 r _ hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨r', hrr', hr'⟩ := hread2 r1 rest f hrr1 (by simp at hf; omega)
    exact ⟨r', hrr', by rw [hdec1 f, hr']; rfl⟩

end Tokens

/-- Flushing a writer pads fewer than eight bits. -/
theorem toByteArray_pad_lt {w : LSBWriter} {bs pad : List Bool} (h : w.Rep bs)
    (hp : bytesBits w.toByteArray.data.toList = bs ++ pad) : pad.length < 8 := by
  obtain ⟨hc, _, hbs⟩ := h
  have hl := congrArg List.length hp
  rw [← hbs] at hl
  unfold LSBWriter.toByteArray at hl
  split at hl
  · next h0 => simp only [List.length_append, length_bytesBits, length_natBits, h0] at hl; omega
  · simp [length_bytesBits, length_natBits] at hl; omega

/-- The output of `compress` is one DEFLATE member, decoded exactly to its end. -/
theorem compress_take {data c : ByteArray} (h : compress data = some c) :
    deflateTake c.data.toList = .ok (data.data.toList, []) := by
  obtain ⟨t, ht, hl⟩ := fixedLitLenTable_spec
  obtain ⟨td, htd, hd⟩ := fixedDistTable_spec
  obtain ⟨hlz, hval, happ⟩ := lz77Greedy_spec data.data
  obtain ⟨w', bits, hw', hrep, hread⟩ := encodeTokens_spec' hl hd hval
    ((LSBWriter.rep_empty.writeBit true).writeVal 1 2)
  have hc : c = w'.toByteArray := by
    unfold compress at h
    rw [ht, htd] at h
    simp only [writeFixedHuffmanBlock, hlz, hw', Option.some.injEq] at h
    exact h.symm
  subst hc
  obtain ⟨pad, hpad⟩ := hrep.toByteArray
  have hpl := toByteArray_pad_lt hrep hpad
  have hr0 := LSBReader.rep_ofByteArray w'.toByteArray
  rw [hpad] at hr0
  simp only [List.nil_append, natBits, List.cons_append] at hr0
  obtain ⟨r1, h1, hr1⟩ := hr0.readBit
  obtain ⟨r2, h2, hr2⟩ := (show r1.Rep (natBits 1 2 ++ (bits ++ pad)) from hr1).readBits
  obtain ⟨r3, hr3, h3⟩ := hread r2 pad (r2.bitsLeft + 1) hr2 (by rw [hr2.bitsLeft]; simp)
  rw [happ] at h3
  have hb : (1 : Nat) % 2 ^ 2 = 1 := by decide
  rw [hb] at h2
  have hin : r3.input = [] := by
    have := hr3.bitsLeft
    simp only [LSBReader.bitsLeft] at this
    cases hi : r3.input with
    | nil => rfl
    | cons _ _ => rw [hi] at this; simp at this; omega
  have hreader : (⟨0, 0, w'.toByteArray.data.toList, 0⟩ : LSBReader) =
      LSBReader.ofByteArray w'.toByteArray := by
    simp [LSBReader.ofByteArray, ByteArray_toList_eq]
  unfold deflateTake
  dsimp only
  rw [hreader]
  generalize (LSBReader.ofByteArray w'.toByteArray).bitsLeft = f
  simp only [decompressBlocks, decompressBlockBody, h1, h2, ht, htd, decodeSymbol, h3,
    Nat.one_ne_zero, ↓reduceIte, hin]

/-- The compressing encoder round-trips through the member decoder, whatever
follows the member. -/
theorem roundTripFixed : RoundTrip decoder encoderFixed := by
  intro data rest
  unfold encoderFixed
  cases hc : compress ⟨data.toArray⟩ with
  | none => exact Proofs.Formats.Compression.Deflate.roundTrip data rest
  | some c =>
    have h := DeflateLocal.deflateTake_append (compress_take hc) rest
    simp only [List.nil_append] at h
    exact Proofs.Formats.Compression.Deflate.decoder_eq_some.mpr h

end Silmaril.Proofs.Formats.Compression.FixedEncoder
