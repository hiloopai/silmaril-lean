module

public import Silmaril.Formats.Compression.Deflate.RoundTrip
public import Silmaril.Raw.Formats.Compression.Deflate.HuffmanLemmas
public import Silmaril.Raw.Formats.Compression.Deflate.LZ77

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Deflate.RoundTrip`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

open Silmaril.Formats.Compression

/-! ### Fixed Huffman tables -/

theorem kraftTotal_append (L L' : CodeLengths) (M : Nat) :
    kraftTotal (L ++ L') M = kraftTotal L M + kraftTotal L' M := by
  simp [kraftTotal]

theorem kraftTotal_replicate (n x M : Nat) (hx : 0 < x) :
    kraftTotal (List.replicate n x) M = n * 2 ^ (M - x) := by
  simp [kraftTotal, List.map_replicate, List.sum_replicate_nat, Nat.pos_iff_ne_zero.mp hx]

theorem isValidLengths_of_kraftTotal (L : CodeLengths) (M : Nat) (hb : ∀ x ∈ L, x ≤ M)
    (h : kraftTotal L M ≤ 2 ^ M) : isValidLengths L M = true := by
  simp only [isValidLengths, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨hb, ?_⟩
  rw [kraftSum, kraft_foldl, Nat.shiftLeft_eq]
  simpa using h

theorem fixedLitLenLengths_getElem? (i : Nat) (hi : i < 288) :
    fixedLitLenLengths[i]? =
      some (if i < 144 then 8 else if i < 256 then 9 else if i < 280 then 7 else 8) := by
  rw [fixedLitLenLengths, List.getElem?_ofFn]
  simp only [hi, ↓reduceDIte]

theorem fixedLitLenLengths_length : fixedLitLenLengths.length = 288 := by
  rw [fixedLitLenLengths, List.length_ofFn]

theorem fixedLitLenLengths_getElem (i : Nat) (hi : i < fixedLitLenLengths.length) :
    fixedLitLenLengths[i] =
      if i < 144 then 8 else if i < 256 then 9 else if i < 280 then 7 else 8 := by
  have h := fixedLitLenLengths_getElem? i (by rwa [fixedLitLenLengths_length] at hi)
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

set_option maxRecDepth 4000 in
theorem fixedLitLenLengths_eq : fixedLitLenLengths =
    List.replicate 144 8 ++ List.replicate 112 9 ++ List.replicate 24 7 ++ List.replicate 8 8 := by
  apply List.ext_getElem (by simp [fixedLitLenLengths_length])
  intro i h1 h2
  rw [fixedLitLenLengths_getElem]
  simp only [List.getElem_append, List.getElem_replicate, List.length_append,
    List.length_replicate]
  by_cases a : i < 144 <;> by_cases b : i < 256 <;> by_cases c : i < 280 <;>
    simp [a, b, c] <;> omega

theorem fixedLitLenLengths_valid : isValidLengths fixedLitLenLengths 9 = true := by
  apply isValidLengths_of_kraftTotal
  · intro x hx
    rw [fixedLitLenLengths_eq] at hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with ((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> omega
  rw [fixedLitLenLengths_eq]
  simp only [kraftTotal_append, kraftTotal_replicate _ _ _ (by decide : 0 < 8),
    kraftTotal_replicate _ _ _ (by decide : 0 < 9), kraftTotal_replicate _ _ _ (by decide : 0 < 7)]
  decide

theorem fixedDistLengths_valid : isValidLengths fixedDistLengths 5 = true := by
  apply isValidLengths_of_kraftTotal
  · intro x hx
    simp only [fixedDistLengths, List.mem_replicate] at hx
    omega
  simp only [fixedDistLengths, kraftTotal_replicate _ _ _ (by decide : 0 < 5)]
  decide

theorem fixedLitLenTable_spec :
    ∃ t, fixedLitLenTable = some t ∧ ∀ s < 286, t.SymOK s := by
  have h : fixedLitLenTable = HuffmanTable.ofLengths fixedLitLenLengths 9 := rfl
  cases ht : HuffmanTable.ofLengths fixedLitLenLengths 9 with
  | none => simp [HuffmanTable.ofLengths, fixedLitLenLengths_valid] at ht
  | some t =>
    refine ⟨t, by rw [h, ht], fun s hs => ?_⟩
    have hs' : s < fixedLitLenLengths.length := by rw [fixedLitLenLengths_length]; omega
    refine HuffmanTable.ofLengths_symOK ht hs' ?_
    rw [fixedLitLenLengths_getElem]
    split <;> (try split) <;> (try split) <;> decide

theorem fixedDistTable_spec :
    ∃ t, fixedDistTable = some t ∧ ∀ s < 30, t.SymOK s := by
  have h : fixedDistTable = HuffmanTable.ofLengths fixedDistLengths 5 := rfl
  cases ht : HuffmanTable.ofLengths fixedDistLengths 5 with
  | none => simp [HuffmanTable.ofLengths, fixedDistLengths_valid] at ht
  | some t =>
    refine ⟨t, by rw [h, ht], fun s hs => ?_⟩
    have hs' : s < fixedDistLengths.length := by simp [fixedDistLengths]; omega
    refine HuffmanTable.ofLengths_symOK ht hs' ?_
    simp only [fixedDistLengths, List.getElem_replicate]
    decide

/-! ### Length and distance codes -/

theorem findCode_spec (bases : List Nat) (x bound idx : Nat) (hidx : idx ≤ bound)
    (hb : bases.getD idx 0 ≤ x) :
    findCode bases x bound idx ≤ bound ∧ bases.getD (findCode bases x bound idx) 0 ≤ x ∧
      (findCode bases x bound idx < bound →
        x < bases.getD (findCode bases x bound idx + 1) 0) := by
  fun_induction findCode bases x bound idx with
  | case1 idx hlt hle ih => exact ih (by omega) hle
  | case2 idx hlt hgt => exact ⟨by omega, hb, fun _ => by omega⟩
  | case3 idx hge => exact ⟨Nat.le_refl _, by rwa [show idx = bound by omega] at hb, by omega⟩

theorem lengthBase_facts :
    (∀ i < 29, lengthBase.getD i 3 = lengthBase.getD i 0) ∧
      (∀ i < 28, lengthBase.getD (i + 1) 0 ≤ lengthBase.getD i 0 + 2 ^ lengthExtraBits.getD i 0) ∧
      lengthBase.getD 28 0 = 258 ∧ lengthBase.getD 0 0 = 3 := by
  decide

theorem distanceBase_facts :
    (∀ i < 30, distanceBase.getD i 1 = distanceBase.getD i 0) ∧
      (∀ i < 29, distanceBase.getD (i + 1) 0 ≤
        distanceBase.getD i 0 + 2 ^ distanceExtraBits.getD i 0) ∧
      distanceBase.getD 29 0 = 24577 ∧ distanceExtraBits.getD 29 0 = 13 ∧
      distanceBase.getD 0 0 = 1 := by
  decide

set_option maxRecDepth 4000 in
theorem findLenCode_spec (len : Nat) (h3 : 3 ≤ len) (h258 : len ≤ 258) :
    257 ≤ findLenCode len ∧ findLenCode len ≤ 285 ∧
      lengthBase.getD (findLenCode len - 257) 3 ≤ len ∧
      len - lengthBase.getD (findLenCode len - 257) 3 <
        2 ^ lengthExtraBits.getD (findLenCode len - 257) 0 := by
  obtain ⟨hd, hgap, h28, h0⟩ := lengthBase_facts
  obtain ⟨hle, hbase, hnext⟩ := findCode_spec lengthBase len 28 0 (by decide) (by omega)
  have hsub : findLenCode len - 257 = findCode lengthBase len 28 0 := by
    simp [findLenCode]
  rw [hsub, hd _ (by omega)]
  refine ⟨by simp [findLenCode], by simp [findLenCode]; omega, hbase, ?_⟩
  by_cases h : findCode lengthBase len 28 0 < 28
  · have := hgap _ h
    have := hnext h
    omega
  · have he : findCode lengthBase len 28 0 = 28 := by omega
    rw [he] at hbase ⊢
    rw [h28] at hbase ⊢
    have : len - 258 = 0 := by omega
    rw [this]; exact Nat.two_pow_pos _

theorem findDistCode_spec (d : Nat) (h1 : 1 ≤ d) (hd : d ≤ 32768) :
    findDistCode d < 30 ∧ distanceBase.getD (findDistCode d) 1 ≤ d ∧
      d - distanceBase.getD (findDistCode d) 1 < 2 ^ distanceExtraBits.getD (findDistCode d) 0 := by
  obtain ⟨hd', hgap, h29, he29, h0⟩ := distanceBase_facts
  obtain ⟨hle, hbase, hnext⟩ := findCode_spec distanceBase d 29 0 (by decide) (by omega)
  simp only [findDistCode]
  rw [hd' _ (by omega)]
  refine ⟨by omega, hbase, ?_⟩
  by_cases h : findCode distanceBase d 29 0 < 29
  · have := hgap _ h
    have := hnext h
    omega
  · have he : findCode distanceBase d 29 0 = 29 := by omega
    rw [he, h29, he29]
    omega

/-! ### Tokens -/

section Tokens

variable {litLen dist : HuffmanTable} (hl : ∀ s < 286, litLen.SymOK s)
  (hd : ∀ s < 30, dist.SymOK s)
include hl hd

/-- Writing a non-final token and decoding it back performs that token. -/
theorem writeToken_spec {out : List UInt8} {t : Token} (ht : TokenValid out t)
    {w : LSBWriter} {bs : List Bool} (hw : w.Rep bs) :
    ∃ w' bits, writeToken litLen dist w t = some w' ∧ w'.Rep (bs ++ bits) ∧ 0 < bits.length ∧
      ∀ (r : LSBReader) rest, r.Rep (bits ++ rest) → ∃ r', r'.Rep rest ∧
        ∀ fuel, decodeSymbolsFuel litLen dist (fuel + 1) r out =
          decodeSymbolsFuel litLen dist fuel r' (applyToken out t) := by
  cases t with
  | eob => exact ht.elim
  | literal b =>
    obtain ⟨w', bits, hwr, hrep, hlen, hread⟩ := (hl b.toNat (by have := b.toNat_lt; omega)).writeSymbolLSB hw
    refine ⟨w', bits, by simpa [writeToken] using hwr, hrep, hlen, fun r rest hr => ?_⟩
    obtain ⟨r', hr', hrr⟩ := hread r rest hr
    refine ⟨r', hrr, fun fuel => ?_⟩
    simp [decodeSymbolsFuel, decodeStep, hr', b.toNat_lt, applyToken]
  | lenDist len d =>
    obtain ⟨h3, h258, hd1, hd2, hdo⟩ := ht
    obtain ⟨hlc1, hlc2, hlb, hlx⟩ := findLenCode_spec len h3 h258
    obtain ⟨hdc, hdb, hdx⟩ := findDistCode_spec d hd1 hd2
    obtain ⟨w1, bits1, hw1, hrep1, hlen1, hread1⟩ :=
      (hl (findLenCode len) (by omega)).writeSymbolLSB hw
    have hrep1' := hrep1.writeVal (len - lengthBase.getD (findLenCode len - 257) 3)
      (lengthExtraBits.getD (findLenCode len - 257) 0)
    obtain ⟨w2, bits2, hw2, hrep2, _, hread2⟩ := (hd (findDistCode d) hdc).writeSymbolLSB hrep1'
    have hrep2' := hrep2.writeVal (d - distanceBase.getD (findDistCode d) 1)
      (distanceExtraBits.getD (findDistCode d) 0)
    refine ⟨w2.writeVal (d - distanceBase.getD (findDistCode d) 1)
      (distanceExtraBits.getD (findDistCode d) 0), bits1 ++ natBits (len - lengthBase.getD (findLenCode len - 257) 3)
      (lengthExtraBits.getD (findLenCode len - 257) 0) ++ bits2 ++
      natBits (d - distanceBase.getD (findDistCode d) 1) (distanceExtraBits.getD (findDistCode d) 0),
      ?_, by simpa [List.append_assoc] using hrep2', by simp; omega, fun r rest hr => ?_⟩
    · simp only [writeToken, hw1, hw2]
    simp only [List.append_assoc] at hr
    obtain ⟨r1, hr1, hrr1⟩ := hread1 r _ hr
    obtain ⟨r2, hr2, hrr2⟩ := hrr1.readBits
    obtain ⟨r3, hr3, hrr3⟩ := hread2 r2 _ hrr2
    obtain ⟨r4, hr4, hrr4⟩ := hrr3.readBits
    refine ⟨r4, hrr4, fun fuel => ?_⟩
    rw [Nat.mod_eq_of_lt hlx] at hr2
    rw [Nat.mod_eq_of_lt hdx] at hr4
    have hlen' : lengthBase.getD (findLenCode len - 257) 3 +
        (len - lengthBase.getD (findLenCode len - 257) 3) = len := by omega
    have hdist' : distanceBase.getD (findDistCode d) 1 +
        (d - distanceBase.getD (findDistCode d) 1) = d := by omega
    have hn1 : ¬ findLenCode len < 256 := by omega
    have hn2 : findLenCode len ≠ 256 := by omega
    have hn3 : ¬ d > out.length := by omega
    have hn4 : ¬ 30 ≤ findDistCode d := by omega
    simp only [decodeSymbolsFuel, decodeStep, hr1, hn1, hn2, hlc2, hr2, hr3, hr4, hlen', hdist', hn3,
      hn4, ↓reduceIte, applyToken]

omit hd in
/-- Writing end-of-block and decoding it back ends the block. -/
theorem writeToken_eob_spec {out : List UInt8} {w : LSBWriter} {bs : List Bool} (hw : w.Rep bs) :
    ∃ w' bits, writeToken litLen dist w .eob = some w' ∧ w'.Rep (bs ++ bits) ∧
      ∀ (r : LSBReader) rest, r.Rep (bits ++ rest) → ∃ r',
        ∀ fuel, decodeSymbolsFuel litLen dist (fuel + 1) r out = .ok (out, r') := by
  obtain ⟨w', bits, hwr, hrep, _, hread⟩ := (hl 256 (by decide)).writeSymbolLSB hw
  refine ⟨w', bits, by simpa [writeToken] using hwr, hrep, fun r rest hr => ?_⟩
  obtain ⟨r', hr', _⟩ := hread r rest hr
  exact ⟨r', fun fuel => by simp [decodeSymbolsFuel, decodeStep, hr']⟩

/-- A valid token stream followed by end-of-block decodes to its expansion. -/
theorem encodeTokens_spec {ts : List Token} {out : List UInt8} (hts : TokensValid out ts)
    {w : LSBWriter} {bs : List Bool} (hw : w.Rep bs) :
    ∃ w' bits, encodeTokens litLen dist w (ts ++ [.eob]) = some w' ∧ w'.Rep (bs ++ bits) ∧
      ∀ (r : LSBReader) rest fuel, r.Rep (bits ++ rest) → bits.length + rest.length < fuel →
        ∃ r', decodeSymbolsFuel litLen dist fuel r out = .ok (applyTokens out ts, r') := by
  induction ts generalizing out w bs with
  | nil =>
    obtain ⟨w', bits, hwr, hrep, hread⟩ := writeToken_eob_spec hl (dist := dist) (out := out) hw
    refine ⟨w', bits, by simp [encodeTokens, hwr], hrep, fun r rest fuel hr hf => ?_⟩
    obtain ⟨r', hr'⟩ := hread r rest hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact ⟨r', by simpa using hr' f⟩
  | cons t ts ih =>
    obtain ⟨ht, hts⟩ := hts
    obtain ⟨w1, bits1, hw1, hrep1, hlen1, hread1⟩ := writeToken_spec hl hd ht hw
    obtain ⟨w2, bits2, hw2, hrep2, hread2⟩ := ih hts hrep1
    refine ⟨w2, bits1 ++ bits2, by simp [encodeTokens, hw1, hw2], by simpa using hrep2,
      fun r rest fuel hr hf => ?_⟩
    rw [List.append_assoc] at hr
    obtain ⟨r1, hrr1, hdec1⟩ := hread1 r _ hr
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨r', hr'⟩ := hread2 r1 rest f hrr1 (by simp at hf; omega)
    exact ⟨r', by rw [hdec1 f, hr']; rfl⟩

end Tokens

/-! ### Stored blocks

`writeStoredBlock` is the path `zlibCompress` and `gzipCompress` take, and the
one that silently corrupted every input of 65536 bytes or more.  The statement
that would have caught it is `writeStoredBlock_sound` at the end of this
section: it holds for *every* `data`, because `writeStoredGo` now splits.
-/

theorem storedBits_length (final : Bool) (data : List UInt8) :
    (storedBits final data).length = 40 + 8 * data.length := by
  simp [storedBits]; omega

theorem storedChunks_pos (data : List UInt8) : 1 ≤ storedChunks data := by
  rw [storedChunks]; split <;> omega

theorem storedStream_length (data : List UInt8) :
    (storedStream data).length = 40 * storedChunks data + 8 * data.length := by
  fun_induction storedStream data with
  | case1 data hle => rw [storedChunks]; simp [hle, storedBits_length]
  | case2 data hle ih =>
    rw [storedChunks]
    simp only [hle, ↓reduceDIte, List.length_append, storedBits_length, ih, List.length_take,
      List.length_drop, maxStoredLen]
    simp only [maxStoredLen] at hle
    omega

/-! #### Writing -/

theorem writeStoredChunk_rep {w : LSBWriter} {bs : List Bool} (h : w.Rep bs) (hc : w.count = 0)
    (final : Bool) (data : List UInt8) :
    (writeStoredChunk w final data).Rep (bs ++ storedBits final data) ∧
      (writeStoredChunk w final data).count = 0 := by
  have hlt : w.count < 8 := by omega
  have r1 := h.writeBit final
  have c1 : (w.writeBit final).count = 1 := by rw [LSBWriter.writeBit_count _ hlt, hc]
  have r2 := r1.writeVal 0 2
  have c2 : ((w.writeBit final).writeVal 0 2).count = 3 := by
    rw [LSBWriter.writeVal_count 2 _ 0 (by omega), c1]
  have r3 := r2.alignToByte
  rw [c2] at r3
  have c3 : (((w.writeBit final).writeVal 0 2).alignToByte).count = 0 :=
    LSBWriter.alignToByte_count _
  have r4 := r3.writeVal data.length 16
  have c4 : ((((w.writeBit final).writeVal 0 2).alignToByte).writeVal data.length 16).count
      = 0 := by rw [LSBWriter.writeVal_count 16 _ _ (by omega), c3]
  have r5 := r4.writeVal (maxStoredLen ^^^ data.length) 16
  have c5 : (((((w.writeBit final).writeVal 0 2).alignToByte).writeVal data.length
      16).writeVal (maxStoredLen ^^^ data.length) 16).count = 0 := by
    rw [LSBWriter.writeVal_count 16 _ _ (by omega), c4]
  have r6 := LSBWriter.Rep.writeBytes data r5
  have c6 := LSBWriter.writeBytes_count data _ c5
  refine ⟨?_, by simpa only [writeStoredChunk] using c6⟩
  have hpad : ((8 : Nat) - 3) % 8 = 5 := by decide
  rw [hpad] at r6
  simpa only [writeStoredChunk, storedBits, List.append_assoc] using r6

theorem writeStoredGo_rep (w : LSBWriter) (data : List UInt8) :
    ∀ (bs : List Bool), w.Rep bs → w.count = 0 →
      (writeStoredGo w data).Rep (bs ++ storedStream data) ∧
        (writeStoredGo w data).count = 0 := by
  fun_induction writeStoredGo w data with
  | case1 w data hle =>
    intro bs h hc
    rw [storedStream]
    simp only [hle, ↓reduceDIte]
    exact writeStoredChunk_rep h hc true data
  | case2 w data hle ih =>
    intro bs h hc
    obtain ⟨h1, c1⟩ := writeStoredChunk_rep h hc false (data.take maxStoredLen)
    obtain ⟨h2, c2⟩ := ih (bs ++ storedBits false (data.take maxStoredLen)) h1 c1
    refine ⟨?_, c2⟩
    rw [storedStream]
    simp only [hle, ↓reduceDIte]
    simpa only [List.append_assoc] using h2

/-! #### Reading -/

theorem readStoredBytes_rep : ∀ (bs : List UInt8) {r : LSBReader} {rest : List Bool}
    (acc : List UInt8), r.Rep (bytesBits bs ++ rest) → r.count = 0 →
    ∃ r', readStoredBytes acc r bs.length = .ok (acc ++ bs, r') ∧ r'.Rep rest ∧ r'.count = 0 := by
  intro bs
  induction bs with
  | nil =>
    intro r rest acc h hc
    exact ⟨r, by simp [readStoredBytes], by simpa [bytesBits] using h, hc⟩
  | cons b bs ih =>
    intro r rest acc h hc
    simp only [bytesBits, List.flatMap_cons, List.append_assoc] at h
    obtain ⟨r1, h1, hr1⟩ := h.readBits
    have hc1 : r1.count = 0 := by rw [LSBReader.readBits_count 8 (by omega) h1, hc]
    obtain ⟨r2, h2, hr2, hc2⟩ := ih (acc ++ [b]) (by simpa [bytesBits] using hr1) hc1
    refine ⟨r2, ?_, hr2, hc2⟩
    have hb : b.toNat % 2 ^ 8 = b.toNat := Nat.mod_eq_of_lt (by simpa using b.toNat_lt)
    rw [hb] at h1
    simp only [List.length_cons, readStoredBytes, LSBReader.readByte, h1]
    rw [show UInt8.ofNat b.toNat = b from by simp]
    simpa using h2

theorem decompressStored_rep {r : LSBReader} {rest : List Bool} (data : List UInt8)
    (hlen : data.length ≤ maxStoredLen) (hc : r.count = 5)
    (h : r.Rep (List.replicate 5 false ++ (natBits data.length 16 ++
      (natBits (maxStoredLen ^^^ data.length) 16 ++ (bytesBits data ++ rest))))) :
    ∃ r', decompressStored r = .ok (data, r') ∧ r'.Rep rest ∧ r'.count = 0 := by
  have halign := h.alignToByte
  rw [hc, List.drop_left' (by simp)] at halign
  have hca : r.alignToByte.count = 0 := LSBReader.alignToByte_count r
  obtain ⟨r1, h1, hr1⟩ := halign.readBits
  have hc1 : r1.count = 0 := by rw [LSBReader.readBits_count 16 (by omega) h1, hca]
  obtain ⟨r2, h2, hr2⟩ := hr1.readBits
  have hc2 : r2.count = 0 := by rw [LSBReader.readBits_count 16 (by omega) h2, hc1]
  have hlen16 : data.length % 2 ^ 16 = data.length := by
    apply Nat.mod_eq_of_lt; simp only [maxStoredLen] at hlen; omega
  have hxlt : (maxStoredLen ^^^ data.length) < 2 ^ 16 := by
    have hA : (maxStoredLen : Nat) < 2 ^ 16 := by decide
    have hB : data.length < 2 ^ 16 := by simp only [maxStoredLen] at hlen; omega
    exact Nat.xor_lt_two_pow hA hB
  rw [hlen16] at h1
  rw [Nat.mod_eq_of_lt hxlt] at h2
  have hxor : data.length ^^^ (maxStoredLen ^^^ data.length) = maxStoredLen := by
    rw [← Nat.xor_assoc, Nat.xor_comm data.length maxStoredLen, Nat.xor_assoc, Nat.xor_self,
      Nat.xor_zero]
  have hcheck : ¬ ((data.length ^^^ (maxStoredLen ^^^ data.length)) % 65536 ≠ 65535) := by
    rw [hxor]; decide
  obtain ⟨r3, h3, hr3, hc3⟩ := readStoredBytes_rep data [] hr2 hc2
  refine ⟨r3, ?_, hr3, hc3⟩
  simp only [decompressStored, h1, h2, hcheck, ↓reduceIte]
  simpa using h3

theorem decompressBlocks_storedStream (data : List UInt8) :
    ∀ (fuel : Nat) (r : LSBReader) (rest : List Bool) (out : List UInt8),
      r.Rep (storedStream data ++ rest) → r.count = 0 → storedChunks data ≤ fuel →
      ∃ r', decompressBlocks fuel r out = .ok (out ++ data, r') ∧ r'.Rep rest := by
  fun_induction storedChunks data with
  | case1 data hle =>
    intro fuel r rest out h hc hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [storedStream] at h
    simp only [hle, ↓reduceDIte, storedBits, List.append_assoc, List.singleton_append] at h
    obtain ⟨r1, h1, hr1⟩ := h.readBit
    have hc1 : r1.count = 7 := by rw [LSBReader.readBit_count (by omega) h1, hc]
    obtain ⟨r2, h2, hr2⟩ := hr1.readBits
    have hc2 : r2.count = 5 := by rw [LSBReader.readBits_count 2 (by omega) h2, hc1]
    rw [show (0 : Nat) % 2 ^ 2 = 0 from by decide] at h2
    obtain ⟨r3, h3, hr3, _⟩ := decompressStored_rep data hle hc2 hr2
    refine ⟨r3, ?_, hr3⟩
    simp only [decompressBlocks, h1, h2, decompressBlockBody, h3, ↓reduceIte]
  | case2 data hle ih =>
    intro fuel r rest out h hc hf
    have hpos := storedChunks_pos (data.drop maxStoredLen)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [storedStream] at h
    simp only [hle, ↓reduceDIte, storedBits, List.append_assoc, List.singleton_append] at h
    obtain ⟨r1, h1, hr1⟩ := h.readBit
    have hc1 : r1.count = 7 := by rw [LSBReader.readBit_count (by omega) h1, hc]
    obtain ⟨r2, h2, hr2⟩ := hr1.readBits
    have hc2 : r2.count = 5 := by rw [LSBReader.readBits_count 2 (by omega) h2, hc1]
    rw [show (0 : Nat) % 2 ^ 2 = 0 from by decide] at h2
    obtain ⟨r3, h3, hr3, hc3⟩ :=
      decompressStored_rep (data.take maxStoredLen) (by simp only [List.length_take]; omega) hc2
        hr2
    obtain ⟨r4, h4, hr4⟩ := ih f r3 rest (out ++ data.take maxStoredLen) hr3 hc3 (by omega)
    refine ⟨r4, ?_, hr4⟩
    simp only [decompressBlocks, h1, h2, decompressBlockBody, h3, ↓reduceIte, Bool.false_eq_true,
      h4]
    rw [List.append_assoc, List.take_append_drop]

/-! #### Soundness -/

/-- The stored-block writer round-trips, for inputs of **any** size.  RFC 1951
§3.2.4 caps one stored block at 65535 bytes; `writeStoredGo` splits at that
boundary, with BFINAL set only on the last block.  Before the split,
`zlibCompress` / `gzipCompress` of any input of 65536 bytes or more produced a
stream its own decoder rejects. -/
theorem writeStoredBlock_sound (data : ByteArray) :
    decompress (writeStoredBlock data).toByteArray = some data := by
  obtain ⟨hrep, _⟩ := writeStoredGo_rep LSBWriter.empty data.toList []
    LSBWriter.rep_empty rfl
  rw [List.nil_append] at hrep
  obtain ⟨pad, hpad⟩ := hrep.toByteArray
  have hr0 := LSBReader.rep_ofByteArray (writeStoredGo LSBWriter.empty data.toList).toByteArray
  rw [hpad] at hr0
  have hbits : (LSBReader.ofByteArray
      (writeStoredGo LSBWriter.empty data.toList).toByteArray).bitsLeft
      = (storedStream data.toList).length + pad.length := by
    rw [hr0.bitsLeft]; simp
  have hfuel : storedChunks data.toList ≤
      (LSBReader.ofByteArray (writeStoredGo LSBWriter.empty data.toList).toByteArray).bitsLeft
        + 1 := by
    rw [hbits, storedStream_length]
    have := storedChunks_pos data.toList
    omega
  obtain ⟨r', hr', _⟩ := decompressBlocks_storedStream data.toList _ _ pad [] hr0 rfl hfuel
  unfold decompress writeStoredBlock decompressBlock
  rw [hr']
  simp [ByteArray_toList_eq]

/-- The wire format of a single stored block: five header bytes then the data
(RFC 1951 §3.2.4). -/
theorem writeStoredBlock_size (data : ByteArray) (h : data.size ≤ maxStoredLen) :
    (writeStoredBlock data).toByteArray.size = data.size + 5 := by
  have hlen : data.toList.length = data.size := by rw [ByteArray_toList_eq]; simp
  obtain ⟨hrep, hc⟩ := writeStoredGo_rep LSBWriter.empty data.toList []
    LSBWriter.rep_empty rfl
  rw [List.nil_append] at hrep
  have hsize := LSBWriter.toByteArray_size hrep hc
  have hchunks : storedChunks data.toList = 1 := by
    rw [storedChunks]; simp [hlen, h]
  rw [storedStream_length, hchunks] at hsize
  unfold writeStoredBlock
  omega

/-! ### Main theorems -/

/-- `compress` always succeeds. -/
theorem compress_total (data : ByteArray) : ∃ c, compress data = some c := by
  obtain ⟨t, ht, hl⟩ := fixedLitLenTable_spec
  obtain ⟨td, htd, hd⟩ := fixedDistTable_spec
  obtain ⟨hlz, hval, _⟩ := lz77Greedy_spec data.data
  obtain ⟨w', _, hw', _⟩ := encodeTokens_spec hl hd hval
    ((LSBWriter.rep_empty.writeBit true).writeVal 1 2)
  refine ⟨w'.toByteArray, ?_⟩
  unfold compress
  rw [ht, htd]
  simp only [writeFixedHuffmanBlock, hlz, hw']

/-- Whatever `compress` produces decodes back to its input. -/
theorem compress_sound {data c : ByteArray} (h : compress data = some c) : Compresses data c := by
  obtain ⟨t, ht, hl⟩ := fixedLitLenTable_spec
  obtain ⟨td, htd, hd⟩ := fixedDistTable_spec
  obtain ⟨hlz, hval, happ⟩ := lz77Greedy_spec data.data
  obtain ⟨w', bits, hw', hrep, hread⟩ := encodeTokens_spec hl hd hval
    ((LSBWriter.rep_empty.writeBit true).writeVal 1 2)
  have hc : c = w'.toByteArray := by
    unfold compress at h
    rw [ht, htd] at h
    simp only [writeFixedHuffmanBlock, hlz, hw', Option.some.injEq] at h
    exact h.symm
  subst hc
  obtain ⟨pad, hpad⟩ := hrep.toByteArray
  have hr0 := LSBReader.rep_ofByteArray w'.toByteArray
  rw [hpad] at hr0
  simp only [List.nil_append, natBits, List.cons_append] at hr0
  obtain ⟨r1, h1, hr1⟩ := hr0.readBit
  obtain ⟨r2, h2, hr2⟩ := (show r1.Rep (natBits 1 2 ++ (bits ++ pad)) from hr1).readBits
  obtain ⟨r3, h3⟩ := hread r2 pad (r2.bitsLeft + 1) hr2 (by rw [hr2.bitsLeft]; simp)
  rw [happ] at h3
  have hb : (1 : Nat) % 2 ^ 2 = 1 := by decide
  rw [hb] at h2
  unfold Compresses decompress decompressBlock
  generalize hf : (LSBReader.ofByteArray w'.toByteArray).bitsLeft = f
  simp only [decompressBlocks, decompressBlockBody, h1, h2, ht, htd, decodeSymbol, h3,
    Nat.one_ne_zero, ↓reduceIte]

/-- Every byte string has a DEFLATE encoding. -/
theorem decompress_surjective (data : ByteArray) : ∃ c, Compresses data c :=
  let ⟨c, hc⟩ := compress_total data
  ⟨c, compress_sound hc⟩

/-! ### Known-answer vectors

Everything above is stated against this file's own `decompress`, so it would
survive replacing both codecs by nonsense.  The byte strings below were produced
by zlib (`zlib.compressobj(9, zlib.DEFLATED, -15)` for the fixed and dynamic
blocks, `compressobj(0, …)` for the stored one), i.e. by an independent RFC 1951
implementation, and they pin the bit layout, the canonical code assignment, the
block headers and the dynamic code-length alphabet to the actual standard. -/

set_option maxRecDepth 100000 in
/-- Stored block (BTYPE 00) for `"abc"`, as emitted by zlib at level 0. -/
theorem decompress_stored_vector :
    decompress ⟨#[0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63]⟩
      = some ⟨#[0x61, 0x62, 0x63]⟩ := by
  have h : (⟨#[0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63]⟩ : ByteArray).toList
      = [0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63] := by rw [ByteArray_toList_eq]
  simp only [decompress, decompressBlock, LSBReader.ofByteArray, h]
  rfl

set_option maxRecDepth 100000 in
/-- Fixed-Huffman block (BTYPE 01) for `"abc"`, as emitted by zlib. -/
theorem decompress_fixed_vector :
    decompress ⟨#[0x4b, 0x4c, 0x4a, 0x06, 0x00]⟩ = some ⟨#[0x61, 0x62, 0x63]⟩ := by
  have h : (⟨#[0x4b, 0x4c, 0x4a, 0x06, 0x00]⟩ : ByteArray).toList
      = [0x4b, 0x4c, 0x4a, 0x06, 0x00] := by rw [ByteArray_toList_eq]
  simp only [decompress, decompressBlock, LSBReader.ofByteArray, h]
  rfl

set_option maxRecDepth 100000 in
/-- Dynamic-Huffman block (BTYPE 10) for a 40-byte string over `a b c d`, as
emitted by zlib at level 9.  This is the block type every real gzip/zlib stream
uses, and the one PR #818 could not decode at all. -/
theorem decompress_dynamic_vector :
    decompress ⟨#[0x25, 0x88, 0xb1, 0x09, 0x00, 0x00, 0x0c, 0x83, 0x6e, 0x35, 0xe6, 0xff,
      0x1b, 0x1a, 0xa8, 0x83, 0x88, 0xd8, 0x02, 0xd5, 0xe0, 0x82, 0x7c, 0x4e, 0x1d, 0xd8,
      0xb8, 0xe3, 0x01]⟩
      = some ⟨#[0x61, 0x63, 0x64, 0x64, 0x61, 0x61, 0x61, 0x64, 0x63, 0x63, 0x62, 0x61,
        0x63, 0x61, 0x61, 0x61, 0x61, 0x62, 0x64, 0x63, 0x63, 0x62, 0x61, 0x63, 0x63,
        0x63, 0x62, 0x64, 0x64, 0x64, 0x64, 0x61, 0x63, 0x64, 0x62, 0x63, 0x64, 0x63,
        0x63, 0x63]⟩ := by
  have h : (⟨#[0x25, 0x88, 0xb1, 0x09, 0x00, 0x00, 0x0c, 0x83, 0x6e, 0x35, 0xe6, 0xff,
      0x1b, 0x1a, 0xa8, 0x83, 0x88, 0xd8, 0x02, 0xd5, 0xe0, 0x82, 0x7c, 0x4e, 0x1d, 0xd8,
      0xb8, 0xe3, 0x01]⟩ : ByteArray).toList
      = [0x25, 0x88, 0xb1, 0x09, 0x00, 0x00, 0x0c, 0x83, 0x6e, 0x35, 0xe6, 0xff,
        0x1b, 0x1a, 0xa8, 0x83, 0x88, 0xd8, 0x02, 0xd5, 0xe0, 0x82, 0x7c, 0x4e, 0x1d, 0xd8,
        0xb8, 0xe3, 0x01] := by rw [ByteArray_toList_eq]
  simp only [decompress, decompressBlock, LSBReader.ofByteArray, h]
  rfl

/-! ### Rejection

`compress_sound` says nothing about streams this decoder should *refuse*.  The
distance guard below is the one that was missing: `distanceBase.getD distSym 1`
silently returned the default `1` for the reserved symbols 30 and 31. -/

/-- RFC 1951 §3.2.6: distance codes 30 and 31 never occur, and a decoder must
reject them rather than invent a distance. -/
theorem decodeStep_rejects_dist_ge_30 {litLen dist : HuffmanTable} {r r1 r2 r3 : LSBReader}
    {out : List UInt8} {sym distSym extraVal : Nat}
    (hs : litLen.readSymbolLSB r = some (sym, r1)) (h257 : 257 ≤ sym) (h285 : sym ≤ 285)
    (he : r1.readBits (lengthExtraBits.getD (sym - 257) 0) = some (extraVal, r2))
    (hd : dist.readSymbolLSB r2 = some (distSym, r3)) (h30 : 30 ≤ distSym) :
    decodeStep litLen dist r out = .error (.badDistanceCode distSym) := by
  have hn1 : ¬ sym < 256 := by omega
  have hn2 : sym ≠ 256 := by omega
  simp only [decodeStep, hs, hn1, hn2, h285, he, hd, h30, ↓reduceIte]

set_option maxRecDepth 100000 in
/-- `73 04 3e 00` is a fixed-Huffman block whose back-reference uses distance
code 30.  zlib reports `invalid distance code`; before this branch we returned
`"AAAA"`. -/
theorem decompress_rejects_dist_code_30 :
    decompress ⟨#[0x73, 0x04, 0x3e, 0x00]⟩ = none := by
  have h : (⟨#[0x73, 0x04, 0x3e, 0x00]⟩ : ByteArray).toList = [0x73, 0x04, 0x3e, 0x00] := by
    rw [ByteArray_toList_eq]
  simp only [decompress, decompressBlock, LSBReader.ofByteArray, h]
  rfl

/-- BTYPE 11 is reserved (RFC 1951 §3.2.3). -/
theorem decompress_rejects_reserved_btype :
    decompress ⟨#[0x07, 0x00]⟩ = none := by
  have h : (⟨#[0x07, 0x00]⟩ : ByteArray).toList = [0x07, 0x00] := by rw [ByteArray_toList_eq]
  simp only [decompress, decompressBlock, LSBReader.ofByteArray, h]
  rfl

end Silmaril.Formats.Compression.Deflate
