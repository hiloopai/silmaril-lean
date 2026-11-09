module

public import Silmaril.Formats.Compression.Deflate.Stored
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Formats.Compression.Deflate.Decompress

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Deflate.Stored`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

open Silmaril.Formats.Compression

/-! ### Round trip

`decompressBlocks` is the format; these lemmas show that a stored stream decodes
to the bytes it was built from. Everything is byte-aligned, so the reader states
are explicit `⟨0, 0, bytes, _⟩` rather than abstract bit lists. -/

/-- Reading `n` bits that are already in the buffer. -/
theorem readBits_of_count (v n k : Nat) (inp : List UInt8) (t : Nat) :
    LSBReader.readBits ⟨v, n + k, inp, t⟩ n = some (v % 2 ^ n, ⟨v >>> n, k, inp, t + n⟩) := by
  induction n generalizing v t with
  | zero => simp [LSBReader.readBits, Nat.mod_one]
  | succ n ih =>
    have hb : LSBReader.readBit ⟨v, (n + 1) + k, inp, t⟩
        = some (decide (v % 2 = 1), ⟨v >>> 1, n + k, inp, t + 1⟩) := by
      simp [LSBReader.readBit]
    rw [LSBReader.readBits, hb]
    dsimp only
    rw [ih (v >>> 1) (t + 1)]
    have hv : (if (decide (v % 2 = 1)) = true then 1 else 0) + 2 * (v >>> 1 % 2 ^ n)
        = v % 2 ^ (n + 1) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.pow_succ', Nat.mod_mul]
      by_cases h : v % 2 = 1 <;> simp [h] <;> omega
    have hs : v >>> 1 >>> n = v >>> (n + 1) := by
      rw [← Nat.shiftRight_add, Nat.add_comm]
    simp only [Option.some.injEq, Prod.mk.injEq, LSBReader.mk.injEq]
    exact ⟨hv, hs, trivial, trivial, by omega⟩

/-- A reader at a byte boundary, about to read the byte `b`. -/
theorem readBit_aligned (b : UInt8) (rest : List UInt8) (t : Nat) :
    LSBReader.readBit ⟨0, 0, b :: rest, t⟩
      = some (decide (b.toNat % 2 = 1), ⟨b.toNat >>> 1, 7, rest, t + 1⟩) := by
  simp [LSBReader.readBit, LSBReader.refill]
  rfl

/-- `if v % 2 = 1 then 1 else 0` is `v % 2`. -/
theorem ite_mod_two (v : Nat) : (if (decide (v % 2 = 1)) = true then 1 else 0) = v % 2 := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

/-- Reading a whole byte at a byte boundary leaves the reader at the next one. -/
theorem readBits8_aligned (b : UInt8) (rest : List UInt8) (t : Nat) :
    LSBReader.readBits ⟨0, 0, b :: rest, t⟩ 8 = some (b.toNat, ⟨0, 0, rest, t + 8⟩) := by
  have hlt : b.toNat < 256 := b.toNat_lt
  rw [show (8 : Nat) = 7 + 1 from rfl, LSBReader.readBits, readBit_aligned]
  dsimp only
  rw [show (7 : Nat) = 7 + 0 from rfl, readBits_of_count]
  have h1 : b.toNat >>> 1 >>> 7 = 0 := by
    rw [← Nat.shiftRight_add, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by simpa using hlt)
  have h2 : (if (decide (b.toNat % 2 = 1)) = true then 1 else 0) + 2 * (b.toNat >>> 1 % 2 ^ 7)
      = b.toNat := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one, ite_mod_two]
    omega
  rw [h1]
  dsimp only
  rw [h2]

/-- Splitting a read of `n + m` bits into a read of `n` and then of `m`. -/
theorem readBits_split (n m : Nat) (r : LSBReader) (v1 : Nat) (r1 : LSBReader)
    (v2 : Nat) (r2 : LSBReader) (h1 : r.readBits n = some (v1, r1))
    (h2 : r1.readBits m = some (v2, r2)) :
    r.readBits (n + m) = some (v1 + 2 ^ n * v2, r2) := by
  induction n generalizing r v1 with
  | zero =>
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simpa using h2
  | succ n ih =>
    rw [Nat.succ_add, LSBReader.readBits]
    rw [LSBReader.readBits] at h1
    cases hb : r.readBit with
    | none => simp [hb] at h1
    | some p =>
      obtain ⟨b, r'⟩ := p
      rw [hb] at h1
      dsimp only at h1 ⊢
      cases hr : r'.readBits n with
      | none => rw [hr] at h1; simp at h1
      | some q =>
        obtain ⟨v, r''⟩ := q
        rw [hr] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rw [ih r' v hr]
        simp only [Option.some.injEq, Prod.mk.injEq, and_true]
        have hp : 2 ^ (n + 1) * v2 = 2 * (2 ^ n * v2) := by
          rw [Nat.pow_succ']; exact Nat.mul_assoc 2 (2 ^ n) v2
        rw [hp]
        omega

/-- Reading two bytes at a byte boundary, little-endian. -/
theorem readBits16_aligned (b0 b1 : UInt8) (rest : List UInt8) (t : Nat) :
    LSBReader.readBits ⟨0, 0, b0 :: b1 :: rest, t⟩ 16
      = some (b0.toNat + 256 * b1.toNat, ⟨0, 0, rest, t + 16⟩) := by
  have h := readBits_split 8 8 ⟨0, 0, b0 :: b1 :: rest, t⟩ b0.toNat ⟨0, 0, b1 :: rest, t + 8⟩
    b1.toNat ⟨0, 0, rest, t + 8 + 8⟩ (readBits8_aligned b0 _ t) (readBits8_aligned b1 _ (t + 8))
  rw [show (16 : Nat) = 8 + 8 from rfl, h, show (2 : Nat) ^ 8 = 256 from rfl]

theorem alignToByte_eq (v c : Nat) (inp : List UInt8) (t : Nat) :
    LSBReader.alignToByte ⟨v, c, inp, t⟩ = ⟨0, 0, inp, t + c⟩ := rfl

/-- Reading the payload of a stored block. -/
theorem readStoredBytes_aligned (acc chunk rest : List UInt8) (t : Nat) :
    readStoredBytes acc ⟨0, 0, chunk ++ rest, t⟩ chunk.length
      = .ok (acc ++ chunk, ⟨0, 0, rest, t + 8 * chunk.length⟩) := by
  induction chunk generalizing acc t with
  | nil => simp [readStoredBytes]
  | cons b bs ih =>
    have hb : LSBReader.readByte ⟨0, 0, b :: (bs ++ rest), t⟩ = some (b, ⟨0, 0, bs ++ rest, t + 8⟩) := by
      simp [LSBReader.readByte, readBits8_aligned]
    rw [List.cons_append, List.length_cons, readStoredBytes, hb]
    dsimp only
    rw [ih (acc ++ [b]) (t + 8)]
    simp only [List.append_assoc, List.cons_append, List.nil_append, Except.ok.injEq,
      Prod.mk.injEq, LSBReader.mk.injEq, true_and]
    omega

/-- The body of one stored block decodes to its payload. -/
theorem decompressStored_stored (v t : Nat) (chunk rest : List UInt8)
    (h : chunk.length ≤ storedMax) :
    decompressStored ⟨v, 5, storedLenBytes chunk.length ++ (chunk ++ rest), t⟩
      = .ok (chunk, ⟨0, 0, rest, t + 5 + 16 + 16 + 8 * chunk.length⟩) := by
  have hlen : chunk.length < 65536 := by simp [storedMax] at h; omega
  have hn : (65535 ^^^ chunk.length) < 65536 :=
    Nat.xor_lt_two_pow (n := 16) (by decide) (by simpa using hlen)
  have hx : chunk.length ^^^ (65535 ^^^ chunk.length) = 65535 := by
    rw [Nat.xor_comm 65535 chunk.length, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hsize : UInt8.size = 256 := rfl
  rw [decompressStored, alignToByte_eq]
  simp only [storedLenBytes, List.cons_append, List.nil_append]
  rw [readBits16_aligned]
  dsimp only
  rw [readBits16_aligned]
  dsimp only
  have e1 : (UInt8.ofNat (chunk.length % 256)).toNat + 256 * (UInt8.ofNat (chunk.length / 256)).toNat
      = chunk.length := by
    rw [UInt8.toNat_ofNat_of_lt' (by rw [hsize]; omega),
      UInt8.toNat_ofNat_of_lt' (by rw [hsize]; omega)]
    omega
  have e2 : (UInt8.ofNat ((65535 ^^^ chunk.length) % 256)).toNat
      + 256 * (UInt8.ofNat ((65535 ^^^ chunk.length) / 256)).toNat = 65535 ^^^ chunk.length := by
    rw [UInt8.toNat_ofNat_of_lt' (by rw [hsize]; omega),
      UInt8.toNat_ofNat_of_lt' (by rw [hsize]; omega)]
    omega
  rw [e1, e2, hx]
  simp only [Nat.reduceMod, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [readStoredBytes_aligned, List.nil_append]

theorem readBits2_header (v : Nat) (inp : List UInt8) (t : Nat) :
    LSBReader.readBits ⟨v, 7, inp, t⟩ 2 = some (v % 4, ⟨v >>> 2, 5, inp, t + 2⟩) := by
  have h := readBits_of_count v 2 5 inp t
  simpa using h

/-- Decoding one stored block: the payload is appended to the output, and the
reader is left at the byte after the block. -/
theorem decompressBlocks_step (final : Bool) (chunk tail out : List UInt8) (t f : Nat)
    (h : chunk.length ≤ storedMax) :
    decompressBlocks (f + 1) ⟨0, 0, storedBlockBytes final chunk ++ tail, t⟩ out
      = (if final then .ok (out ++ chunk, ⟨0, 0, tail, t + 1 + 2 + 5 + 16 + 16 + 8 * chunk.length⟩)
         else decompressBlocks f ⟨0, 0, tail, t + 1 + 2 + 5 + 16 + 16 + 8 * chunk.length⟩
                (out ++ chunk)) := by
  rw [storedBlockBytes, List.cons_append, List.append_assoc, decompressBlocks, readBit_aligned]
  dsimp only
  rw [readBits2_header]
  dsimp only
  cases final with
  | true =>
    simp only [reduceIte]
    rw [show ((1 : UInt8).toNat) = 1 from rfl, show (1 : Nat) >>> 1 = 0 from rfl,
      show (0 : Nat) % 4 = 0 from rfl]
    rw [decompressBlockBody]
    simp only [↓reduceIte]
    rw [decompressStored_stored _ _ _ _ h]
    simp
  | false =>
    simp only [reduceIte, Bool.false_eq_true]
    rw [show ((0 : UInt8).toNat) = 0 from rfl, show (0 : Nat) >>> 1 = 0 from rfl,
      show (0 : Nat) % 4 = 0 from rfl]
    rw [decompressBlockBody]
    simp only [↓reduceIte]
    rw [decompressStored_stored _ _ _ _ h]
    simp

theorem storedBytes_length_le (data : List UInt8) : data.length ≤ (storedBytes data).length := by
  fun_induction storedBytes data with
  | case1 data hle => simp [storedBlockBytes, storedLenBytes]; omega
  | case2 data hgt ih =>
    simp only [storedBlockBytes, storedLenBytes, List.length_append, List.length_cons,
      List.length_take, List.length_drop] at *
    omega

/-- A stored stream decodes to the data it was built from, leaving the reader at
the byte after the last block. -/
theorem decompressBlocks_storedBytes : ∀ (fuel : Nat) (data rest out : List UInt8) (t : Nat),
    data.length + 1 ≤ fuel →
    ∃ t', decompressBlocks fuel ⟨0, 0, storedBytes data ++ rest, t⟩ out
      = .ok (out ++ data, ⟨0, 0, rest, t'⟩) := by
  intro fuel
  induction fuel with
  | zero => intro data rest out t h; omega
  | succ f ih =>
    intro data rest out t h
    rw [storedBytes]
    split
    · next hle =>
      refine ⟨t + 1 + 2 + 5 + 16 + 16 + 8 * data.length, ?_⟩
      rw [decompressBlocks_step true data rest out t f hle]
      simp
    · next hgt =>
      have hlen : (data.take storedMax).length ≤ storedMax := by
        simp [List.length_take]
        omega
      rw [List.append_assoc, decompressBlocks_step false (data.take storedMax)
        (storedBytes (data.drop storedMax) ++ rest) out t f hlen]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hfuel : (data.drop storedMax).length + 1 ≤ f := by
        simp only [List.length_drop, storedMax] at *
        omega
      obtain ⟨t', ht'⟩ := ih (data.drop storedMax) rest (out ++ data.take storedMax)
        (t + 1 + 2 + 5 + 16 + 16 + 8 * (data.take storedMax).length) hfuel
      refine ⟨t', ?_⟩
      rw [ht', List.append_assoc, List.take_append_drop]

/-- `deflateTake` on a stored stream returns exactly the data and the bytes
after it. -/
theorem deflateTake_storedBytes (data rest : List UInt8) :
    deflateTake (storedBytes data ++ rest) = .ok (data, rest) := by
  have hfuel : data.length + 1 ≤
      (LSBReader.bitsLeft ⟨0, 0, storedBytes data ++ rest, 0⟩) + 1 := by
    have := storedBytes_length_le data
    simp only [LSBReader.bitsLeft, List.length_append]
    omega
  obtain ⟨t', ht'⟩ := decompressBlocks_storedBytes _ data rest [] 0 hfuel
  rw [deflateTake]
  dsimp only
  rw [ht']
  simp

/-- A stored stream is a DEFLATE encoding of its input: the round trip of
`Deflate.decompress` against `compressStored`. -/
theorem decompress_compressStored (data : ByteArray) :
    decompress (compressStored data) = some data := by
  have hbs : (LSBReader.ofByteArray (compressStored data))
      = ⟨0, 0, storedBytes data.data.toList ++ [], 0⟩ := by
    simp [LSBReader.ofByteArray, compressStored, ByteArray_toList_eq]
  have h := deflateTake_storedBytes data.data.toList []
  rw [deflateTake] at h
  dsimp only at h
  simp only [decompress, decompressBlock]
  rw [hbs]
  revert h
  cases hd : decompressBlocks (LSBReader.bitsLeft ⟨0, 0, storedBytes data.data.toList ++ [], 0⟩ + 1)
      ⟨0, 0, storedBytes data.data.toList ++ [], 0⟩ [] with
  | error e => intro h; simp at h
  | ok p =>
    intro h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    simp [h.1]

/-- `compressStored` meets the `Compresses` specification of `Deflate`. -/
theorem compressStored_sound (data : ByteArray) : Compresses data (compressStored data) :=
  decompress_compressStored data

/-! ### The decoder only consumes a prefix

Every reader step leaves the unread input a suffix of what it started with, so
whatever `deflateTake` hands back really is the tail of the stream it was given.
This is what makes a trailer check meaningful: the bytes compared against the
checksum are bytes of the stream. -/

theorem readBit_suffix {r : LSBReader} {b : Bool} {r' : LSBReader}
    (h : r.readBit = some (b, r')) : r'.input <:+ r.input := by
  rcases r with ⟨buf, cnt, inp, tr⟩
  by_cases hc : cnt = 0
  · subst hc
    cases inp with
    | nil => simp [LSBReader.readBit, LSBReader.refill] at h
    | cons x xs =>
      simp [LSBReader.readBit, LSBReader.refill] at h
      rcases h with ⟨-, rfl⟩
      exact ⟨[x], rfl⟩
  · simp [LSBReader.readBit, hc] at h
    rcases h with ⟨-, rfl⟩
    exact List.suffix_rfl

theorem readBits_suffix {r : LSBReader} {n v : Nat} {r' : LSBReader}
    (h : r.readBits n = some (v, r')) : r'.input <:+ r.input := by
  induction n generalizing r v r' with
  | zero =>
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact List.suffix_rfl
  | succ n ih =>
    rw [LSBReader.readBits] at h
    cases hb : r.readBit with
    | none => rw [hb] at h; simp at h
    | some p =>
      obtain ⟨b, r1⟩ := p
      rw [hb] at h
      dsimp only at h
      cases hr : r1.readBits n with
      | none => rw [hr] at h; simp at h
      | some q =>
        obtain ⟨v1, r2⟩ := q
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact (ih hr).trans (readBit_suffix hb)

theorem readStoredBytes_suffix {acc : List UInt8} {r : LSBReader} {n : Nat}
    {out : List UInt8} {r' : LSBReader} (h : readStoredBytes acc r n = .ok (out, r')) :
    r'.input <:+ r.input := by
  induction n generalizing acc r r' out with
  | zero =>
    simp only [readStoredBytes, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact List.suffix_rfl
  | succ n ih =>
    rw [readStoredBytes] at h
    cases hb : r.readByte with
    | none => rw [hb] at h; simp at h
    | some p =>
      obtain ⟨b, r1⟩ := p
      rw [hb] at h
      dsimp only at h
      have hr1 : r1.input <:+ r.input := by
        unfold LSBReader.readByte at hb
        cases hv : r.readBits 8 with
        | none => rw [hv] at hb; simp at hb
        | some q =>
          obtain ⟨v, r2⟩ := q
          rw [hv] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          rw [← hb.2]
          exact readBits_suffix hv
      exact (ih h).trans hr1

theorem decompressStored_suffix {r : LSBReader} {out : List UInt8} {r' : LSBReader}
    (h : decompressStored r = .ok (out, r')) : r'.input <:+ r.input := by
  unfold decompressStored at h
  dsimp only at h
  cases h1 : (r.alignToByte).readBits 16 with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨len, r1⟩ := p
    rw [h1] at h
    dsimp only at h
    cases h2 : r1.readBits 16 with
    | none => rw [h2] at h; simp at h
    | some q =>
      obtain ⟨nlen, r2⟩ := q
      rw [h2] at h
      dsimp only at h
      split at h
      · simp at h
      · have ha : (r.alignToByte).input = r.input := rfl
        exact ((readStoredBytes_suffix h).trans (readBits_suffix h2)).trans
          (ha ▸ readBits_suffix h1)

theorem decodeSymbolLSBAux_suffix {entries : List CodeEntry} {r : LSBReader}
    {code len maxIter sym : Nat} {r' : LSBReader}
    (h : decodeSymbolLSBAux entries r code len maxIter = some (sym, r')) :
    r'.input <:+ r.input := by
  induction maxIter generalizing r code len r' sym with
  | zero => simp [decodeSymbolLSBAux] at h
  | succ n ih =>
    rw [decodeSymbolLSBAux] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact List.suffix_rfl
    · cases hb : r.readBit with
      | none => rw [hb] at h; simp at h
      | some p =>
        obtain ⟨b, r1⟩ := p
        rw [hb] at h
        dsimp only at h
        exact (ih h).trans (readBit_suffix hb)

theorem readSymbolLSB_suffix {t : HuffmanTable} {r : LSBReader} {sym : Nat} {r' : LSBReader}
    (h : t.readSymbolLSB r = some (sym, r')) : r'.input <:+ r.input :=
  decodeSymbolLSBAux_suffix h

theorem decodeStep_suffix {litLen dist : HuffmanTable} {r : LSBReader} {output : List UInt8}
    {st : SymbolStep} (h : decodeStep litLen dist r output = .ok st) :
    (stepReader st).input <:+ r.input := by
  unfold decodeStep at h
  cases h0 : litLen.readSymbolLSB r with
  | none => rw [h0] at h; simp at h
  | some p =>
    obtain ⟨sym, r1⟩ := p
    rw [h0] at h
    dsimp only at h
    have hs1 : r1.input <:+ r.input := readSymbolLSB_suffix h0
    split at h
    · simp only [Except.ok.injEq] at h; rw [← h]; exact hs1
    · split at h
      · simp only [Except.ok.injEq] at h; rw [← h]; exact hs1
      · split at h
        · cases h2 : r1.readBits (lengthExtraBits.getD (sym - 257) 0) with
          | none => rw [h2] at h; simp at h
          | some q =>
            obtain ⟨ev, r2⟩ := q
            rw [h2] at h
            dsimp only at h
            cases h3 : dist.readSymbolLSB r2 with
            | none => rw [h3] at h; simp at h
            | some u =>
              obtain ⟨ds, r3⟩ := u
              rw [h3] at h
              dsimp only at h
              split at h
              · simp at h
              · cases h4 : r3.readBits (distanceExtraBits.getD ds 0) with
                | none => rw [h4] at h; simp at h
                | some w =>
                  obtain ⟨dv, r4⟩ := w
                  rw [h4] at h
                  dsimp only at h
                  split at h
                  · simp at h
                  · simp only [Except.ok.injEq] at h
                    rw [← h]
                    exact (((readBits_suffix h4).trans (readSymbolLSB_suffix h3)).trans
                      (readBits_suffix h2)).trans hs1
        · simp at h

theorem decodeSymbolsFuel_suffix {litLen dist : HuffmanTable} :
    ∀ {fuel : Nat} {r : LSBReader} {output out : List UInt8} {r' : LSBReader},
      decodeSymbolsFuel litLen dist fuel r output = .ok (out, r') → r'.input <:+ r.input := by
  intro fuel
  induction fuel with
  | zero => intro r output out r' h; simp [decodeSymbolsFuel] at h
  | succ f ih =>
    intro r output out r' h
    rw [decodeSymbolsFuel] at h
    cases hs : decodeStep litLen dist r output with
    | error e => rw [hs] at h; simp at h
    | ok st =>
      have hsuf := decodeStep_suffix hs
      rw [hs] at h
      cases st with
      | done o rr =>
        dsimp only at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact hsuf
      | more o rr =>
        dsimp only at h
        exact (ih h).trans hsuf

theorem decodeSymbol_suffix {litLen dist : HuffmanTable} {r : LSBReader} {output out : List UInt8}
    {r' : LSBReader} (h : decodeSymbol litLen dist r output = .ok (out, r')) :
    r'.input <:+ r.input :=
  decodeSymbolsFuel_suffix h

theorem readCLLengths_suffix :
    ∀ {n i : Nat} {acc lens : List Nat} {r r' : LSBReader},
      readCLLengths n i acc r = .ok (lens, r') → r'.input <:+ r.input := by
  intro n
  induction n with
  | zero =>
    intro i acc lens r r' h
    rw [readCLLengths] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact List.suffix_refl _
  | succ n ih =>
    intro i acc lens r r' h
    rw [readCLLengths] at h
    cases hb : r.readBits 3 with
    | none => rw [hb] at h; simp at h
    | some p =>
      obtain ⟨v, r1⟩ := p
      rw [hb] at h
      exact (ih h).trans (readBits_suffix hb)

theorem readCodeLengths_suffix {clTable : HuffmanTable} {total : Nat} :
    ∀ {fuel : Nat} {acc lens : List Nat} {r r' : LSBReader},
      readCodeLengths clTable total fuel acc r = .ok (lens, r') → r'.input <:+ r.input := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc lens r r' h
    rw [readCodeLengths] at h
    by_cases he : acc.length = total
    · rw [ite_eq_left he] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact List.suffix_refl _
    · rw [ite_eq_right he] at h; simp at h
  | succ f ih =>
    intro acc lens r r' h
    rw [readCodeLengths] at h
    by_cases hdone : total ≤ acc.length
    · rw [ite_eq_left hdone] at h
      by_cases he : acc.length = total
      · rw [ite_eq_left he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact List.suffix_refl _
      · rw [ite_eq_right he] at h; simp at h
    · rw [ite_eq_right hdone] at h
      cases hs : clTable.readSymbolLSB r with
      | none => rw [hs] at h; simp at h
      | some p =>
        obtain ⟨sym, r1⟩ := p
        rw [hs] at h
        dsimp only at h
        have hs1 : r1.input <:+ r.input := readSymbolLSB_suffix hs
        by_cases hlt : sym < 16
        · rw [ite_eq_left hlt] at h
          exact (ih h).trans hs1
        · rw [ite_eq_right hlt] at h
          by_cases h16 : sym = 16
          · rw [ite_eq_left h16] at h
            cases hl : acc.getLast? with
            | none => rw [hl] at h; simp at h
            | some prev =>
              rw [hl] at h
              dsimp only at h
              cases he : r1.readBits 2 with
              | none => rw [he] at h; simp at h
              | some q =>
                obtain ⟨e, r2⟩ := q
                rw [he] at h
                dsimp only at h
                exact ((ih h).trans (readBits_suffix he)).trans hs1
          · rw [ite_eq_right h16] at h
            by_cases h17 : sym = 17
            · rw [ite_eq_left h17] at h
              cases he : r1.readBits 3 with
              | none => rw [he] at h; simp at h
              | some q =>
                obtain ⟨e, r2⟩ := q
                rw [he] at h
                dsimp only at h
                exact ((ih h).trans (readBits_suffix he)).trans hs1
            · rw [ite_eq_right h17] at h
              by_cases h18 : sym = 18
              · rw [ite_eq_left h18] at h
                cases he : r1.readBits 7 with
                | none => rw [he] at h; simp at h
                | some q =>
                  obtain ⟨e, r2⟩ := q
                  rw [he] at h
                  dsimp only at h
                  exact ((ih h).trans (readBits_suffix he)).trans hs1
              · rw [ite_eq_right h18] at h; simp at h

theorem readDynamicTables_suffix {r : LSBReader} {lt dt : HuffmanTable} {r' : LSBReader}
    (h : readDynamicTables r = .ok (lt, dt, r')) : r'.input <:+ r.input := by
  rw [readDynamicTables] at h
  cases h1 : r.readBits 5 with
  | none => rw [h1] at h; simp at h
  | some p1 =>
    obtain ⟨hlit, r1⟩ := p1
    rw [h1] at h
    dsimp only at h
    have hs1 : r1.input <:+ r.input := readBits_suffix h1
    cases h2 : r1.readBits 5 with
    | none => rw [h2] at h; simp at h
    | some p2 =>
      obtain ⟨hdist, r2⟩ := p2
      rw [h2] at h
      dsimp only at h
      have hs2 : r2.input <:+ r.input := (readBits_suffix h2).trans hs1
      cases h3 : r2.readBits 4 with
      | none => rw [h3] at h; simp at h
      | some p3 =>
        obtain ⟨hclen, r3⟩ := p3
        rw [h3] at h
        dsimp only at h
        have hs3 : r3.input <:+ r.input := (readBits_suffix h3).trans hs2
        split at h
        · simp at h
        · cases h4 : readCLLengths (hclen + 4) 0 (List.replicate 19 0) r3 with
          | error e => rw [h4] at h; simp at h
          | ok u =>
            obtain ⟨clLens, r4⟩ := u
            rw [h4] at h
            dsimp only at h
            have hs4 : r4.input <:+ r.input := (readCLLengths_suffix h4).trans hs3
            split at h
            · simp at h
            · cases h5 : HuffmanTable.ofLengths clLens 7 with
              | none => rw [h5] at h; simp at h
              | some clTable =>
                rw [h5] at h
                dsimp only at h
                cases h6 : readCodeLengths clTable (hlit + 257 + (hdist + 1))
                    (hlit + 257 + (hdist + 1) + 1) [] r4 with
                | error e => rw [h6] at h; simp at h
                | ok w =>
                  obtain ⟨lens, r5⟩ := w
                  rw [h6] at h
                  dsimp only at h
                  have hs5 : r5.input <:+ r.input := (readCodeLengths_suffix h6).trans hs4
                  split at h
                  · simp at h
                  · split at h
                    · simp at h
                    · split at h
                      · simp at h
                      · split at h
                        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                          rw [← h.2.2]
                          exact hs5
                        · simp at h

/-- Every block body leaves the reader on a suffix of its input. -/
theorem decompressBlockBody_suffix {btype : Nat} {r : LSBReader} {out res : List UInt8}
    {r' : LSBReader} (h : decompressBlockBody btype r out = .ok (res, r')) :
    r'.input <:+ r.input := by
  rw [decompressBlockBody] at h
  split at h
  · cases hd : decompressStored r with
    | error e => rw [hd] at h; simp at h
    | ok u =>
      obtain ⟨bytes, r1⟩ := u
      rw [hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact decompressStored_suffix hd
  · split at h
    · cases hf1 : fixedLitLenTable with
      | none => rw [hf1] at h; simp at h
      | some lt =>
        cases hf2 : fixedDistTable with
        | none => rw [hf1, hf2] at h; simp at h
        | some dt =>
          rw [hf1, hf2] at h
          exact decodeSymbol_suffix h
    · split at h
      · cases hdt : readDynamicTables r with
        | error e => rw [hdt] at h; simp at h
        | ok u =>
          obtain ⟨lt, dt, r1⟩ := u
          rw [hdt] at h
          dsimp only at h
          exact (decodeSymbol_suffix h).trans (readDynamicTables_suffix hdt)
      · simp at h

set_option maxRecDepth 4000 in
theorem decompressBlocks_suffix :
    ∀ {fuel : Nat} {r : LSBReader} {out res : List UInt8} {r' : LSBReader},
      decompressBlocks fuel r out = .ok (res, r') → r'.input <:+ r.input := by
  intro fuel
  induction fuel with
  | zero => intro r out res r' h; simp [decompressBlocks] at h
  | succ f ih =>
    intro r out res r' h
    rw [decompressBlocks] at h
    cases hb : r.readBit with
    | none => rw [hb] at h; simp at h
    | some p =>
      obtain ⟨bfinal, r1⟩ := p
      rw [hb] at h
      dsimp only at h
      have hs1 : r1.input <:+ r.input := readBit_suffix hb
      cases h2 : r1.readBits 2 with
      | none => rw [h2] at h; simp at h
      | some q =>
        obtain ⟨btype, r2⟩ := q
        rw [h2] at h
        dsimp only at h
        have hs2 : r2.input <:+ r.input := (readBits_suffix h2).trans hs1
        cases hbody : decompressBlockBody btype r2 out with
        | error e => rw [hbody] at h; simp at h
        | ok u =>
          obtain ⟨out', r3⟩ := u
          rw [hbody] at h
          dsimp only at h
          have hs3 : r3.input <:+ r.input := (decompressBlockBody_suffix hbody).trans hs2
          cases bfinal with
          | true =>
            simp only [reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2]
            exact hs3
          | false =>
            simp only [Bool.false_eq_true, reduceIte] at h
            exact (ih h).trans hs3

/-- Whatever `deflateTake` returns as the remainder really is a suffix of its
input: the decoder consumes a prefix and stops. -/
theorem deflateTake_suffix {bs out rest : List UInt8} (h : deflateTake bs = .ok (out, rest)) :
    rest <:+ bs := by
  rw [deflateTake] at h
  dsimp only at h
  cases hd : decompressBlocks (LSBReader.bitsLeft ⟨0, 0, bs, 0⟩ + 1) ⟨0, 0, bs, 0⟩ [] with
  | error e => rw [hd] at h; simp at h
  | ok p =>
    obtain ⟨o, r'⟩ := p
    rw [hd] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact decompressBlocks_suffix hd

end Silmaril.Formats.Compression.Deflate
