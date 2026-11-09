module

public import Silmaril.Formats.Compression.Inflate.Stream.Bits
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
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamFacts
public import Silmaril.Raw.Formats.Compression.Deflate.HuffmanLemmas
public import Silmaril.Raw.Formats.Compression.Deflate.StoredWriter
public import Silmaril.Raw.Formats.Compression.Deflate.RoundTrip
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32Spec
public import Silmaril.Raw.Formats.Compression.Zlib.DictionaryHistory
public import Silmaril.Raw.Formats.Compression.Vectors

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.Bits`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

namespace Reservoir

end Reservoir

namespace Reservoir

end Reservoir

namespace Reservoir

/-! ## Bit-list arithmetic and refill -/

theorem natBits_mod (v n : Nat) : natBits (v % 2 ^ n) n = natBits v n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [natBits, natBits, Nat.pow_succ']
    rw [Nat.mod_mod_of_dvd _ (by exact ⟨2 ^ n, rfl⟩), Nat.mod_mul_right_div_self, ih]

theorem natBits_add_mul (lo hi n m : Nat) (hlo : lo < 2 ^ n) :
    natBits (lo + hi * 2 ^ n) (n + m) = natBits lo n ++ natBits hi m := by
  rw [natBits_append, ← natBits_mod (lo + hi * 2 ^ n) n,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlo, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlo, Nat.zero_add]

theorem ofBytes_valid (bytes : List UInt8) : (ofBytes bytes).Valid := by
  simp [ofBytes, Valid]

theorem ofBytes_unread (bytes : List UInt8) : (ofBytes bytes).unread = bytesBits bytes := rfl

theorem feed_valid {s : Reservoir} (h : s.Valid) (bytes : List UInt8) :
    (s.feed bytes).Valid := h

theorem feed_unread (s : Reservoir) (bytes : List UInt8) :
    (s.feed bytes).unread = s.unread ++ bytesBits bytes := by
  simp [feed, unread, bytesBits, List.flatMap_append, List.append_assoc]

theorem pullByte_valid {s t : Reservoir} (hs : s.Valid) (h : s.pullByte = some t) : t.Valid := by
  cases hi : s.input with
  | nil => simp [pullByte, hi] at h
  | cons byte rest =>
    simp only [pullByte, hi, Option.some.injEq] at h
    subst t
    have hb : byte.toNat + 1 ≤ 256 := by have := byte.toNat_lt; omega
    change s.hold + byte.toNat * 2 ^ s.bits < 2 ^ (s.bits + 8)
    calc
      _ < 2 ^ s.bits + byte.toNat * 2 ^ s.bits := Nat.add_lt_add_right hs _
      _ = (byte.toNat + 1) * 2 ^ s.bits := by simp [Nat.add_mul, Nat.add_comm]
      _ ≤ 256 * 2 ^ s.bits := Nat.mul_le_mul_right _ hb
      _ = _ := by rw [Nat.pow_add]; simp [Nat.mul_comm]

theorem pullByte_unread {s t : Reservoir} (hs : s.Valid) (h : s.pullByte = some t) :
    t.unread = s.unread := by
  cases hi : s.input with
  | nil => simp [pullByte, hi] at h
  | cons byte rest =>
    simp only [pullByte, hi, Option.some.injEq] at h
    subst t
    simp only [unread, natBits_add_mul _ _ _ _ hs, hi, bytesBits, List.flatMap_cons,
      List.append_assoc]

theorem pullByte_consumed {s t : Reservoir} (h : s.pullByte = some t) :
    t.consumed = s.consumed := by
  cases hi : s.input <;> simp [pullByte, hi] at h
  subst t
  rfl

theorem pullByte_bits_mod {s t : Reservoir} (h : s.pullByte = some t) :
    t.bits % 8 = s.bits % 8 := by
  cases hi : s.input <;> simp [pullByte, hi] at h
  subst t
  simp

/-! ## Consuming and byte alignment -/

theorem lowBits_lt (s : Reservoir) (n : Nat) : s.lowBits n < 2 ^ n :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem dropBits_valid {s : Reservoir} (hs : s.Valid) {n : Nat} (hn : n ≤ s.bits) :
    (s.dropBits n).Valid := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).mpr
  change s.hold < 2 ^ (s.bits - n) * 2 ^ n
  rw [← Nat.pow_add, Nat.sub_add_cancel hn]
  exact hs

theorem unread_split (s : Reservoir) {n : Nat} (hn : n ≤ s.bits) :
    s.unread = natBits (s.lowBits n) n ++ (s.dropBits n).unread := by
  simp only [unread, lowBits, dropBits, natBits_mod]
  rw [← List.append_assoc, ← natBits_append, Nat.add_sub_of_le hn]

theorem dropBits_unread (s : Reservoir) {n : Nat} (hn : n ≤ s.bits) :
    (s.dropBits n).unread = s.unread.drop n := by
  rw [unread_split s hn, List.drop_append_of_le_length (by simp)]
  simp

theorem byteBits_valid {s : Reservoir} (hs : s.Valid) : s.byteBits.Valid :=
  dropBits_valid hs (Nat.mod_le _ _)

theorem byteBits_unread (s : Reservoir) :
    s.byteBits.unread = s.unread.drop (s.bits % 8) :=
  dropBits_unread s (Nat.mod_le _ _)

theorem byteBits_bits (s : Reservoir) : s.byteBits.bits = 8 * (s.bits / 8) := by
  have := Nat.mod_add_div s.bits 8
  simp only [byteBits, dropBits]
  omega

theorem byteBits_bits_mod (s : Reservoir) : s.byteBits.bits % 8 = 0 := by
  rw [byteBits_bits]
  omega

theorem byteBits_input (s : Reservoir) : s.byteBits.input = s.input := rfl

/-! ## `NEEDBITS` contracts -/

theorem needBitsAux_sound (required consumed : Nat) (input : List UInt8) (hold bits : Nat)
    (hs : (⟨hold, bits, input, consumed⟩ : Reservoir).Valid) :
    NeedSound required ⟨hold, bits, input, consumed⟩
      (needBitsAux required consumed input hold bits) := by
  induction input generalizing hold bits with
  | nil =>
    unfold needBitsAux
    split <;> simp_all [NeedSound, NeedResult.state]
  | cons byte rest ih =>
    unfold needBitsAux
    split
    · simp_all [NeedSound, NeedResult.state]
    · have hp : (⟨hold, bits, byte :: rest, consumed⟩ : Reservoir).pullByte =
          some ⟨hold + byte.toNat * 2 ^ bits, bits + 8, rest, consumed⟩ := rfl
      have next := ih (hold + byte.toNat * 2 ^ bits) (bits + 8) (pullByte_valid hs hp)
      rcases next with ⟨hv, hu, hc, hm, status⟩
      refine ⟨hv, hu.trans (pullByte_unread hs hp), hc, ?_, status⟩
      exact hm.trans (pullByte_bits_mod hp)

theorem needBits_sound (required : Nat) {s : Reservoir} (hs : s.Valid) :
    NeedSound required s (needBits required s) := by
  exact needBitsAux_sound required s.consumed s.input s.hold s.bits hs

theorem needBitsAux_ready (required consumed : Nat) (input : List UInt8) (hold bits : Nat)
    (enough : required ≤ bits) :
    needBitsAux required consumed input hold bits = .ready ⟨hold, bits, input, consumed⟩ := by
  cases input <;> simp only [needBitsAux, enough, ite_true]

theorem needBits_ready {required : Nat} {s : Reservoir} (enough : required ≤ s.bits) :
    needBits required s = .ready s :=
  needBitsAux_ready required s.consumed s.input s.hold s.bits enough

theorem needBitsAux_append (required consumed : Nat) (input added : List UInt8)
    (hold bits : Nat) :
    needBitsAux required consumed (input ++ added) hold bits =
      match needBitsAux required consumed input hold bits with
      | .ready state => .ready (state.feed added)
      | .needInput state => needBits required (state.feed added) := by
  induction input generalizing hold bits with
  | nil =>
    by_cases enough : required ≤ bits
    · rw [needBitsAux_ready _ _ _ _ _ enough]
      simp only [needBitsAux, enough, ite_true]
      rfl
    · simp only [List.nil_append, needBitsAux, enough, ite_false]
      rfl
  | cons byte rest ih =>
    simp only [List.cons_append, needBitsAux]
    by_cases enough : required ≤ bits
    · simp only [enough, ite_true]
      rfl
    · simp only [enough, ite_false]
      exact ih _ _

/-- Exact resumability: adding a later chunk after partial refill has the same
result as making that chunk available from the start. -/
theorem needBits_feed (required : Nat) (s : Reservoir) (added : List UInt8) :
    needBits required (s.feed added) =
      match needBits required s with
      | .ready state => .ready (state.feed added)
      | .needInput state => needBits required (state.feed added) :=
  needBitsAux_append required s.consumed s.input added s.hold s.bits

theorem readBits_sound (n : Nat) {s : Reservoir} (hs : s.Valid) :
    ReadSound n s (readBits n s) := by
  have hn := needBits_sound n hs
  cases he : needBits n s with
  | ready filled =>
    rw [he] at hn
    simp only [NeedSound, NeedResult.state] at hn
    rcases hn with ⟨hv, hu, hc, hm, enough⟩
    simp only [readBits, he, ReadSound]
    refine ⟨dropBits_valid hv enough, lowBits_lt _ _, ?_, ?_, ?_⟩
    · exact hu.symm.trans (unread_split filled enough)
    · change filled.consumed + n = s.consumed + n
      rw [hc]
    · change (filled.bits - n) % 8 = (s.bits + 7 * n) % 8
      omega
  | needInput filled =>
    rw [he] at hn
    simpa only [readBits, he, ReadSound, NeedSound, NeedResult.state] using hn

/-! ## An explicit canonical-reader normalization -/

theorem bufferedBytes_bits (n v : Nat) :
    bytesBits (bufferedBytes n v) = natBits v (8 * n) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [bufferedBytes, bytesBits, List.flatMap_cons]
    rw [show (UInt8.ofNat v).toNat = v % 2 ^ 8 by rfl, natBits_mod]
    change natBits v 8 ++ bytesBits (bufferedBytes n (v / 256)) = _
    rw [ih, show 8 * (n + 1) = 8 + 8 * n by omega, natBits_append]

theorem normalize_correct {s : Reservoir} (hs : s.Valid) : Normalizes s s.normalize := by
  refine ⟨hs, rfl, ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩, rfl⟩
  change natBits (s.hold % 2 ^ (s.bits % 8)) (s.bits % 8) ++
    bytesBits (bufferedBytes (s.bits / 8) (s.hold / 2 ^ (s.bits % 8)) ++ s.input) = s.unread
  rw [natBits_mod]
  simp only [bytesBits, List.flatMap_append]
  change natBits s.hold (s.bits % 8) ++
    (bytesBits (bufferedBytes (s.bits / 8) (s.hold / 2 ^ (s.bits % 8))) ++ bytesBits s.input) = _
  rw [bufferedBytes_bits, ← List.append_assoc, ← natBits_append]
  congr 2
  exact Nat.mod_add_div s.bits 8

theorem Normalizes.count_lt {s : Reservoir} {r : LSBReader} (h : Normalizes s r) :
    r.count < 8 := by rw [h.2.1]; omega

theorem Normalizes.pullByte {s t : Reservoir} {r : LSBReader}
    (h : Normalizes s r) (hp : s.pullByte = some t) : Normalizes t r := by
  refine ⟨pullByte_valid h.1 hp, h.2.1.trans (pullByte_bits_mod hp).symm, ?_, ?_⟩
  · rw [pullByte_unread h.1 hp]
    exact h.2.2.1
  · exact h.2.2.2.trans (pullByte_consumed hp).symm

theorem Normalizes.feed {s : Reservoir} {r : LSBReader}
    (h : Normalizes s r) (added : List UInt8) :
    Normalizes (s.feed added) { r with input := r.input ++ added } := by
  refine ⟨feed_valid h.1 _, h.2.1, ⟨h.2.2.1.1, ?_⟩, h.2.2.2⟩
  rw [feed_unread, ← h.2.2.1.2]
  simp only [bytesBits, List.flatMap_append, List.append_assoc]

theorem Normalizes.needBits {s : Reservoir} {r : LSBReader}
    (h : Normalizes s r) (required : Nat) :
    Normalizes (needBits required s).state r := by
  obtain ⟨hv, hu, hc, hm, _⟩ := needBits_sound required h.1
  refine ⟨hv, h.2.1.trans hm.symm, ?_, h.2.2.2.trans hc.symm⟩
  rw [hu]
  exact h.2.2.1

/-- Successful reservoir reads are successful canonical-reader reads with the
same value and position, and their resulting representations remain related.
This equality concerns reader observations, not physical accumulator records. -/
theorem Normalizes.readBits {s t : Reservoir} {r : LSBReader} {n value : Nat}
    (h : Normalizes s r) (hr : readBits n s = .value value t) :
    ∃ r', r.readBits n = some (value, r') ∧ Normalizes t r' := by
  have sound := readBits_sound n h.1
  rw [hr] at sound
  rcases sound with ⟨hv, hvalue, hu, hc, hm⟩
  have rep : r.Rep (natBits value n ++ t.unread) := by
    rw [← hu]
    exact h.2.2.1
  obtain ⟨r', read, rest⟩ := rep.readBits
  rw [Nat.mod_eq_of_lt hvalue] at read
  refine ⟨r', read, hv, ?_, rest, ?_⟩
  · have count := LSBReader.readBits_count n h.count_lt read
    rw [h.2.1] at count
    omega
  · rw [LSBReader.readBits_totalRead read, h.2.2.2, hc]

theorem Normalizes.readBits_needInput {s t : Reservoir} {r : LSBReader} {n : Nat}
    (h : Normalizes s r) (hr : Reservoir.readBits n s = .needInput t) : Normalizes t r := by
  have sound := readBits_sound n h.1
  rw [hr] at sound
  rcases sound with ⟨hv, hu, hc, hm, _, _⟩
  refine ⟨hv, h.2.1.trans hm.symm, ?_, h.2.2.2.trans hc.symm⟩
  rw [hu]
  exact h.2.2.1

theorem Normalizes.byteBits {s : Reservoir} {r : LSBReader} (h : Normalizes s r) :
    Normalizes s.byteBits r.alignToByte := by
  refine ⟨byteBits_valid h.1, ?_, ?_, ?_⟩
  · change 0 = s.byteBits.bits % 8
    exact (byteBits_bits_mod s).symm
  · rw [byteBits_unread, ← h.2.1]
    exact h.2.2.1.alignToByte
  · change r.totalRead + r.count = s.consumed + s.bits % 8
    rw [h.2.2.2, h.2.1]

/-! ## Successful canonical reads remain valid after input extension -/

@[simp] theorem readerFeed_nil (r : LSBReader) : readerFeed r [] = r := by
  simp [readerFeed]

theorem readerFeed_readBit {r r' : LSBReader} {bit : Bool}
    (h : r.readBit = some (bit, r')) (added : List UInt8) :
    (readerFeed r added).readBit = some (bit, readerFeed r' added) := by
  by_cases empty : r.count = 0
  · cases input : r.input with
    | nil => simp [LSBReader.readBit, LSBReader.refill, empty, input] at h
    | cons byte rest =>
      simp only [LSBReader.readBit, empty, ite_true, LSBReader.refill, input,
        Nat.reduceEqDiff, ite_false, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [readerFeed, LSBReader.readBit, empty, ite_true, LSBReader.refill,
        input, List.cons_append, Nat.reduceEqDiff, ite_false]
  · simp only [LSBReader.readBit, empty, ite_false,
      Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [readerFeed, LSBReader.readBit, empty, ite_false]
    rfl

theorem readerFeed_readBits (n : Nat) {r r' : LSBReader} {value : Nat}
    (h : r.readBits n = some (value, r')) (added : List UInt8) :
    (readerFeed r added).readBits n = some (value, readerFeed r' added) := by
  induction n generalizing r r' value with
  | zero =>
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | succ n ih =>
    simp only [LSBReader.readBits] at h
    cases hb : r.readBit with
    | none => simp only [hb, reduceCtorEq] at h
    | some pair =>
      rcases pair with ⟨bit, middle⟩
      cases hr : middle.readBits n with
      | none => simp only [hb, hr, reduceCtorEq] at h
      | some pair =>
        rcases pair with ⟨rest, final⟩
        simp only [hb, hr, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [LSBReader.readBits, readerFeed_readBit hb, ih hr]

/-! ## Non-vacuous boundary examples -/

/-- `BYTEBITS` keeps two already-prefetched bytes instead of discarding them. -/
theorem byteBits_retains_prefetched :
    (⟨0x12345, 19, [], 5⟩ : Reservoir).byteBits = ⟨0x2468, 16, [], 8⟩ := by decide

/-- Exhaustion retains the pulled byte, ready for a later `feed`. -/
theorem needBits_suspends_after_partial_refill :
    needBits 16 (ofBytes [0x41]) = .needInput ⟨0x41, 8, [], 0⟩ := by decide

/-- Normalization moves the complete prefetched bytes into canonical input. -/
theorem normalize_retains_prefetched :
    (⟨0x12345, 19, [], 5⟩ : Reservoir).normalize.input = [0x68, 0x24] := by decide

end Reservoir
end Silmaril.Formats.Compression.Inflate.Stream
