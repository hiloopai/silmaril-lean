module

public import Silmaril.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Formats.Compression.Bits.Bitstream

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Bits.BitstreamLemmas`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

theorem ByteArray_toList_loop_eq (b : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r hlt ih =>
    have hi : i < b.data.toList.length := by simpa using hlt
    rw [ih, List.drop_eq_getElem_cons hi]
    have hget : b.get! i = b.data.toList[i] := by
      simp [ByteArray.get!, getElem!_pos, hlt]
    simp [hget]
  | case2 i r hlt =>
    have hle : b.data.toList.length ≤ i := by simpa using Nat.le_of_not_lt hlt
    simp [List.drop_eq_nil_of_le hle]

theorem ByteArray_toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  simp [ByteArray.toList, ByteArray_toList_loop_eq]

@[simp] theorem length_natBits (v n : Nat) : (natBits v n).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [natBits, ih]

@[simp] theorem length_msbBits (c n : Nat) : (msbBits c n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [msbBits, ih]

@[simp] theorem length_bytesBits (bs : List UInt8) : (bytesBits bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bytesBits] at *; omega

theorem natBits_append (v n m : Nat) :
    natBits v (n + m) = natBits v n ++ natBits (v / 2 ^ n) m := by
  induction n generalizing v with
  | zero => simp [natBits]
  | succ n ih =>
    rw [Nat.add_right_comm, natBits, natBits, ih, Nat.pow_succ', Nat.div_div_eq_div_mul]
    simp

theorem natBits_add_high (v n : Nat) (b : Bool) (hv : v < 2 ^ n) :
    natBits (v + (if b then 2 ^ n else 0)) (n + 1) = natBits v n ++ [b] := by
  induction n generalizing v with
  | zero =>
    have : v = 0 := by omega
    subst this
    cases b <;> simp [natBits]
  | succ n ih =>
    have h2 : v / 2 < 2 ^ n := by rw [Nat.pow_succ] at hv; omega
    have hmod : (v + (if b then 2 ^ (n + 1) else 0)) % 2 = v % 2 := by
      cases b <;> simp [Nat.pow_succ, Nat.add_mul_mod_self_right]
    have hdiv : (v + (if b then 2 ^ (n + 1) else 0)) / 2 = v / 2 + (if b then 2 ^ n else 0) := by
      cases b <;> simp [Nat.pow_succ]; omega
    rw [natBits, hmod, hdiv, ih _ h2, natBits]
    rfl

theorem LSBWriter.rep_empty : LSBWriter.empty.Rep [] := by
  refine ⟨by decide, by decide, ?_⟩
  rfl

theorem LSBWriter.Rep.writeBit {w : LSBWriter} {bs : List Bool} (h : w.Rep bs) (b : Bool) :
    (w.writeBit b).Rep (bs ++ [b]) := by
  rcases w with ⟨buf, cnt, bytes, tb⟩
  obtain ⟨hc, hb, hbs⟩ := h
  simp only at hc hb hbs
  have hshift : (1 <<< cnt) = 2 ^ cnt := by simp [Nat.shiftLeft_eq]
  have hlt : buf + (if b then 2 ^ cnt else 0) < 2 ^ (cnt + 1) := by
    rw [Nat.pow_succ]; cases b <;> simp <;> omega
  have hbits := natBits_add_high buf cnt b hb
  generalize hnb : buf + (if b then 2 ^ cnt else 0) = nb at hlt hbits
  unfold LSBWriter.writeBit
  simp only [hshift, hnb]
  split
  · exact ⟨by assumption, hlt, by simp only; rw [hbits, ← hbs, List.append_assoc]⟩
  · have h7 : cnt = 7 := by omega
    subst h7
    have h256 : nb < 256 := by simpa using hlt
    have hsh : nb >>> 8 = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt h256
    have hb' : (UInt8.ofNat (nb % 256)).toNat = nb := by simp [Nat.mod_eq_of_lt h256]
    have h0 : natBits 0 (7 + 1 - 8) = [] := rfl
    refine ⟨by simp, by simp [hsh], ?_⟩
    simp only [hsh, ByteArray.data_push, Array.toList_push, bytesBits, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, hb', h0]
    rw [← hbs, List.append_assoc, ← hbits]
    rfl

theorem LSBWriter.Rep.writeVal {w : LSBWriter} {bs : List Bool} (h : w.Rep bs) (v n : Nat) :
    (w.writeVal v n).Rep (bs ++ natBits v n) := by
  induction n generalizing w v bs with
  | zero => simpa [LSBWriter.writeVal, natBits] using h
  | succ n ih =>
    rw [LSBWriter.writeVal, natBits]
    have := ih (h.writeBit (decide (v % 2 = 1))) (v / 2)
    simpa [List.append_assoc] using this

theorem LSBWriter.Rep.writeCodeMSB {w : LSBWriter} {bs : List Bool} (h : w.Rep bs) (c n : Nat) :
    (w.writeCodeMSB c n).Rep (bs ++ msbBits c n) := by
  induction n generalizing w bs with
  | zero => simpa [LSBWriter.writeCodeMSB, msbBits] using h
  | succ n ih =>
    rw [LSBWriter.writeCodeMSB, msbBits]
    have := ih (h.writeBit (c.testBit n))
    simpa [List.append_assoc] using this

theorem LSBWriter.Rep.toByteArray {w : LSBWriter} {bs : List Bool} (h : w.Rep bs) :
    ∃ pad, bytesBits w.toByteArray.data.toList = bs ++ pad := by
  obtain ⟨hc, hb, hbs⟩ := h
  unfold LSBWriter.toByteArray
  split
  · next h0 => exact ⟨[], by simp [← hbs, h0, natBits]⟩
  · have h256 : w.buffer < 256 := by
      have : 2 ^ w.count ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
      simp at this; omega
    refine ⟨natBits (w.buffer / 2 ^ w.count) (8 - w.count), ?_⟩
    have hb' : (UInt8.ofNat (w.buffer % 256)).toNat = w.buffer := by
      simp [Nat.mod_eq_of_lt h256]
    have := natBits_append w.buffer w.count (8 - w.count)
    rw [show w.count + (8 - w.count) = 8 by omega] at this
    simp only [ByteArray.data_push, Array.toList_push, bytesBits, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, hb', this, ← hbs, List.append_assoc]

theorem LSBReader.rep_ofByteArray (b : ByteArray) :
    (LSBReader.ofByteArray b).Rep (bytesBits b.data.toList) := by
  refine ⟨by simp [LSBReader.ofByteArray], ?_⟩
  simp [LSBReader.ofByteArray, natBits, ByteArray_toList_eq]

theorem LSBReader.Rep.bitsLeft {r : LSBReader} {bs : List Bool} (h : r.Rep bs) :
    r.bitsLeft = bs.length := by
  obtain ⟨_, h⟩ := h
  subst h
  simp [LSBReader.bitsLeft]

theorem LSBReader.Rep.readBit {r : LSBReader} {b : Bool} {bs : List Bool} (h : r.Rep (b :: bs)) :
    ∃ r', r.readBit = some (b, r') ∧ r'.Rep bs := by
  rcases r with ⟨buf, cnt, input, tr⟩
  obtain ⟨hb, hbs⟩ := h
  simp only at hb hbs
  unfold LSBReader.readBit
  by_cases hc : cnt = 0
  · subst hc
    simp only [natBits, List.nil_append] at hbs
    cases input with
    | nil => simp [bytesBits] at hbs
    | cons x xs =>
      simp only [bytesBits, List.flatMap_cons] at hbs
      have hx : x.toNat < 2 ^ 8 := x.toNat_lt
      have h8 : natBits x.toNat 8 = decide (x.toNat % 2 = 1) :: natBits (x.toNat / 2) 7 := rfl
      rw [h8, List.cons_append, List.cons.injEq] at hbs
      obtain ⟨rfl, hrest⟩ := hbs
      refine ⟨{ buffer := x.toNat >>> 1, count := 7, input := xs, totalRead := tr + 1 },
        by simp [LSBReader.refill]; rfl, ?_, ?_⟩
      · simp only [Nat.shiftRight_eq_div_pow]; omega
      · simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one]
        rw [← hrest]; rfl
  · obtain ⟨k, rfl⟩ : ∃ k, cnt = k + 1 := ⟨cnt - 1, by omega⟩
    rw [natBits, List.cons_append, List.cons.injEq] at hbs
    obtain ⟨rfl, hrest⟩ := hbs
    refine ⟨{ buffer := buf >>> 1, count := k, input := input, totalRead := tr + 1 },
      by simp, ?_, ?_⟩
    · simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      rw [Nat.pow_succ] at hb; omega
    · simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      exact hrest

@[simp] theorem natBits_zero (k : Nat) : natBits 0 k = List.replicate k false := by
  induction k with
  | zero => rfl
  | succ k ih => simp [natBits, ih, List.replicate_succ]

/-! ### Byte alignment

RFC 1951 §3.2.4 pads to a byte boundary before a stored block's LEN/NLEN.  These
lemmas say what that does to the abstract bit list on each side, and track the
partial-byte counter, which is what fixes the number of pad bits. -/

theorem LSBWriter.writeBit_count (w : LSBWriter) (hc : w.count < 8) (b : Bool) :
    (w.writeBit b).count = (w.count + 1) % 8 := by
  have key : (w.writeBit b).count = if w.count + 1 < 8 then w.count + 1 else w.count + 1 - 8 := by
    unfold LSBWriter.writeBit
    by_cases h : w.count + 1 < 8
    · simp only [h, ↓reduceDIte, ↓reduceIte]
    · simp only [h, ↓reduceDIte, ↓reduceIte]
  rw [key]
  split <;> omega

theorem LSBWriter.writeVal_count : ∀ (n : Nat) (w : LSBWriter) (v : Nat), w.count < 8 →
    (w.writeVal v n).count = (w.count + n) % 8 := by
  intro n
  induction n with
  | zero => intro w v hc; simpa [LSBWriter.writeVal] using (Nat.mod_eq_of_lt hc).symm
  | succ n ih =>
    intro w v hc
    rw [LSBWriter.writeVal,
      ih _ (v / 2) (by rw [LSBWriter.writeBit_count _ hc]; exact Nat.mod_lt _ (by decide)),
      LSBWriter.writeBit_count _ hc]
    omega

theorem LSBWriter.alignToByte_count (w : LSBWriter) : (w.alignToByte).count = 0 := by
  unfold LSBWriter.alignToByte
  split
  · assumption
  · rfl

theorem LSBWriter.Rep.alignToByte {w : LSBWriter} {bs : List Bool} (h : w.Rep bs) :
    (w.alignToByte).Rep (bs ++ List.replicate ((8 - w.count) % 8) false) := by
  obtain ⟨hc, hb, hbs⟩ := h
  unfold LSBWriter.alignToByte
  split
  · next h0 => rw [h0]; simpa using ⟨hc, hb, hbs⟩
  · next h0 =>
    have h256 : w.buffer < 256 := by
      have : 2 ^ w.count ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
      simp at this; omega
    have hb' : (UInt8.ofNat (w.buffer % 256)).toNat = w.buffer := by
      simp [Nat.mod_eq_of_lt h256]
    have hsplit := natBits_append w.buffer w.count (8 - w.count)
    rw [show w.count + (8 - w.count) = 8 by omega] at hsplit
    have hdiv : w.buffer / 2 ^ w.count = 0 := Nat.div_eq_of_lt hb
    have hmod : (8 - w.count) % 8 = 8 - w.count := Nat.mod_eq_of_lt (by omega)
    have hpush : bytesBits (w.bytes.push (UInt8.ofNat (w.buffer % 256))).data.toList
        = bytesBits w.bytes.data.toList ++ natBits w.buffer 8 := by
      simp only [ByteArray.data_push, Array.toList_push, bytesBits, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, hb']
    have hnb : natBits (0 : Nat) (0 : Nat) = [] := rfl
    refine ⟨by simp, by simp, ?_⟩
    show bytesBits (w.bytes.push (UInt8.ofNat (w.buffer % 256))).data.toList ++
      natBits 0 0 = bs ++ List.replicate ((8 - w.count) % 8) false
    rw [hnb, List.append_nil, hpush, hsplit, hdiv, natBits_zero, hmod, ← hbs, List.append_assoc]

theorem LSBWriter.Rep.writeByte {w : LSBWriter} {bs : List Bool} (h : w.Rep bs) (b : UInt8) :
    (w.writeByte b).Rep (bs ++ natBits b.toNat 8) := h.writeVal b.toNat 8

theorem LSBWriter.Rep.writeBytes : ∀ (data : List UInt8) {w : LSBWriter} {bs : List Bool},
    w.Rep bs → (data.foldl (fun w' b => w'.writeByte b) w).Rep (bs ++ bytesBits data) := by
  intro data
  induction data with
  | nil => intro w bs h; simpa [bytesBits] using h
  | cons b rest ih =>
    intro w bs h
    simp only [List.foldl_cons]
    simpa [bytesBits, List.append_assoc] using ih (h.writeByte b)

theorem LSBWriter.writeBytes_count : ∀ (data : List UInt8) (w : LSBWriter), w.count = 0 →
    (data.foldl (fun w' b => w'.writeByte b) w).count = 0 := by
  intro data
  induction data with
  | nil => intro w hc; simpa using hc
  | cons b rest ih =>
    intro w hc
    simp only [List.foldl_cons]
    exact ih _ (by rw [LSBWriter.writeByte, LSBWriter.writeVal_count 8 w b.toNat (by omega), hc])

/-- At a byte boundary the flushed bytes are exactly the abstract bits. -/
theorem LSBWriter.toByteArray_size {w : LSBWriter} {bs : List Bool} (h : w.Rep bs)
    (hc : w.count = 0) : w.toByteArray.size = bs.length / 8 := by
  obtain ⟨_, _, hbs⟩ := h
  rw [hc] at hbs
  simp only [natBits, List.append_nil] at hbs
  unfold LSBWriter.toByteArray
  simp only [hc, ↓reduceIte]
  have hlen := length_bytesBits w.bytes.data.toList
  rw [hbs] at hlen
  have hsz : w.bytes.data.toList.length = w.bytes.size := by simp
  omega

theorem LSBReader.alignToByte_count (r : LSBReader) : (r.alignToByte).count = 0 := rfl

theorem LSBReader.Rep.alignToByte {r : LSBReader} {bs : List Bool} (h : r.Rep bs) :
    (r.alignToByte).Rep (bs.drop r.count) := by
  obtain ⟨_, hbs⟩ := h
  refine ⟨by simp [LSBReader.alignToByte], ?_⟩
  rw [← hbs, List.drop_left' (by simp)]
  simp [LSBReader.alignToByte]

theorem LSBReader.readBit_count {r r' : LSBReader} {b : Bool} (hc : r.count < 8)
    (h : r.readBit = some (b, r')) : r'.count = (r.count + 7) % 8 := by
  rw [LSBReader.readBit] at h
  by_cases h0 : r.count = 0
  · simp only [h0, ↓reduceIte] at h
    by_cases h1 : r.refill.count = 0
    · simp only [h1, ↓reduceIte] at h
      exact absurd h (by simp)
    · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      have h8 : r.refill.count = 8 := by
        unfold LSBReader.refill at h1 ⊢
        split at h1
        · exact absurd h0 (by simpa using h1)
        · rfl
      rw [← h.2]
      simp only [h0, h8]
  · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    simp only
    omega

theorem LSBReader.readBits_count : ∀ (n : Nat) {r r' : LSBReader} {v : Nat}, r.count < 8 →
    r.readBits n = some (v, r') → r'.count = (r.count + 7 * n) % 8 := by
  intro n
  induction n with
  | zero =>
    intro r r' v hc h
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    simpa using (Nat.mod_eq_of_lt hc).symm
  | succ n ih =>
    intro r r' v hc h
    simp only [LSBReader.readBits] at h
    split at h
    · simp at h
    · next b r1 hb =>
      split at h
      · simp at h
      · next val r2 hv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have h1 := LSBReader.readBit_count hc hb
        have h2 := ih (r := r1) (by rw [h1]; exact Nat.mod_lt _ (by decide)) hv
        rw [← h.2, h2, h1]
        omega

theorem LSBReader.Rep.readBits {r : LSBReader} {v n : Nat} {bs : List Bool}
    (h : r.Rep (natBits v n ++ bs)) :
    ∃ r', r.readBits n = some (v % 2 ^ n, r') ∧ r'.Rep bs := by
  induction n generalizing v r with
  | zero => exact ⟨r, by simp [LSBReader.readBits, Nat.mod_one], by simpa [natBits] using h⟩
  | succ n ih =>
    rw [natBits, List.cons_append] at h
    obtain ⟨r1, h1, hr1⟩ := h.readBit
    obtain ⟨r2, h2, hr2⟩ := ih hr1
    refine ⟨r2, ?_, hr2⟩
    simp only [LSBReader.readBits, h1, h2, Option.some.injEq, Prod.mk.injEq, and_true]
    rw [Nat.pow_succ', Nat.mod_mul]
    by_cases hv : v % 2 = 1 <;> simp [hv] <;> omega

end Silmaril.Formats.Compression
