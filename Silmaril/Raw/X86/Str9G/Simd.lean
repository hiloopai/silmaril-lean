module

public import Silmaril.X86.Str9G.Defs

/-! # Per-byte and per-bit facts of the SSE2 forms (`Str9G`)

* `byteOf_ofBytes`: byte `i < 16` of `ofBytes f` is `f i`; hence `byteOf_cmpeqb`,
  `byteOf_minub`;
* `getLsbD_movmskb`: bit `i` of `movmskb v` is the top bit of byte `i` (`i < 16`), and the
  bits from 16 up are clear;
* `msb_byteOf_cmpeqb_zero`: after `pcmpeqb` against zero, the top bit of byte `i` says
  whether byte `i` was zero; `minub_byte_zero`: a byte of a `pminub` is zero iff one of the
  two bytes is;
* `bsfIndex_spec`: the index `bsf` writes is the lowest set bit.
-/

@[expose] public section

namespace Silmaril.Raw.X86.Str9G

open Silmaril.X86.Str9G
open Silmaril.X86.Sse9 (Xmm)

/-- Little-endian digits of width `k`. -/
def digits (k : Nat) (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => digits k a n + a n * 2 ^ (k * n)

theorem digits_lt {k : Nat} {a : Nat → Nat} (h : ∀ j, a j < 2 ^ k) :
    ∀ n, digits k a n < 2 ^ (k * n)
  | 0 => by simp [digits]
  | n + 1 => by
    have ih := digits_lt h n
    have ha := h n
    simp only [digits]
    have : a n * 2 ^ (k * n) ≤ (2 ^ k - 1) * 2 ^ (k * n) :=
      Nat.mul_le_mul_right _ (by omega)
    have e : 2 ^ (k * (n + 1)) = 2 ^ k * 2 ^ (k * n) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [e]
    have : (2 ^ k - 1) * 2 ^ (k * n) + 2 ^ (k * n) = 2 ^ k * 2 ^ (k * n) := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [Nat.sub_mul, Nat.one_mul]
      have : 2 ^ (k * n) ≤ 2 ^ k * 2 ^ (k * n) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega

theorem digits_get {k : Nat} {a : Nat → Nat} (h : ∀ j, a j < 2 ^ k) :
    ∀ n i, i < n → (digits k a n >>> (k * i)) % 2 ^ k = a i
  | 0, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, hi => by
    simp only [digits, Nat.shiftRight_eq_div_pow]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have ih := digits_get h n i hi
      rw [Nat.shiftRight_eq_div_pow] at ih
      have e1 : k * n = k * i + k * (n - i) := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' (Nat.le_of_lt hi)]
      have e2 : k * (n - i) = k + k * (n - i - 1) := by
        rw [show n - i = 1 + (n - i - 1) by omega, Nat.mul_add, Nat.mul_one]
        congr 2; omega
      rw [e1, Nat.pow_add, Nat.mul_left_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), e2,
        Nat.pow_add, Nat.mul_left_comm, Nat.add_mul_mod_self_left, ih]
    · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (digits_lt h i),
        Nat.zero_add, Nat.mod_eq_of_lt (h i)]

theorem sum_range_eq_digits (k : Nat) (a : Nat → Nat) :
    ∀ n, ((List.range n).map fun j => a j * 2 ^ (k * j)).sum = digits k a n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_eq_digits k a n]
    simp [digits]

theorem toNat_ofBytes (f : Nat → BitVec 8) :
    (ofBytes f).toNat = digits 8 (fun i => (f i).toNat) 16 := by
  unfold ofBytes
  rw [BitVec.toNat_ofNat, sum_range_eq_digits 8 (fun i => (f i).toNat) 16]
  exact Nat.mod_eq_of_lt (digits_lt (fun j => (f j).isLt) 16)

/-- **Byte `i` of `ofBytes f` is `f i`.** -/
theorem byteOf_ofBytes (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) : byteOf (ofBytes f) i = f i := by
  apply BitVec.eq_of_toNat_eq
  unfold byteOf
  rw [BitVec.extractLsb'_toNat, toNat_ofBytes]
  exact digits_get (k := 8) (fun j => (f j).isLt) 16 i hi

theorem byteOf_cmpeqb (d v : Xmm) {i : Nat} (hi : i < 16) :
    byteOf (cmpeqb d v) i = if byteOf d i = byteOf v i then 0xFF else 0 := by
  unfold cmpeqb bytewise; rw [byteOf_ofBytes _ hi]

theorem byteOf_minub (d v : Xmm) {i : Nat} (hi : i < 16) :
    byteOf (minub d v) i = if (byteOf d i).toNat ≤ (byteOf v i).toNat then byteOf d i else byteOf v i := by
  unfold minub bytewise; rw [byteOf_ofBytes _ hi]

theorem minub_byte_zero (d v : Xmm) {i : Nat} (hi : i < 16) :
    byteOf (minub d v) i = 0 ↔ byteOf d i = 0 ∨ byteOf v i = 0 := by
  rw [byteOf_minub d v hi]
  have h1 := (byteOf d i).isLt; have h2 := (byteOf v i).isLt
  constructor
  · intro h; split at h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · rw [ite_eq_left_iff.mpr (fun hn => absurd (by rw [h]; simp) hn)]; exact h
    · split
      · rename_i hle; rw [h] at hle; apply BitVec.eq_of_toNat_eq; simp at hle ⊢; omega
      · exact h

/-- **Bit `i` of `pmovmskb`.** -/
theorem getLsbD_movmskb (v : Xmm) (i : Nat) :
    (movmskb v).getLsbD i = (decide (i < 16) && (byteOf v i).msb) := by
  have hs : ((List.range 16).map fun j => if (byteOf v j).msb then 2 ^ j else 0).sum =
      digits 1 (fun j => if (byteOf v j).msb then 1 else 0) 16 := by
    rw [← sum_range_eq_digits]; congr 1; apply List.map_congr_left; intro j _
    split <;> simp
  have hlt : digits 1 (fun j => if (byteOf v j).msb then 1 else 0) 16 < 2 ^ 16 :=
    digits_lt (fun j => by split <;> simp) 16
  unfold movmskb
  rw [hs, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  by_cases hi : i < 16
  · have := digits_get (k := 1) (a := fun j => if (byteOf v j).msb then 1 else 0)
      (fun j => by split <;> simp) 16 i hi
    simp only [Nat.one_mul, Nat.pow_one, Nat.shiftRight_eq_div_pow] at this
    rw [this]
    have : i < 64 := by omega
    simp only [this, decide_true, Bool.true_and, hi]
    split <;> simp_all
  · have : digits 1 (fun j => if (byteOf v j).msb then 1 else 0) 16 / 2 ^ i = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, this]

/-- After `pcmpeqb` against zero, the top bit of byte `i` says whether byte `i` was zero. -/
theorem msb_byteOf_cmpeqb_zero (v : Xmm) {i : Nat} (hi : i < 16) :
    (byteOf (cmpeqb 0 v) i).msb = decide (byteOf v i = 0) := by
  rw [byteOf_cmpeqb _ _ hi]
  have : byteOf 0 i = 0 := by unfold byteOf; simp
  rw [this]
  split
  · rename_i he
    rw [decide_eq_true he.symm]; decide
  · rename_i he
    rw [decide_eq_false (fun e => he e.symm)]; decide

theorem msb_byteOf_cmpeqb_zero' (v : Xmm) {i : Nat} (hi : i < 16) :
    (byteOf (cmpeqb v 0) i).msb = decide (byteOf v i = 0) := by
  rw [byteOf_cmpeqb _ _ hi]
  have : byteOf 0 i = 0 := by unfold byteOf; simp
  rw [this]
  split
  · rename_i he
    rw [decide_eq_true he]; decide
  · rename_i he
    rw [decide_eq_false he]; decide

/-- **`bsf` writes the index of the lowest set bit.** -/
theorem bsfIndex_spec {n : Nat} {x : BitVec n} (hx : x ≠ 0) :
    Silmaril.X86.Ext9.bsfIndex x < n ∧ x.getLsbD (Silmaril.X86.Ext9.bsfIndex x) = true ∧
      ∀ j < Silmaril.X86.Ext9.bsfIndex x, x.getLsbD j = false := by
  unfold Silmaril.X86.Ext9.bsfIndex Silmaril.X86.Ext.tzcntN
  have hex : ∃ i, i < n ∧ x.getLsbD i = true := by
    by_contra hne
    apply hx
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    show x.getLsbD i = (0#n).getLsbD i
    rw [BitVec.getLsbD_zero]
    cases hb : x.getLsbD i
    · rfl
    · exact absurd ⟨i, hi, hb⟩ hne
  cases hf : (List.range n).find? (fun i => x.getLsbD i) with
  | none =>
    exfalso
    obtain ⟨i, hi, hb⟩ := hex
    have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
    simp [hb] at this
  | some k =>
    simp only [Option.getD_some]
    have hk := List.find?_some hf
    have hmem := List.mem_of_find?_eq_some hf
    rw [List.find?_eq_some_iff_append] at hf
    obtain ⟨-, as, bs, hsplit, hbefore⟩ := hf
    have hget : ∀ j, j < as.length → as[j]? = some j := by
      intro j hj
      have h1 : (List.range n)[j]? = as[j]? := by
        rw [hsplit, List.getElem?_append_left hj]
      have hjn : j < n := by
        have : as.length < (List.range n).length := by rw [hsplit]; simp
        simp at this; omega
      rw [← h1, List.getElem?_range hjn]
    have hlen : as.length = k := by
      have h1 : (List.range n)[as.length]? = some k := by rw [hsplit]; simp
      have hlt : as.length < n := by
        have : as.length < (List.range n).length := by rw [hsplit]; simp
        simpa using this
      rw [List.getElem?_range hlt] at h1
      exact Option.some.inj h1
    refine ⟨List.mem_range.mp hmem, by simpa using hk, ?_⟩
    intro j hj
    have hjm : j ∈ as := List.mem_of_getElem? (hget j (by omega))
    simpa using hbefore j hjm

end Silmaril.Raw.X86.Str9G
