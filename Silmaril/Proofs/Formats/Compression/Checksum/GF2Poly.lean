module

public import Silmaril.Formats.Compression.Checksum.GF2Poly
public import Silmaril.Proofs.Formats.Compression.Checksum.GF2PolyBits

/-! Proofs about `Silmaril.Formats.Compression.Checksum.GF2Poly`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.GF2Poly

open Silmaril.Formats.Compression.GF2Poly

/-! ### Bit arithmetic -/

theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = a / 2 ^^^ b / 2 :=
  Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_div_two, Nat.testBit_xor]

theorem xor_eq_zero_iff {a b : Nat} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    exact Nat.eq_of_testBit_eq fun i => by
      have := congrArg (·.testBit i) h
      simp only [Nat.testBit_xor, Nat.zero_testBit] at this
      revert this; cases a.testBit i <;> cases b.testBit i <;> simp
  · rintro rfl; exact Nat.xor_self a

/-! ### Multiplication -/

theorem mul_def (a b : Nat) :
    mul a b = (mul a (b / 2) <<< 1) ^^^ (if b.testBit 0 then a else 0) := by
  rw [mul]
  split
  · subst_vars; simp [mul]
  · rfl

@[simp] theorem mul_zero (a : Nat) : mul a 0 = 0 := by rw [mul]; simp

@[simp] theorem mul_one (a : Nat) : mul a 1 = a := by rw [mul_def]; simp

theorem mul_xor (a b c : Nat) : mul a (b ^^^ c) = mul a b ^^^ mul a c := by
  induction b using Nat.strongRecOn generalizing c with
  | ind b ih =>
    by_cases hb : b = 0
    · subst hb; simp
    rw [mul_def, mul_def a b, mul_def a c, xor_div_two, ih _ (by omega), Nat.shiftLeft_xor_distrib,
      Nat.testBit_xor]
    cases b.testBit 0 <;> cases c.testBit 0 <;> simp
    · ac_rfl
    · ac_rfl
    · have h (x y : Nat) : x ^^^ a ^^^ (y ^^^ a) = x ^^^ y ^^^ (a ^^^ a) := by ac_rfl
      rw [h, Nat.xor_self, Nat.xor_zero]

theorem mul_shiftLeft (a b k : Nat) : mul a (b <<< k) = mul a b <<< k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [mul_def, Nat.shiftLeft_add, Nat.shiftLeft_add (mul a b), ← ih]
    have h1 : b <<< k <<< 1 / 2 = b <<< k := by rw [Nat.shiftLeft_eq]; omega
    have h2 : (b <<< k <<< 1).testBit 0 = false := by simp
    rw [h1, h2]; simp

/-- A nonzero multiple of `g` has degree at least `deg g`. -/
theorem mul_bounds {g d : Nat} (hg1 : 2 ^ d ≤ g) (hg2 : g < 2 ^ (d + 1)) :
    ∀ q, q ≠ 0 → ∃ m, 2 ^ (m + d) ≤ mul g q ∧ mul g q < 2 ^ (m + d + 1) := by
  intro q
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro hq
    by_cases h1 : q / 2 = 0
    · have : q = 1 := by omega
      subst this; exact ⟨0, by simpa using hg1, by simpa using hg2⟩
    obtain ⟨m, hm1, hm2⟩ := ih (q / 2) (by omega) h1
    refine ⟨m + 1, ?_⟩
    rw [mul_def]
    have hlt : (if q.testBit 0 then g else 0) < 2 ^ (m + 1 + d) := by
      have : 2 ^ (d + 1) ≤ 2 ^ (m + 1 + d) := Nat.pow_le_pow_right (by decide) (by omega)
      split <;> omega
    have hs1 : 2 ^ (m + 1 + d) ≤ mul g (q / 2) <<< 1 := by
      rw [Nat.shiftLeft_eq, show m + 1 + d = m + d + 1 by omega, Nat.pow_succ]; omega
    have hs2 : mul g (q / 2) <<< 1 < 2 ^ (m + 1 + d + 1) := by
      rw [Nat.shiftLeft_eq, show m + 1 + d + 1 = m + d + 1 + 1 by omega, Nat.pow_succ]; omega
    refine ⟨?_, Nat.xor_lt_two_pow hs2 (Nat.lt_trans hlt (Nat.pow_lt_pow_right (by decide)
      (by omega)))⟩
    apply Nat.ge_two_pow_of_testBit
    rw [Nat.testBit_xor, testBit_of_bounds hs1 hs2, Nat.testBit_lt_two_pow hlt]; rfl

/-! ### Congruence modulo `g` -/

/-- `a ≡ b (mod g)`: `a - b` is a multiple of `g`. -/
def Cong (g a b : Nat) : Prop := ∃ q, a ^^^ b = mul g q

theorem Cong.refl (g a : Nat) : Cong g a a := ⟨0, by simp [Nat.xor_self]⟩

theorem Cong.symm {g a b : Nat} : Cong g a b → Cong g b a := by
  rintro ⟨q, h⟩; exact ⟨q, by rw [Nat.xor_comm, h]⟩

theorem Cong.xor {g a b c d : Nat} : Cong g a b → Cong g c d → Cong g (a ^^^ c) (b ^^^ d) := by
  rintro ⟨q, hq⟩ ⟨r, hr⟩
  refine ⟨q ^^^ r, ?_⟩
  rw [mul_xor, ← hq, ← hr]; ac_rfl

theorem Cong.trans {g a b c : Nat} : Cong g a b → Cong g b c → Cong g a c := by
  rintro ⟨q, hq⟩ ⟨r, hr⟩
  refine ⟨q ^^^ r, ?_⟩
  rw [mul_xor, ← hq, ← hr]
  calc a ^^^ c = a ^^^ (b ^^^ b) ^^^ c := by rw [Nat.xor_self, Nat.xor_zero]
    _ = _ := by ac_rfl

theorem Cong.shiftLeft {g a b : Nat} (k : Nat) : Cong g a b → Cong g (a <<< k) (b <<< k) := by
  rintro ⟨q, hq⟩
  exact ⟨q <<< k, by rw [mul_shiftLeft, ← hq, Nat.shiftLeft_xor_distrib]⟩

theorem Cong.mul_self (g q : Nat) : Cong g (mul g q) 0 := ⟨q, by simp⟩

/-- Remainders of degree below `deg g` are congruent only if equal. -/
theorem Cong.eq {g a b : Nat} (hg : g ≠ 0) (h : Cong g a b) (ha : a < 2 ^ deg g)
    (hb : b < 2 ^ deg g) : a = b := by
  obtain ⟨q, hq⟩ := h
  by_cases hq0 : q = 0
  · subst hq0; simpa [xor_eq_zero_iff] using hq
  obtain ⟨m, hm, -⟩ := mul_bounds (Nat.log2_self_le hg) Nat.lt_log2_self q hq0
  have hlt : a ^^^ b < 2 ^ deg g := Nat.xor_lt_two_pow ha hb
  have : 2 ^ deg g ≤ 2 ^ (m + deg g) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [deg] at *
  omega

/-! ### Remainder -/

theorem mod_cong (a g : Nat) : Cong g (mod a g) a := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    rw [mod]
    split
    · next h =>
      refine (ih _ (xor_shiftLeft_log2_lt h.1 h.2.1 h.2.2)).trans ?_
      refine ⟨1 <<< (deg a - deg g), ?_⟩
      rw [mul_shiftLeft, mul_one]
      calc a ^^^ g <<< (deg a - deg g) ^^^ a = a ^^^ a ^^^ g <<< (deg a - deg g) := by ac_rfl
        _ = _ := by rw [Nat.xor_self, Nat.zero_xor]
    · exact Cong.refl g a

theorem mod_lt (a : Nat) {g : Nat} (hg : g ≠ 0) : mod a g < 2 ^ deg g := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    rw [mod]
    split
    · next h => exact ih _ (xor_shiftLeft_log2_lt h.1 h.2.1 h.2.2)
    · next h =>
      by_cases ha : a = 0
      · subst ha; exact Nat.two_pow_pos _
      have : deg a < deg g := by simp only [deg] at h ⊢; omega
      exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) this)

/-- `mod a g` is the unique polynomial of degree below `deg g` congruent to `a`. -/
theorem mod_eq_iff {a g r : Nat} (hg : g ≠ 0) :
    mod a g = r ↔ r < 2 ^ deg g ∧ ∃ q, a ^^^ r = mul g q := by
  constructor
  · rintro rfl; exact ⟨mod_lt a hg, (mod_cong a g).symm⟩
  · rintro ⟨hr, h⟩; exact Cong.eq hg ((mod_cong a g).trans h) (mod_lt a hg) hr

theorem mod_eq_of_cong {a b g : Nat} (hg : g ≠ 0) (h : Cong g a b) : mod a g = mod b g :=
  Cong.eq hg (((mod_cong a g).trans h).trans (mod_cong b g).symm) (mod_lt a hg) (mod_lt b hg)

theorem mod_eq_self {a g : Nat} (hg : g ≠ 0) (ha : a < 2 ^ deg g) : mod a g = a :=
  (mod_eq_iff hg).2 ⟨ha, (Cong.refl g a)⟩

theorem mod_xor (a b : Nat) {g : Nat} (hg : g ≠ 0) : mod (a ^^^ b) g = mod a g ^^^ mod b g :=
  (mod_eq_iff hg).2 ⟨Nat.xor_lt_two_pow (mod_lt a hg) (mod_lt b hg),
    (((mod_cong a g).xor (mod_cong b g)).symm)⟩

theorem mod_shiftLeft_mod (a k : Nat) {g : Nat} (hg : g ≠ 0) :
    mod (mod a g <<< k) g = mod (a <<< k) g :=
  mod_eq_of_cong hg ((mod_cong a g).shiftLeft k)

theorem mod_mul_self (g q : Nat) (hg : g ≠ 0) : mod (mul g q) g = 0 :=
  (mod_eq_of_cong hg (Cong.mul_self g q)).trans (mod_eq_self hg (Nat.two_pow_pos _))

theorem mod_mod (a : Nat) {g : Nat} (hg : g ≠ 0) : mod (mod a g) g = mod a g :=
  mod_eq_self hg (mod_lt a hg)

/-- Division with remainder: `a = g · q + (a mod g)`. -/
theorem exists_eq_mul_xor_mod (a g : Nat) : ∃ q, a = mul g q ^^^ mod a g := by
  obtain ⟨q, hq⟩ := mod_cong a g
  exact ⟨q, by rw [← hq]; calc a = a ^^^ (mod a g ^^^ mod a g) := by rw [Nat.xor_self, Nat.xor_zero]
                               _ = _ := by ac_rfl⟩

/-! ### Bit strings and reflection -/

theorem ofBits_append_aux (a : Nat) (bs : List Bool) :
    bs.foldl (fun acc b => add (mulXPow 1 acc) b.toNat) a = (a <<< bs.length) ^^^ ofBits bs := by
  induction bs generalizing a with
  | nil => simp [ofBits]
  | cons b bs ih =>
    simp only [List.foldl_cons, ofBits, List.length_cons] at ih ⊢
    rw [ih, ih (add (mulXPow 1 0) b.toNat)]
    simp only [add, mulXPow, Nat.zero_shiftLeft, Nat.zero_xor, Nat.shiftLeft_xor_distrib,
      ← Nat.shiftLeft_add, Nat.add_comm 1]
    ac_rfl

theorem ofBits_append (as bs : List Bool) :
    ofBits (as ++ bs) = (ofBits as <<< bs.length) ^^^ ofBits bs := by
  rw [ofBits, List.foldl_append]; exact ofBits_append_aux _ _

theorem ofBits_lt_aux (a m : Nat) (bs : List Bool) (ha : a < 2 ^ m) :
    bs.foldl (fun acc b => add (mulXPow 1 acc) b.toNat) a < 2 ^ (m + bs.length) := by
  induction bs generalizing a m with
  | nil => simpa using ha
  | cons b bs ih =>
    rw [List.foldl_cons, List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]
    refine ih _ _ (Nat.xor_lt_two_pow ?_ ?_)
    · simp only [mulXPow, Nat.shiftLeft_eq, Nat.pow_succ]; omega
    · have := Nat.two_pow_pos m; cases b <;> simp [Nat.pow_succ] <;> omega

theorem ofBits_lt (bs : List Bool) : ofBits bs < 2 ^ bs.length := by
  have := ofBits_lt_aux 0 0 bs (by decide)
  rwa [Nat.zero_add] at this

theorem ofBits_singleton (b : Bool) : ofBits [b] = b.toNat := by
  simp [ofBits]

theorem reflect_succ (n r : Nat) :
    reflect (n + 1) r = (reflect n r <<< 1) ^^^ (r.testBit n).toNat := by
  rw [reflect, List.range_succ, List.map_append, ofBits_append, List.map_singleton,
    ofBits_singleton]
  rfl

theorem testBit_reflect (n r i : Nat) :
    (reflect n r).testBit i = (decide (i < n) && r.testBit (n - 1 - i)) := by
  induction n generalizing i with
  | zero => simp [reflect, ofBits]
  | succ n ih =>
    rw [reflect_succ, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_bool_toNat]
    rcases i with _ | i
    · simp
    · rw [ih]
      simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, decide_false, Bool.false_and,
        Bool.xor_false, Nat.le_add_left, decide_true, Bool.true_and]
      rw [show n - (i + 1) = n - 1 - i by omega]
      by_cases h : i < n
      · simp [h, show i + 1 < n + 1 by omega]
      · simp [h, show ¬ i + 1 < n + 1 by omega]

theorem reflect_lt (n r : Nat) : reflect n r < 2 ^ n := by
  have := ofBits_lt ((List.range n).map r.testBit)
  rwa [List.length_map, List.length_range] at this

theorem reflect_xor (n a b : Nat) : reflect n (a ^^^ b) = reflect n a ^^^ reflect n b :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_reflect, Nat.testBit_xor]; cases decide (i < n) <;> simp

theorem reflect_reflect {n r : Nat} (h : r < 2 ^ n) : reflect n (reflect n r) = r :=
  Nat.eq_of_testBit_eq fun i => by
    rw [testBit_reflect, testBit_reflect]
    by_cases hi : i < n
    · rw [show n - 1 - (n - 1 - i) = i by omega]; simp [hi, show n - 1 - i < n by omega]
    · have : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : r.testBit i = false := Nat.testBit_lt_two_pow (by omega)
      simp [hi, h2]

end Silmaril.Proofs.Formats.Compression.GF2Poly
