module

public import Silmaril.Logic.ACL2.Standard.IntegerBits.Defs
import Mathlib.Data.Nat.Size
import Init.Data.Int.Bitwise.Lemmas

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Standard.IntegerBits

open Silmaril.Logic.ACL2.Standard

private theorem testBit_injective {a b : Int} (h : ∀ k, a.testBit k = b.testBit k) : a = b := by
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b => exact congrArg Int.ofNat (Nat.eq_of_testBit_eq h)
    | negSucc b =>
      have ha : a < 2 ^ (a + b) := Nat.lt_of_le_of_lt (Nat.le_add_right ..) Nat.lt_two_pow_self
      have hb : b < 2 ^ (a + b) := Nat.lt_of_le_of_lt (Nat.le_add_left ..) Nat.lt_two_pow_self
      have hh := h (a + b)
      simp [Int.testBit, Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb] at hh
  | negSucc a =>
    cases b with
    | ofNat b =>
      have ha : a < 2 ^ (a + b) := Nat.lt_of_le_of_lt (Nat.le_add_right ..) Nat.lt_two_pow_self
      have hb : b < 2 ^ (a + b) := Nat.lt_of_le_of_lt (Nat.le_add_left ..) Nat.lt_two_pow_self
      have hh := h (a + b)
      simp [Int.testBit, Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb] at hh
    | negSucc b =>
      apply congrArg Int.negSucc
      apply Nat.eq_of_testBit_eq
      intro k
      simpa [Int.testBit] using h k

private theorem integerFix_integer (i : Int) : (Object.integer i).integerFix = i := rfl

private theorem bodd_eq_mod (n : Int) : n.bodd = decide (n % 2 = 1) := by
  have h := Int.bodd_add_div2 n
  rw [Int.div2_val] at h
  cases hb : n.bodd <;> simp only [hb, Bool.cond_false, Bool.cond_true] at h <;> simp <;> omega

private theorem testBit_zero (n : Int) : n.testBit 0 = n.bodd := by
  cases n <;> rfl

theorem land_recurrence (a b : Int) :
    Int.land a b = 2 * Int.land (a / 2) (b / 2) + (if a % 2 = 1 ∧ b % 2 = 1 then 1 else 0) := by
  conv_lhs => rw [← Int.bit_decomp a, ← Int.bit_decomp b]
  rw [Int.land_bit, Int.bit_val, Int.div2_val, Int.div2_val]
  rw [bodd_eq_mod, bodd_eq_mod]
  by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1 <;> simp [ha, hb]

theorem land_zero_left (a : Int) : Int.land 0 a = 0 := by
  apply testBit_injective
  intro k
  rw [Int.testBit_land]
  change _ = Nat.testBit 0 k
  simp [show (0 : Int).testBit k = Nat.testBit 0 k from rfl]

theorem land_zero_right (a : Int) : Int.land a 0 = 0 := by
  apply testBit_injective
  intro k
  rw [Int.testBit_land]
  change _ = Nat.testBit 0 k
  simp [show (0 : Int).testBit k = Nat.testBit 0 k from rfl]

theorem land_neg_one_left (a : Int) : Int.land (-1) a = a := by
  apply testBit_injective
  intro k
  have hb : (-1 : Int).testBit k = true := by
    change !(Nat.testBit 0 k) = true
    simp
  simp [hb]

theorem land_neg_one_right (a : Int) : Int.land a (-1) = a := by
  apply testBit_injective
  intro k
  have hb : (-1 : Int).testBit k = true := by
    change !(Nat.testBit 0 k) = true
    simp
  simp [hb]

theorem lognot_eq (x : Object) : x.lognot = Object.integer (-x.integerFix - 1) := by
  unfold Object.lognot
  apply congrArg Object.integer
  cases x.integerFix <;> simp only [Int.lnot, Int.negSucc_eq, Int.ofNat_eq_natCast] <;> omega

theorem logior_eq (x y : Object) : x.binaryLogior y = (x.lognot.binaryLogand y.lognot).lognot := by
  simp only [Object.binaryLogior, Object.binaryLogand, Object.lognot, integerFix_integer]
  apply congrArg Object.integer
  apply testBit_injective
  intro k
  simp only [Int.testBit_lor, Int.testBit_lnot, Int.testBit_land]
  cases x.integerFix.testBit k <;> cases y.integerFix.testBit k <;> rfl

theorem logxor_eq (x y : Object) : x.binaryLogxor y =
    ((x.lognot.binaryLogior y).binaryLogand (y.lognot.binaryLogior x)).lognot := by
  simp only [Object.binaryLogxor, Object.binaryLogior, Object.binaryLogand, Object.lognot,
    integerFix_integer]
  apply congrArg Object.integer
  apply testBit_injective
  intro k
  simp only [Int.testBit_lxor, Int.testBit_lor, Int.testBit_lnot, Int.testBit_land]
  cases x.integerFix.testBit k <;> cases y.integerFix.testBit k <;> rfl

theorem ash_eq (x count : Object) : x.ash count = Object.integer
    (if 0 ≤ count.integerFix then x.integerFix * 2 ^ count.integerFix.toNat
     else x.integerFix / 2 ^ (-count.integerFix).toNat) := by
  simp only [Object.ash, ← Int.shiftRight_eq, Int.shiftRight_eq_div_pow, ← Int.shiftLeft_eq]
  rfl

theorem logbitp_eq (index x : Object) : index.logbitp x =
    Object.ofBool (decide (x.integerFix / 2 ^ index.natRank % 2 = 1)) := by
  have h : Int.shiftRight x.integerFix index.natRank = x.integerFix / 2 ^ index.natRank := by
    rw [← Int.shiftRight_eq, Int.shiftRight_eq_div_pow]
    rfl
  rw [Object.logbitp, ← h, ← bodd_eq_mod, ← testBit_zero]
  congr 1
  cases x.integerFix with
  | ofNat n =>
    change n.testBit index.natRank = (n >>> index.natRank).testBit 0
    simp
  | negSucc n =>
    change (!n.testBit index.natRank) = !(n >>> index.natRank).testBit 0
    simp

private theorem size_div_two (n : Nat) (h : n ≠ 0) : n.size = 1 + (n / 2).size := by
  have hb := Nat.bit_bodd_div2 n
  have hbit : Nat.bit n.bodd n.div2 ≠ 0 := fun he => h (hb.symm.trans he)
  calc
    n.size = (Nat.bit n.bodd n.div2).size := congrArg Nat.size hb.symm
    _ = 1 + (n / 2).size := by rw [Nat.size_bit hbit, Nat.div2_val]; omega

theorem integerLength_recurrence (n : Int) (hz : n ≠ 0) (hs : n ≠ -1) :
    (Object.integer n).integerLength = Object.integer
      (1 + (Object.integer (n / 2)).integerLength.integerFix) := by
  rw [← Int.div2_val]
  cases n with
  | ofNat n =>
    have h : n ≠ 0 := fun he => hz (congrArg Int.ofNat he)
    simp only [Object.integerLength, integerFix_integer, Int.div2, Nat.div2_val, size_div_two n h]
    rfl
  | negSucc n =>
    have h : n ≠ 0 := fun he => hs (congrArg Int.negSucc he)
    simp only [Object.integerLength, integerFix_integer, Int.div2, Nat.div2_val, size_div_two n h]
    rfl

end Silmaril.Proofs.Logic.ACL2.Standard.IntegerBits
