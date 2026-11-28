module

public import Silmaril.Logic.ManyValuedCatalogue.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

public section

namespace Silmaril.Proofs.Logic.ManyValuedCatalogue

open Silmaril.Logic.ManyValuedCatalogue

namespace Goedel

variable {A : Type*} [LinearOrder A] [BoundedOrder A]

theorem residuation (x y z : A) : Goedel.and x y ≤ z ↔ y ≤ Goedel.imp x z := by
  change min x y ≤ z ↔ y ≤ Goedel.imp x z
  by_cases h : x ≤ z
  · simp [Goedel.imp, h, (min_le_left x y).trans h]
  · simp [Goedel.imp, h, min_le_iff]

theorem neg_eq (x : A) : Goedel.neg x = if x = ⊥ then ⊤ else ⊥ := by
  simp [Goedel.neg, Goedel.imp]

end Goedel

namespace UnitInterval

open Silmaril.Logic.ManyValuedCatalogue.UnitInterval

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem luk_residuation (x y z : UnitInterval K) : lukAnd x y ≤ z ↔ y ≤ lukImp x z := by
  change max 0 (x.val + y.val - 1) ≤ z.val ↔ y.val ≤ min 1 (1 - x.val + z.val)
  simp only [max_le_iff, le_min_iff, z.2.1, y.2.2, true_and]
  constructor <;> intro h <;> linarith

theorem luk_neg_eq (x : UnitInterval K) : lukImp x ⊥ = lukNeg x := by
  apply Subtype.ext
  change min 1 (1 - x.val + 0) = 1 - x.val
  rw [add_zero, min_eq_right (sub_le_self _ x.2.1)]

theorem prod_residuation (x y z : UnitInterval K) : prodAnd x y ≤ z ↔ y ≤ prodImp x z := by
  by_cases h : x ≤ z
  · have hmul : x.val * y.val ≤ x.val := by
      simpa using mul_le_mul_of_nonneg_left y.2.2 x.2.1
    simp [prodImp, h, show prodAnd x y ≤ z from hmul.trans h]
  · have hx : 0 < x.val := z.2.1.trans_lt (lt_of_not_ge h)
    rw [prodImp, dite_eq_right h]
    change x.val * y.val ≤ z.val ↔ y.val ≤ z.val / x.val
    rw [le_div_iff₀ hx, mul_comm]

theorem prod_neg_eq (x : UnitInterval K) : prodNeg x = Goedel.neg x := by
  by_cases h : x ≤ ⊥
  · simp [prodNeg, prodImp, Goedel.neg, Goedel.imp, h]
  · apply Subtype.ext
    rw [prodNeg, prodImp, dite_eq_right h, Goedel.neg, Goedel.imp, ite_eq_right h]
    change 0 / x.val = 0
    exact zero_div _

theorem prod_meet_eq (x y : UnitInterval K) : prodMeet x y = min x y := by
  by_cases h : x ≤ y
  · rw [min_eq_left h, prodMeet, prodImp, dite_eq_left h]
    apply Subtype.ext
    exact mul_one _
  · have hx : 0 < x.val := y.2.1.trans_lt (lt_of_not_ge h)
    rw [min_eq_right (le_of_not_ge h), prodMeet, prodImp, dite_eq_right h]
    apply Subtype.ext
    change x.val * (y.val / x.val) = y.val
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hx.ne']

private theorem grid_denom_pos (n : ℕ) : (0 : K) < (n : K) + 1 :=
  add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one

theorem ofGrid_le_iff {n : ℕ} {x y : Grid n} :
    (ofGrid x : UnitInterval K) ≤ ofGrid y ↔ x ≤ y := by
  change (x.val : K) / ((n : K) + 1) ≤ (y.val : K) / ((n : K) + 1) ↔ x.val ≤ y.val
  rw [div_le_div_iff_of_pos_right (grid_denom_pos n), Nat.cast_le]

theorem ofGrid_bot (n : ℕ) : (ofGrid (⊥ : Grid n) : UnitInterval K) = ⊥ := by
  apply Subtype.ext
  change (((⊥ : Grid n).val : ℕ) : K) / ((n : K) + 1) = 0
  rw [bot_eq_zero, Fin.val_zero, Nat.cast_zero, zero_div]

theorem ofGrid_top (n : ℕ) : (ofGrid (⊤ : Grid n) : UnitInterval K) = ⊤ := by
  apply Subtype.ext
  have hn : (⊤ : Grid n).val = n + 1 := by simp [Fin.val_top]
  change (((⊤ : Grid n).val : ℕ) : K) / ((n : K) + 1) = 1
  rw [hn, Nat.cast_add, Nat.cast_one, div_self (grid_denom_pos n).ne']

theorem ofGrid_and {n : ℕ} (x y : Grid n) :
    (ofGrid (Goedel.and x y) : UnitInterval K) = Goedel.and (ofGrid x) (ofGrid y) :=
  (show Monotone (ofGrid : Grid n → UnitInterval K) from fun _ _ h =>
    ofGrid_le_iff.mpr h).map_min

theorem ofGrid_or {n : ℕ} (x y : Grid n) :
    (ofGrid (Goedel.or x y) : UnitInterval K) = Goedel.or (ofGrid x) (ofGrid y) :=
  (show Monotone (ofGrid : Grid n → UnitInterval K) from fun _ _ h =>
    ofGrid_le_iff.mpr h).map_max

theorem ofGrid_goedelImp {n : ℕ} (x y : Grid n) :
    (ofGrid (Goedel.imp x y) : UnitInterval K) = Goedel.imp (ofGrid x) (ofGrid y) := by
  simp only [Goedel.imp, ofGrid_le_iff]
  split <;> simp [ofGrid_top]

theorem ofGrid_goedelNeg {n : ℕ} (x : Grid n) :
    (ofGrid (Goedel.neg x) : UnitInterval K) = Goedel.neg (ofGrid x) := by
  rw [Goedel.neg, Goedel.neg, ofGrid_goedelImp, ofGrid_bot]

theorem ofGrid_lukNeg {n : ℕ} (x : Grid n) :
    (ofGrid (Grid.lukNeg x) : UnitInterval K) = lukNeg (ofGrid x) := by
  apply Subtype.ext
  have hx : x.val ≤ n + 1 := by omega
  change ((n + 1 - x.val : ℕ) : K) / ((n : K) + 1) =
    1 - (x.val : K) / ((n : K) + 1)
  rw [Nat.cast_sub hx, Nat.cast_add, Nat.cast_one, sub_div, div_self (grid_denom_pos n).ne']

theorem ofGrid_lukImp {n : ℕ} (x y : Grid n) :
    (ofGrid (Grid.lukImp x y) : UnitInterval K) = lukImp (ofGrid x) (ofGrid y) := by
  apply Subtype.ext
  have hx : x.val ≤ n + 1 + y.val := by have := x.isLt; omega
  change ((min (n + 1) (n + 1 + y.val - x.val) : ℕ) : K) / ((n : K) + 1) =
    min 1 (1 - (x.val : K) / ((n : K) + 1) + (y.val : K) / ((n : K) + 1))
  have hd := grid_denom_pos (K := K) n
  have h : ((n : K) + 1 + (y.val : K) - (x.val : K)) / ((n : K) + 1) =
      1 - (x.val : K) / ((n : K) + 1) + (y.val : K) / ((n : K) + 1) := by
    rw [sub_div, add_div, div_self hd.ne', add_sub_right_comm]
  simp only [Nat.cast_min, Nat.cast_sub hx, Nat.cast_add, Nat.cast_one]
  rw [← min_div_div_right hd.le, h, div_self hd.ne']

theorem ofGrid_lukAnd {n : ℕ} (x y : Grid n) :
    (ofGrid (Grid.lukAnd x y) : UnitInterval K) = lukAnd (ofGrid x) (ofGrid y) := by
  apply Subtype.ext
  change ((x.val + y.val - (n + 1) : ℕ) : K) / ((n : K) + 1) =
    max 0 ((x.val : K) / ((n : K) + 1) + (y.val : K) / ((n : K) + 1) - 1)
  have hd : (n : K) + 1 ≠ 0 := (grid_denom_pos n).ne'
  by_cases h : n + 1 ≤ x.val + y.val
  · rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_add, Nat.cast_one, sub_div, add_div, div_self hd]
    rw [max_eq_right]
    apply sub_nonneg.mpr
    rw [← add_div, one_le_div (grid_denom_pos n)]
    exact_mod_cast h
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), Nat.cast_zero, zero_div, max_eq_left]
    apply sub_nonpos.mpr
    rw [← add_div, div_le_one (grid_denom_pos n)]
    exact_mod_cast (le_of_not_ge h)

theorem ofRat_le_iff {x y : UnitInterval ℚ} : ofRat x ≤ ofRat y ↔ x ≤ y := by
  exact Rat.cast_le (K := ℝ)

theorem ofRat_top : ofRat (⊤ : UnitInterval ℚ) = ⊤ := by
  apply Subtype.ext
  exact Rat.cast_one

theorem ofRat_bot : ofRat (⊥ : UnitInterval ℚ) = ⊥ := by
  apply Subtype.ext
  exact Rat.cast_zero

theorem ofRat_lukNeg (x : UnitInterval ℚ) : ofRat (lukNeg x) = lukNeg (ofRat x) := by
  apply Subtype.ext
  change ((1 - x.val : ℚ) : ℝ) = 1 - (x.val : ℝ)
  rw [Rat.cast_sub, Rat.cast_one]

theorem ofRat_lukImp (x y : UnitInterval ℚ) :
    ofRat (lukImp x y) = lukImp (ofRat x) (ofRat y) := by
  apply Subtype.ext
  change ((min 1 (1 - x.val + y.val) : ℚ) : ℝ) = min 1 (1 - (x.val : ℝ) + (y.val : ℝ))
  rw [Rat.cast_min, Rat.cast_add, Rat.cast_sub, Rat.cast_one]

theorem ofRat_lukAnd (x y : UnitInterval ℚ) :
    ofRat (lukAnd x y) = lukAnd (ofRat x) (ofRat y) := by
  apply Subtype.ext
  change ((max 0 (x.val + y.val - 1) : ℚ) : ℝ) = max 0 ((x.val : ℝ) + (y.val : ℝ) - 1)
  rw [Rat.cast_max, Rat.cast_sub, Rat.cast_add, Rat.cast_zero, Rat.cast_one]

end UnitInterval

end Silmaril.Proofs.Logic.ManyValuedCatalogue
