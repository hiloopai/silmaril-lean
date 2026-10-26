module

public import Silmaril.Numeric.Ieee754.ConversionCorrectness
public import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Ring

/-! # Correctness of comparison on canonical unpacked values

The executable comparison orders finite significands lexicographically by
exponent and mantissa. Its canonical-form precondition is essential: arbitrary
unnormalized representations of equal dyadics need not compare equal.
-/

@[expose] public section
namespace Silmaril.Numeric.Ieee754.Conformance
open Float.Model Float.Model.UnpackedFloat

private theorem magnitude_lt_of_exponent_lt (format : Format)
    (sx sy : Sign) (mx my : Nat) (ex ey : Int) (px : 0 < mx) (py : 0 < my)
    (hx : ExponentNormalized format (.finite sx mx ex px))
    (hy : ExponentNormalized format (.finite sy my ey py)) (h : ex < ey) :
    (mx : ℚ) * 2 ^ ex < (my : ℚ) * 2 ^ ey := by
  obtain ⟨hminx, hmaxx, _⟩ := hx.finite_bounds format sx mx ex px
  obtain ⟨_, _, hlowy⟩ := hy.finite_bounds format sy my ey py
  have hlowy : 2 ^ format.mantissaBitsWithoutImplicit ≤ my := by
    simp only [Format.mantissaBits, Nat.add_sub_cancel_left] at hlowy
    rcases hlowy with he | hm
    · omega
    · exact hm
  have hmaxx : (mx : ℚ) < 2 ^ format.mantissaBits := by exact_mod_cast hmaxx
  have hlowy : (2 : ℚ) ^ format.mantissaBitsWithoutImplicit ≤ my := by exact_mod_cast hlowy
  calc
    (mx : ℚ) * 2 ^ ex < 2 ^ format.mantissaBits * 2 ^ ex :=
      mul_lt_mul_of_pos_right hmaxx (zpow_pos (by norm_num) _)
    _ = 2 ^ format.mantissaBitsWithoutImplicit * 2 ^ (ex + 1) := by
      simp only [Format.mantissaBits, pow_add, pow_one,
        zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
      ring
    _ ≤ 2 ^ format.mantissaBitsWithoutImplicit * 2 ^ ey :=
      mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) (by omega))
        (by positivity)
    _ ≤ (my : ℚ) * 2 ^ ey :=
      mul_le_mul_of_nonneg_right hlowy (le_of_lt (zpow_pos (by norm_num) _))

private theorem compare_magnitude (format : Format)
    (sx sy : Sign) (mx my : Nat) (ex ey : Int) (px : 0 < mx) (py : 0 < my)
    (hx : ExponentNormalized format (.finite sx mx ex px))
    (hy : ExponentNormalized format (.finite sy my ey py)) :
    (compare ex ey).then (compare mx my) =
      compare ((mx : ℚ) * 2 ^ ex) ((my : ℚ) * 2 ^ ey) := by
  rcases lt_trichotomy ex ey with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    exact (compare_lt_iff_lt.mpr (magnitude_lt_of_exponent_lt format sx sy mx my ex ey px py hx hy h)).symm
  · subst ey
    rw [compare_eq_iff_eq.mpr rfl]
    dsimp only [Ordering.then]
    rcases lt_trichotomy mx my with h | h | h
    · rw [compare_lt_iff_lt.mpr h]
      exact (compare_lt_iff_lt.mpr
        (mul_lt_mul_of_pos_right (by exact_mod_cast h) (zpow_pos (by norm_num) ex))).symm
    · subst my
      simp
    · rw [compare_gt_iff_gt.mpr h]
      exact (compare_gt_iff_gt.mpr
        (mul_lt_mul_of_pos_right (by exact_mod_cast h) (zpow_pos (by norm_num) ex))).symm
  · rw [compare_gt_iff_gt.mpr h]
    exact (compare_gt_iff_gt.mpr (magnitude_lt_of_exponent_lt format sy sx my mx ey ex py px hy hx h)).symm

private theorem compare_neg_rat (a b : ℚ) : compare (-a) (-b) = (compare a b).swap := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr (neg_lt_neg h)]
    rfl
  · subst b
    simp
  · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr (neg_lt_neg h)]
    rfl

/-- The actual unpacked comparison agrees with rational order for finite
canonical operands in one common format, including both signed zeros. -/
theorem compare_finite (format : Format) (x y : UnpackedFloat) (a b : ℚ)
    (nx : ExponentNormalized format x) (ny : ExponentNormalized format y)
    (hx : value? x = some a) (hy : value? y = some b) :
    x.compare y = some (compare a b) := by
  cases x with
  | notANumber | infinity => simp [value?] at hx
  | zero sx =>
    have ha : a = 0 := by simpa using hx.symm
    subst a
    cases y with
    | notANumber | infinity => simp [value?] at hy
    | zero sy =>
      have hb : b = 0 := by simpa using hy.symm
      subst b
      simp [UnpackedFloat.compare]
    | finite sy my ey py =>
      simp only [value?, Option.some.injEq] at hy
      subst b
      have hp : (0 : ℚ) < my * 2 ^ ey := mul_pos (by exact_mod_cast py) (zpow_pos (by norm_num) _)
      cases sy <;> simp only [UnpackedFloat.compare, Sign.apply, dyadic, Int.cast_natCast, Int.cast_neg]
      · rw [neg_mul, compare_gt_iff_gt.mpr (neg_neg_of_pos hp)]
      · rw [compare_lt_iff_lt.mpr hp]
  | finite sx mx ex px =>
    simp only [value?, Option.some.injEq] at hx
    subst a
    have hpx : (0 : ℚ) < mx * 2 ^ ex := mul_pos (by exact_mod_cast px) (zpow_pos (by norm_num) _)
    cases y with
    | notANumber | infinity => simp [value?] at hy
    | zero sy =>
      have hb : b = 0 := by simpa using hy.symm
      subst b
      cases sx <;> simp only [UnpackedFloat.compare, Sign.apply, dyadic, Int.cast_natCast, Int.cast_neg]
      · rw [neg_mul, compare_lt_iff_lt.mpr (neg_neg_of_pos hpx)]
      · rw [compare_gt_iff_gt.mpr hpx]
    | finite sy my ey py =>
      simp only [value?, Option.some.injEq] at hy
      subst b
      have hpy : (0 : ℚ) < my * 2 ^ ey := mul_pos (by exact_mod_cast py) (zpow_pos (by norm_num) _)
      cases sx <;> cases sy <;>
        simp only [UnpackedFloat.compare, Sign.apply, dyadic, Int.cast_natCast, Int.cast_neg]
      · rw [neg_mul, neg_mul, compare_neg_rat,
          compare_magnitude format .negative .negative mx my ex ey px py nx ny]
      · rw [neg_mul, compare_lt_iff_lt.mpr (lt_trans (neg_neg_of_pos hpx) hpy)]
      · rw [neg_mul, compare_gt_iff_gt.mpr (lt_trans (neg_neg_of_pos hpy) hpx)]
      · rw [compare_magnitude format .positive .positive mx my ex ey px py nx ny]

end Silmaril.Numeric.Ieee754.Conformance
