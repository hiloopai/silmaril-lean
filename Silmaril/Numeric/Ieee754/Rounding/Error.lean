module

public import Silmaril.Numeric.Ieee754.Normalization
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Mathematical meaning of mantissa rounding and residual bits

These lemmas relate the executable rounding code to real residuals measured in
units of the truncated mantissa. They are the first layer of a full format-level
rounding theorem; packing, exponent selection, and overflow are separate.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Rounding

open Float.Model Float.Model.UnpackedFloat

/-- The exact fractional remainder summarized by `Accuracy`. -/
def Residual : Accuracy → ℝ → Prop
  | .exact, r => r = 0
  | .inexact .lt, r => 0 < r ∧ r < 1 / 2
  | .inexact .eq, r => r = 1 / 2
  | .inexact .gt, r => 1 / 2 < r ∧ r < 1

theorem Residual.range {accuracy : Accuracy} {r : ℝ} (h : Residual accuracy r) :
    0 ≤ r ∧ r < 1 := by
  cases accuracy with
  | exact => simp only [Residual] at h; subst r; norm_num
  | inexact order => cases order <;> simp only [Residual] at h <;> constructor <;> linarith

/-- The actual nearest-even mantissa routine has absolute error at most half a unit. -/
theorem roundMantissa_nearestEven_error (sign : Sign) (mantissa : Nat)
    {accuracy : Accuracy} {r : ℝ} (h : Residual accuracy r) :
    |(roundMantissa .nearestTiesToEven sign mantissa accuracy : ℝ) - (mantissa + r)| ≤ 1 / 2 := by
  cases accuracy with
  | exact => simp [Residual] at h; subst r; simp
  | inexact order =>
    cases order with
    | lt =>
      simp only [Residual] at h
      simp only [roundMantissa, Accuracy.roundToNearestEven]
      rw [abs_le]
      constructor <;> linarith
    | eq =>
      simp only [Residual] at h
      have hp := Nat.mod_lt mantissa (by decide : 0 < 2)
      have hm : mantissa % 2 = 0 ∨ mantissa % 2 = 1 := by omega
      rcases hm with hm | hm <;>
        simp only [roundMantissa, Accuracy.roundToNearestEven, hm, Nat.cast_add, Nat.cast_zero, Nat.cast_one] <;>
        rw [abs_le] <;> constructor <;> linarith
    | gt =>
      simp only [Residual] at h
      simp only [roundMantissa, Accuracy.roundToNearestEven, Nat.cast_add, Nat.cast_one]
      rw [abs_le]
      constructor <;> linarith

/-- One right shift preserves the mathematical meaning of the residual bits. -/
theorem shiftRightOne_residual (em : ExtendedMantissa) {r : ℝ} (h : Residual em.accuracy r) :
    Residual em.shiftRightOne.accuracy ((((em.mantissa % 2 : Nat) : ℝ) + r) / 2) := by
  rcases em with ⟨m, rb, sb⟩
  have hp := Nat.mod_lt m (by decide : 0 < 2)
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hm with hm | hm <;> cases rb <;> cases sb <;>
    simp_all [ExtendedMantissa.shiftRightOne, ExtendedMantissa.accuracy, Residual]
  all_goals (try constructor) <;> norm_num at * <;> linarith

/-- Exact value identity for the same shift, including its fractional residual. -/
theorem shiftRightOne_value (em : ExtendedMantissa) (r : ℝ) :
    (em.mantissa : ℝ) + r =
      2 * ((em.shiftRightOne.mantissa : ℝ) + (((em.mantissa % 2 : Nat) : ℝ) + r) / 2) := by
  have hm : (em.mantissa : ℝ) = 2 * (em.mantissa / 2 : Nat) + (em.mantissa % 2 : Nat) := by
    exact_mod_cast (Nat.mod_add_div em.mantissa 2).symm.trans (by omega)
  simp only [ExtendedMantissa.shiftRightOne]
  linarith

/-- Repeated executable shifts preserve an exact value decomposition. -/
theorem shiftRight_residual (em : ExtendedMantissa) (n : Nat) {r : ℝ}
    (h : Residual em.accuracy r) :
    ∃ r' : ℝ, Residual (Nat.repeat ExtendedMantissa.shiftRightOne n em).accuracy r' ∧
      (em.mantissa : ℝ) + r = (2 : ℝ) ^ n *
        ((Nat.repeat ExtendedMantissa.shiftRightOne n em).mantissa + r') := by
  induction n with
  | zero => exact ⟨r, h, by simp [Nat.repeat]⟩
  | succ n ih =>
    obtain ⟨r', hr, hv⟩ := ih
    let shifted := Nat.repeat ExtendedMantissa.shiftRightOne n em
    refine ⟨(((shifted.mantissa % 2 : Nat) : ℝ) + r') / 2,
      shiftRightOne_residual shifted hr, ?_⟩
    calc
      _ = (2 : ℝ) ^ n * ((shifted.mantissa : ℝ) + r') := hv
      _ = _ := by
        rw [shiftRightOne_value shifted r', pow_succ]
        simp only [Nat.repeat, shifted, mul_assoc]

/-- Quantizing after any number of right shifts has a half-ulp absolute bound. -/
theorem shiftRight_nearestEven_error (em : ExtendedMantissa) (n : Nat) (sign : Sign)
    {r : ℝ} (h : Residual em.accuracy r) :
    |(2 : ℝ) ^ n *
        (roundMantissa .nearestTiesToEven sign
          (Nat.repeat ExtendedMantissa.shiftRightOne n em).mantissa
          (Nat.repeat ExtendedMantissa.shiftRightOne n em).accuracy : ℝ) -
      ((em.mantissa : ℝ) + r)| ≤ (2 : ℝ) ^ n / 2 := by
  obtain ⟨r', hr, hv⟩ := shiftRight_residual em n h
  have he := roundMantissa_nearestEven_error sign
    (Nat.repeat ExtendedMantissa.shiftRightOne n em).mantissa hr
  rw [hv, ← mul_sub, abs_mul, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) n)]
  calc
    _ ≤ (2 : ℝ) ^ n * (1 / 2) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- The mantissa component of the executable bit shift is integer division. -/
theorem shiftRight_mantissa (em : ExtendedMantissa) (n : Nat) :
    (Nat.repeat ExtendedMantissa.shiftRightOne n em).mantissa = em.mantissa / 2 ^ n :=
  Conformance.extendedShift_mantissa em n

/-- Rounding can increase the truncated mantissa by at most one. -/
theorem roundMantissa_le_succ (mode : RoundingMode) (sign : Sign) (m : Nat) (a : Accuracy) :
    roundMantissa mode sign m a ≤ m + 1 :=
  (Conformance.roundMantissa_bracket mode sign m a).elim (fun h => by omega) (fun h => by omega)

/-- The first exponent selection always truncates to fewer than p significant bits. -/
theorem shifted_mantissa_lt (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    (shiftToTargetExponent format m e a).1.mantissa < 2 ^ format.mantissaBits :=
  Conformance.shiftToTargetExponent_mantissa_lt format m e a

/-- The exponent after the first shift is at least the format's subnormal minimum. -/
theorem shifted_exponent_min (format : Format) (m : Nat) (e : Int) (a : Accuracy) :
    format.minExponent ≤ (shiftToTargetExponent format m e a).2 :=
  Conformance.shiftToTargetExponent_exponent_ge format m e a

/-- The carry-normalization shift after rounding discards no value. -/
theorem normalize_rounded_exact (format : Format) (m : Nat) (e : Int)
    (hm : m ≤ 2 ^ format.mantissaBits) (he : format.minExponent ≤ e) :
    ((shiftToTargetExponent format m e .exact).1.mantissa : ℝ) *
        (2 : ℝ) ^ (shiftToTargetExponent format m e .exact).2 = (m : ℝ) * (2 : ℝ) ^ e :=
  Conformance.carryShift_value format m e hm he

def Magnitude : UnpackedFloat → ℝ → Prop
  | .zero _, v => v = 0
  | .finite _ m e _, v => v = (m : ℝ) * (2 : ℝ) ^ e
  | _, _ => False

/-- The final carry normalization leaves the once-rounded magnitude unchanged. -/
theorem roundWithAccuracy_magnitude (format : Format) (mode : RoundingMode)
    (sign : Sign) (m : Nat) (e : Int) (a : Accuracy) :
    let first := shiftToTargetExponent format m e a
    Magnitude (roundWithAccuracy format mode sign m e a)
      ((roundMantissa mode sign first.1.mantissa first.1.accuracy : ℝ) * (2 : ℝ) ^ first.2) := by
  let first := shiftToTargetExponent format m e a
  let rounded := roundMantissa mode sign first.1.mantissa first.1.accuracy
  have hm : rounded ≤ 2 ^ format.mantissaBits :=
    (roundMantissa_le_succ mode sign first.1.mantissa first.1.accuracy).trans
      (shifted_mantissa_lt format m e a)
  have hv := normalize_rounded_exact format rounded first.2 hm (shifted_exponent_min format m e a)
  change Magnitude (if h : (shiftToTargetExponent format rounded first.2 .exact).1.mantissa = 0
    then .zero sign else .finite sign (shiftToTargetExponent format rounded first.2 .exact).1.mantissa
      (shiftToTargetExponent format rounded first.2 .exact).2 (Nat.pos_of_ne_zero h))
    ((rounded : ℝ) * (2 : ℝ) ^ first.2)
  split
  next hz => simpa only [Magnitude, hz, Nat.cast_zero, zero_mul] using hv.symm
  next => exact hv.symm

/-- Scaling the executable right-shift/round sequence gives a half-ulp bound. -/
theorem firstRound_error (format : Format) (sign : Sign) (m : Nat) (e : Int)
    {a : Accuracy} {r : ℝ} (h : Residual a r) :
    let first := shiftToTargetExponent format m e a
    |(roundMantissa .nearestTiesToEven sign first.1.mantissa first.1.accuracy : ℝ) *
        (2 : ℝ) ^ first.2 - ((m : ℝ) + r) * (2 : ℝ) ^ e| ≤ (2 : ℝ) ^ first.2 / 2 := by
  let em := ExtendedMantissa.ofMantissaAndAccuracy m a
  let n := (format.targetExponent (totalExponent m e) - e).toNat
  have ha : Residual em.accuracy r := by
    cases a with
    | exact => exact h
    | inexact order => cases order <;> exact h
  have hm : em.mantissa = m := by
    cases a with
    | exact => rfl
    | inexact order => cases order <;> rfl
  have hbase := shiftRight_nearestEven_error em n sign ha
  rw [hm] at hbase
  have hscale := mul_le_mul_of_nonneg_right hbase (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e))
  change |(roundMantissa .nearestTiesToEven sign
      (Nat.repeat ExtendedMantissa.shiftRightOne n em).mantissa
      (Nat.repeat ExtendedMantissa.shiftRightOne n em).accuracy : ℝ) *
        (2 : ℝ) ^ (e + n) - ((m : ℝ) + r) * (2 : ℝ) ^ e| ≤ (2 : ℝ) ^ (e + n) / 2
  rw [zpow_add₀ (by norm_num), zpow_natCast]
  have hleft : ∀ t : ℝ, t * ((2 : ℝ) ^ e * 2 ^ n) - ((m : ℝ) + r) * (2 : ℝ) ^ e =
      ((2 : ℝ) ^ n * t - ((m : ℝ) + r)) * (2 : ℝ) ^ e := by intro t; ring
  rw [hleft, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) e)]
  convert hscale using 1
  ring

/-- Complete unbounded-exponent rounding has a half-ulp error bound.
This theorem concerns the actual rounder, including the carry normalization.
Finite-format packing and overflow are deliberately separate obligations. -/
theorem roundWithAccuracy_nearestEven_error (format : Format) (sign : Sign)
    (m : Nat) (e : Int) {a : Accuracy} {r : ℝ} (h : Residual a r) :
    ∃ v : ℝ, Magnitude (roundWithAccuracy format .nearestTiesToEven sign m e a) v ∧
      |v - ((m : ℝ) + r) * (2 : ℝ) ^ e| ≤
        (2 : ℝ) ^ (shiftToTargetExponent format m e a).2 / 2 :=
  ⟨_, roundWithAccuracy_magnitude format .nearestTiesToEven sign m e a,
    firstRound_error format sign m e h⟩

end Silmaril.Numeric.Ieee754.Rounding
