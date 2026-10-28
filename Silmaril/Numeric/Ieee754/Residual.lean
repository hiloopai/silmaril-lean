module

public import Silmaril.Numeric.Ieee754.MantissaCorrectness
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Sqrt

/-!
# Soundness of IEEE rounding residuals

These proofs connect the core model's round/sticky bits and quotient/root
residuals to mathematical magnitudes. They feed `roundMantissa_correct`;
format normalization and bounded exponent packing are separate obligations.
IEEE 754-2019 §§4.3 and 5.4.1:
<https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section
namespace Silmaril.Numeric.Ieee754.Conformance
open Float.Model Float.Model.UnpackedFloat
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- One right shift preserves the residual classification after rescaling by two. -/
theorem shiftRightOne_sound (em : ExtendedMantissa) (q : K)
    (h : AccuracySound em.mantissa em.accuracy q) :
    AccuracySound em.shiftRightOne.mantissa em.shiftRightOne.accuracy (q / 2) := by
  rcases em with ⟨n, rb, sb⟩
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have he : (n : K) = 2 * (n / 2 : Nat) + (n % 2 : Nat) := by
    exact_mod_cast (Nat.mod_add_div n 2).symm.trans (by omega)
  rcases hn with hn | hn <;> rw [hn] at he <;>
    cases rb <;> cases sb <;>
    simp_all [ExtendedMantissa.shiftRightOne, ExtendedMantissa.accuracy, AccuracySound] <;>
    (try rcases h with ⟨hlo, hhi, hmid⟩) <;>
    (repeat' apply And.intro) <;> linarith

/-- Repeated shifts preserve all information needed by every rounding direction. -/
theorem shiftRight_sound (em : ExtendedMantissa) (amount : Nat) (q : K)
    (h : AccuracySound em.mantissa em.accuracy q) :
    AccuracySound (em >>> amount).mantissa (em >>> amount).accuracy (q / 2 ^ amount) := by
  induction amount with
  | zero =>
    change AccuracySound em.mantissa em.accuracy (q / (2 : K) ^ 0)
    simpa using h
  | succ amount ih =>
    have hs := shiftRightOne_sound (em >>> amount) (q / 2 ^ amount) ih
    simpa [HShiftRight.hShiftRight, Nat.repeat, pow_succ, div_div] using hs

omit [IsStrictOrderedRing K] in
/-- Initializing round/sticky bits preserves the given residual classification. -/
theorem ofMantissaAndAccuracy_sound (n : Nat) (accuracy : Accuracy) (q : K)
    (h : AccuracySound n accuracy q) :
    AccuracySound (ExtendedMantissa.ofMantissaAndAccuracy n accuracy).mantissa
      (ExtendedMantissa.ofMantissaAndAccuracy n accuracy).accuracy q := by
  cases accuracy with
  | exact => exact h
  | inexact order => cases order <;> exact h

/-- Aligning to a requested exponent preserves the exact scaled magnitude. -/
theorem shiftToExponent_sound (n : Nat) (exponent target : Int) (accuracy : Accuracy)
    (q : K) (h : AccuracySound n accuracy q) :
    let shifted := shiftToExponent n exponent accuracy target
    AccuracySound shifted.1.mantissa shifted.1.accuracy
      (q / 2 ^ (target - exponent).toNat) :=
  shiftRight_sound _ _ _ (ofMantissaAndAccuracy_sound n accuracy q h)

/-- Rounding after an arbitrary right alignment meets the global integer-grid
specification. This includes gradual underflow alignment to a format's minimum
exponent; encoding the rounded result still requires the packing proof. -/
theorem shiftToExponent_round_correct (mode : RoundingMode) (sign : Sign)
    (n : Nat) (exponent target : Int) (accuracy : Accuracy)
    (q : K) (h : AccuracySound n accuracy q) :
    let shifted := shiftToExponent n exponent accuracy target
    MantissaRounds mode sign (q / 2 ^ (target - exponent).toNat)
      (Rounding.roundMantissa mode sign shifted.1.mantissa shifted.1.accuracy) :=
  roundMantissa_correct mode sign _ _ _ (shiftToExponent_sound n exponent target accuracy q h)

/-- Integer division's remainder determines the exact quotient's residual class. -/
theorem quotient_accuracySound (numerator denominator : Nat) (hd : 0 < denominator) :
    AccuracySound (numerator / denominator)
      (accuracyOfFraction (numerator % denominator) denominator)
      ((numerator : K) / denominator) := by
  have hdK : (0 : K) < denominator := by exact_mod_cast hd
  have hr : numerator % denominator < denominator := Nat.mod_lt _ hd
  have he : (numerator : K) = (denominator : K) * (numerator / denominator : Nat) +
      (numerator % denominator : Nat) := by
    exact_mod_cast (Nat.mod_add_div numerator denominator).symm.trans (by omega)
  unfold accuracyOfFraction
  split
  next hz =>
    change (numerator : K) / denominator = (numerator / denominator : Nat)
    apply (div_eq_iff (ne_of_gt hdK)).2
    rw [hz] at he
    nlinarith
  next hn =>
    have hrpos : (0 : K) < (numerator % denominator : Nat) := by
      exact_mod_cast (show 0 < numerator % denominator by omega)
    have hrK : (numerator % denominator : Nat) < (denominator : K) := by exact_mod_cast hr
    have hl : (numerator / denominator : Nat) < (numerator : K) / denominator := by
      apply (lt_div_iff₀ hdK).2
      nlinarith
    have hu : (numerator : K) / denominator < (numerator / denominator : Nat) + 1 := by
      apply (div_lt_iff₀ hdK).2
      nlinarith
    refine ⟨hl, hu, ?_⟩
    cases hc : compare (2 * (numerator % denominator)) denominator with
    | lt =>
      have hcK : 2 * (numerator % denominator : Nat) < (denominator : K) := by
        exact_mod_cast Nat.compare_eq_lt.mp hc
      change (numerator : K) / denominator < (numerator / denominator : Nat) + 1 / 2
      apply (div_lt_iff₀ hdK).2
      nlinarith
    | eq =>
      have hcK : 2 * (numerator % denominator : Nat) = (denominator : K) := by
        exact_mod_cast Nat.compare_eq_eq.mp hc
      change (numerator : K) / denominator = (numerator / denominator : Nat) + 1 / 2
      apply (div_eq_iff (ne_of_gt hdK)).2
      nlinarith
    | gt =>
      have hcK : (denominator : K) < 2 * (numerator % denominator : Nat) := by
        exact_mod_cast Nat.compare_eq_gt.mp hc
      change (numerator / denominator : Nat) + 1 / 2 < (numerator : K) / denominator
      apply (lt_div_iff₀ hdK).2
      nlinarith

/-- The integer square-root residual correctly locates the exact real root,
including the fact that an integer radicand never has a half-integer root. -/
theorem sqrt_accuracySound (n : Nat) :
    let root := Nat.sqrt n
    let remainder := n - root * root
    AccuracySound root
      (if remainder = 0 then .exact else .inexact (if remainder ≤ root then .lt else .gt))
      (Real.sqrt n) := by
  dsimp only
  have hr := Nat.sqrt_le n
  have hu := Nat.lt_succ_sqrt n
  have hs : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hroot : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  have hq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hrK : (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ n := by exact_mod_cast hr
  have huK : (n : ℝ) < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by exact_mod_cast hu
  have he : ((n - Nat.sqrt n * Nat.sqrt n : Nat) : ℝ) =
      n - (Nat.sqrt n : ℝ) * Nat.sqrt n := by
    rw [Nat.cast_sub hr, Nat.cast_mul]
  split
  next hz =>
    change Real.sqrt n = (Nat.sqrt n : ℝ)
    rw [hz] at he
    norm_num at he
    nlinarith
  next hn =>
    have hp : (0 : ℝ) < (n - Nat.sqrt n * Nat.sqrt n : Nat) := by
      exact_mod_cast (show 0 < n - Nat.sqrt n * Nat.sqrt n by omega)
    have hl : (Nat.sqrt n : ℝ) < Real.sqrt n := by nlinarith
    have hh : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := by nlinarith
    refine ⟨hl, hh, ?_⟩
    by_cases hle : n - Nat.sqrt n * Nat.sqrt n ≤ Nat.sqrt n
    · simp only [ite_eq_left hle]
      change Real.sqrt n < (Nat.sqrt n : ℝ) + 1 / 2
      have : ((n - Nat.sqrt n * Nat.sqrt n : Nat) : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hle
      nlinarith
    · simp only [ite_eq_right hle]
      change (Nat.sqrt n : ℝ) + 1 / 2 < Real.sqrt n
      have : (Nat.sqrt n : ℝ) + 1 ≤ (n - Nat.sqrt n * Nat.sqrt n : Nat) := by
        exact_mod_cast (show Nat.sqrt n + 1 ≤ n - Nat.sqrt n * Nat.sqrt n by omega)
      nlinarith

/-- The division core's residual is sound for the exact quotient measured in
units of its returned exponent, for every positive divisor significand. -/
theorem divCore_accuracySound (format : Format) (n d : Nat) (en ed : Int) (hd : 0 < d) :
    let result := divCore format n en d ed
    AccuracySound result.1 result.2.2
      (((n : K) * (2 : K) ^ en / ((d : K) * (2 : K) ^ ed)) / (2 : K) ^ result.2.1) := by
  let target := min (en - ed) (format.targetExponent (totalExponent n en - totalExponent d ed))
  let amount := (en - ed - target).toNat
  let numerator := n <<< amount
  have ht : target ≤ en - ed := min_le_left _ _
  have ha : (amount : Int) = en - ed - target := Int.toNat_of_nonneg (by omega)
  have hq : (numerator : K) / d =
      ((n : K) * (2 : K) ^ en / ((d : K) * (2 : K) ^ ed)) / (2 : K) ^ target := by
    simp only [numerator, Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← zpow_natCast (2 : K) amount, ha,
      zpow_sub₀ (by norm_num : (2 : K) ≠ 0), zpow_sub₀ (by norm_num : (2 : K) ≠ 0)]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  change AccuracySound (numerator / d) (accuracyOfFraction (numerator % d) d)
    (((n : K) * (2 : K) ^ en / ((d : K) * (2 : K) ^ ed)) / (2 : K) ^ target)
  rw [← hq]
  exact quotient_accuracySound numerator d hd

/-- The square-root core's residual is sound for the exact real square root
measured in units of its returned exponent, including irrational roots. -/
theorem sqrtCore_accuracySound (format : Format) (n : Nat) (exponent : Int) :
    let result := sqrtCore format n exponent
    AccuracySound result.1 result.2.2
      (Real.sqrt ((n : ℝ) * (2 : ℝ) ^ exponent) / (2 : ℝ) ^ result.2.1) := by
  let target := min (exponent / 2) (format.targetExponent ((totalExponent n exponent + 1) / 2))
  let amount := (exponent - 2 * target).toNat
  let radicand := n <<< amount
  have ht : target ≤ exponent / 2 := min_le_left _ _
  have ha : (amount : Int) = exponent - 2 * target := Int.toNat_of_nonneg (by omega)
  have hscale : (radicand : ℝ) = (n : ℝ) * (2 : ℝ) ^ exponent / ((2 : ℝ) ^ target) ^ 2 := by
    simp only [radicand, Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← zpow_natCast (2 : ℝ) amount, ha, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),
      show 2 * target = target + target by omega,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hq : Real.sqrt (radicand : ℝ) =
      Real.sqrt ((n : ℝ) * (2 : ℝ) ^ exponent) / (2 : ℝ) ^ target := by
    rw [hscale, Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos (by norm_num) _))),
      Real.sqrt_sq (le_of_lt (zpow_pos (by norm_num) _))]
  have hs := sqrt_accuracySound radicand
  rw [hq] at hs
  exact hs

end Silmaril.Numeric.Ieee754.Conformance
