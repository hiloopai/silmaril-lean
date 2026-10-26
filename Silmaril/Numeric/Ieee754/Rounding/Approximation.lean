module

public import Silmaril.Numeric.Ieee754.Rounding.Range
public import Silmaril.Numeric.Ieee754.RoundingCorrectness

/-! # Shared residual rounding and real-valued approximation certificates

A sound residual and an adequately fine exponent grid give a uniform error
bound. Canonical finite results can then be range-checked and packed without
changing their rational value. Exact references may be irrational.
-/

@[expose] public section
namespace Silmaril.Numeric.Ieee754.Rounding
open Float.Model Float.Model.UnpackedFloat LowPrecision

theorem residual_of_accuracySound (n : Nat) (a : Accuracy) (q : ℝ)
    (h : Conformance.AccuracySound n a q) : Residual a (q - n) := by
  cases a with
  | exact => simp only [Conformance.AccuracySound] at h; simp [Residual, h]
  | inexact order =>
    cases order <;> simp only [Conformance.AccuracySound] at h <;>
      simp only [Residual] <;> rcases h with ⟨hl, hu, hm⟩ <;>
      (try constructor) <;> linarith

/-- Relative-plus-underflow error for a sound residual on an adequately
fine exponent grid. The exact magnitude may be non-dyadic. -/
theorem roundWithAccuracy_relative_error (format : Format) (sign : Sign)
    (n : Nat) (e : Int) (a : Accuracy) (q : ℝ)
    (sound : Conformance.AccuracySound n a q)
    (ready : e ≤ format.targetExponent (totalExponent n e)) :
    ∃ v : ℝ, Magnitude (roundWithAccuracy format .nearestTiesToEven sign n e a) v ∧
      |v - q * (2 : ℝ) ^ e| ≤ unitRoundoff format * (q * (2 : ℝ) ^ e) + halfMinSubnormal format := by
  obtain ⟨v, hv, he⟩ := roundWithAccuracy_nearestEven_error format sign n e
    (residual_of_accuracySound n a q sound)
  have heq : ((n : ℝ) + (q - n)) * (2 : ℝ) ^ e = q * (2 : ℝ) ^ e := by ring
  rw [heq, Conformance.shiftToTargetExponent_exponent_eq format n e a ready] at he
  refine ⟨v, hv, he.trans ?_⟩
  by_cases hn : n = 0
  · subst n
    have ht : format.targetExponent (totalExponent 0 e) = format.minExponent := by
      have hp := format.hm
      simp only [totalExponent, Nat.log2_zero, Nat.cast_zero, zero_add,
        Format.targetExponent, Format.mantissaBits, Nat.cast_add, Nat.cast_one] at ready ⊢
      omega
    rw [ht]
    change halfMinSubnormal format ≤ _
    have hnonneg : 0 ≤ unitRoundoff format * (q * (2 : ℝ) ^ e) :=
      mul_nonneg (le_of_lt (zpow_pos (by norm_num) _))
        (mul_nonneg sound.nonneg (le_of_lt (zpow_pos (by norm_num) _)))
    linarith
  · have hq := mul_le_mul_of_nonneg_right sound.bounds.1
      (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e))
    have hu := mul_le_mul_of_nonneg_left hq
      (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) (-(format.mantissaBits : Int))))
    have hh := halfQuantum_le format n e (Nat.pos_of_ne_zero hn)
    unfold unitRoundoff at hh ⊢
    linarith

theorem roundWithAccuracy_canonical_of_ready (format : Format) (mode : RoundingMode)
    (sign : Sign) (n : Nat) (e : Int) (a : Accuracy)
    (ready : e ≤ format.targetExponent (totalExponent n e)) :
    CanonicalValue format (roundWithAccuracy format mode sign n e a) := by
  have hn := Conformance.roundWithAccuracy_normalized format mode sign n e a ready
  have hm := roundWithAccuracy_magnitude format mode sign n e a
  cases hv : roundWithAccuracy format mode sign n e a with
  | notANumber | infinity => simp [hv, Magnitude] at hm
  | zero => trivial
  | finite s m exponent hp =>
    rw [hv] at hn
    obtain ⟨hmin, hmax, hlow⟩ := Conformance.ExponentNormalized.finite_bounds format s m exponent hp hn
    refine ⟨hmax, hmin, ?_⟩
    intro hsub
    rcases hlow with he | hl
    · exact he
    · simp only [Format.mantissaBits, Nat.add_sub_cancel_left] at hl
      omega

theorem roundWithAccuracy_sign (format : Format) (mode : RoundingMode) (sign : Sign)
    (n : Nat) (e : Int) (a : Accuracy) :
    HasSign sign (roundWithAccuracy format mode sign n e a) := by
  unfold roundWithAccuracy
  dsimp only
  split <;> rfl

/-- A reusable certificate for the unbounded rounded result, before checking
the destination exponent range. -/
structure RoundedRealApprox (format : Format) (value : UnpackedFloat) (exact : ℝ) : Prop where
  canonical : CanonicalValue format value
  finite_error : ∃ r : ℚ, unpackedRat? value = some r ∧
    |(r : ℝ) - exact| ≤ unitRoundoff format * |exact| + halfMinSubnormal format

theorem RoundedRealApprox.noOverflow {format : Format} {value : UnpackedFloat} {q : ℝ}
    (h : RoundedRealApprox format value q)
    (bound : (1 + unitRoundoff format) * |q| + halfMinSubnormal format < overflowThreshold format) :
    NoOverflow format value := by
  obtain ⟨r, hr, he⟩ := h.finite_error
  have hm := magnitude_of_unpackedRat hr
  have ht := abs_add_le ((r : ℝ) - q) q
  have hid : (r : ℝ) - q + q = r := by ring
  rw [hid] at ht
  apply noOverflow_of_magnitude_lt format value |(r : ℝ)| h.canonical hm
  nlinarith

theorem RoundedRealApprox.packed_error {format : Format} {value : UnpackedFloat} {q : ℝ}
    (h : RoundedRealApprox format value q) (safe : NoOverflow format value) :
    ∃ r : ℚ, exactValue? (coreSpec format)
      (packNormalized format .nearestTiesToEven value).toNat = some r ∧
      |(r : ℝ) - q| ≤ unitRoundoff format * |q| + halfMinSubnormal format := by
  obtain ⟨r, hr, he⟩ := h.finite_error
  refine ⟨r, ?_, he⟩
  rw [packNormalized_nearestEven, pack_value format value h.canonical safe]
  exact hr

/-- Compatibility spelling for exact rational operations. The underlying
certificate and range/packing proofs also support irrational real references. -/
abbrev RoundedApprox (format : Format) (value : UnpackedFloat) (exact : ℚ) : Prop :=
  RoundedRealApprox format value (exact : ℝ)

theorem RoundedApprox.noOverflow {format : Format} {value : UnpackedFloat} {q : ℚ}
    (h : RoundedApprox format value q)
    (bound : (1 + unitRoundoff format) * |(q : ℝ)| + halfMinSubnormal format < overflowThreshold format) :
    NoOverflow format value := RoundedRealApprox.noOverflow h bound

theorem RoundedApprox.packed_error {format : Format} {value : UnpackedFloat} {q : ℚ}
    (h : RoundedApprox format value q) (safe : NoOverflow format value) :
    ∃ r : ℚ, exactValue? (coreSpec format)
      (packNormalized format .nearestTiesToEven value).toNat = some r ∧
      |(r : ℝ) - (q : ℝ)| ≤ unitRoundoff format * |(q : ℝ)| + halfMinSubnormal format :=
  RoundedRealApprox.packed_error h safe

end Silmaril.Numeric.Ieee754.Rounding
