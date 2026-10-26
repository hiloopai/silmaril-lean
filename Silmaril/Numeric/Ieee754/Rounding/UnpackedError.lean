module

public import Silmaril.Numeric.Ieee754.Rounding.Error

/-! # Error of the executable unbounded-exponent rounder

The theorem includes gradual underflow. Packing overflow is not part of this
layer; a finite-format arithmetic theorem must discharge that additional step.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Rounding

open Float.Model Float.Model.UnpackedFloat

theorem log2_mul_pow_two (m n : Nat) (hm : m ≠ 0) : (m * 2 ^ n).log2 = m.log2 + n := by
  simpa only [Nat.shiftLeft_eq] using Conformance.log2_shiftLeft m n hm

theorem decreaseExponent_value (m : Nat) (e target : Int) :
    ((decreaseExponent m e target).1 : ℝ) * (2 : ℝ) ^ (decreaseExponent m e target).2 =
      (m : ℝ) * (2 : ℝ) ^ e := by
  let n := (e - target).toNat
  have hp : (2 : ℝ) ^ n * (2 : ℝ) ^ (e - n) = (2 : ℝ) ^ e := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    omega
  change ((m <<< n : Nat) : ℝ) * (2 : ℝ) ^ (e - n) = _
  rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, hp]

theorem decreaseExponent_total (m : Nat) (e target : Int) (hm : m ≠ 0) :
    totalExponent (decreaseExponent m e target).1 (decreaseExponent m e target).2 = totalExponent m e :=
  Conformance.decreaseExponent_totalExponent m e target hm

theorem roundUnpacked_exponent (format : Format) (m : Nat) (e : Int) (hm : m ≠ 0) :
    let target := format.targetExponent (totalExponent m e)
    let lowered := decreaseExponent m e target
    (shiftToTargetExponent format lowered.1 lowered.2 .exact).2 = target := by
  dsimp only
  simp only [shiftToTargetExponent, decreaseExponent_total m e _ hm, shiftToExponent]
  have hle : (decreaseExponent m e (format.targetExponent (totalExponent m e))).2 ≤
      format.targetExponent (totalExponent m e) := by
    simp only [decreaseExponent]
    omega
  omega

/-- The exact executable rounder has a half-ulp bound at its chosen exponent. -/
theorem roundUnpacked_nearestEven_error (format : Format) (sign : Sign)
    (m : Nat) (e : Int) (hm : 0 < m) :
    ∃ v : ℝ, Magnitude (roundUnpacked format .nearestTiesToEven (.finite sign m e hm)) v ∧
      |v - (m : ℝ) * (2 : ℝ) ^ e| ≤
        (2 : ℝ) ^ (format.targetExponent (totalExponent m e)) / 2 := by
  let target := format.targetExponent (totalExponent m e)
  let lowered := decreaseExponent m e target
  obtain ⟨v, hv, herr⟩ := roundWithAccuracy_nearestEven_error format sign lowered.1 lowered.2
    (a := .exact) (r := 0) rfl
  refine ⟨v, hv, ?_⟩
  simpa only [add_zero, lowered, target, decreaseExponent_value,
    roundUnpacked_exponent format m e (Nat.ne_of_gt hm)] using herr

noncomputable def unitRoundoff (format : Format) : ℝ := (2 : ℝ) ^ (-(format.mantissaBits : Int))
noncomputable def halfMinSubnormal (format : Format) : ℝ := (2 : ℝ) ^ format.minExponent / 2

/-- Half a quantum is bounded by relative roundoff plus the subnormal allowance. -/
theorem halfQuantum_le (format : Format) (m : Nat) (e : Int) (hm : 0 < m) :
    (2 : ℝ) ^ (format.targetExponent (totalExponent m e)) / 2 ≤
      unitRoundoff format * ((m : ℝ) * (2 : ℝ) ^ e) + halfMinSubnormal format := by
  have hl : (2 : ℝ) ^ m.log2 ≤ (m : ℝ) := by exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hm)
  have hscale := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hl (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e)))
    (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) (-(format.mantissaBits : Int))))
  have hid : (2 : ℝ) ^ (totalExponent m e - format.mantissaBits) / 2 =
      unitRoundoff format * ((2 : ℝ) ^ m.log2 * (2 : ℝ) ^ e) := by
    have he : totalExponent m e - format.mantissaBits =
        -(format.mantissaBits : Int) + ((m.log2 : Int) + e) + 1 := by unfold totalExponent; omega
    rw [he, zpow_add₀ (by norm_num), zpow_one, zpow_add₀ (by norm_num),
      zpow_add₀ (by norm_num), zpow_natCast]
    unfold unitRoundoff
    ring
  unfold Format.targetExponent
  rw [max_def]
  split
  · change halfMinSubnormal format ≤ _
    have hu : 0 ≤ unitRoundoff format * ((m : ℝ) * (2 : ℝ) ^ e) := by
      unfold unitRoundoff
      exact mul_nonneg (le_of_lt (zpow_pos (by norm_num) _))
        (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos (by norm_num) _)))
    linarith
  · rw [hid]
    have hη : 0 ≤ halfMinSubnormal format :=
      div_nonneg (le_of_lt (zpow_pos (by norm_num) _)) (by norm_num)
    change unitRoundoff format * ((2 : ℝ) ^ m.log2 * (2 : ℝ) ^ e) ≤ _
    exact hscale.trans (le_add_of_nonneg_right hη)

/-- Precision-dependent error with a separate gradual-underflow term. -/
theorem roundUnpacked_relative_error (format : Format) (sign : Sign)
    (m : Nat) (e : Int) (hm : 0 < m) :
    ∃ v : ℝ, Magnitude (roundUnpacked format .nearestTiesToEven (.finite sign m e hm)) v ∧
      |v - (m : ℝ) * (2 : ℝ) ^ e| ≤
        unitRoundoff format * ((m : ℝ) * (2 : ℝ) ^ e) + halfMinSubnormal format := by
  obtain ⟨v, hv, herr⟩ := roundUnpacked_nearestEven_error format sign m e hm
  exact ⟨v, hv, herr.trans (halfQuantum_le format m e hm)⟩

end Silmaril.Numeric.Ieee754.Rounding
