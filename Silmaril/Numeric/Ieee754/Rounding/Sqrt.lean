module

public import Silmaril.Numeric.Ieee754.Rounding.Division

/-! # Uniform error of the executable square-root residual rounder

The residual specification refers to the exact real square root, including
irrational roots. No intermediate rational approximation of the root is assumed.
-/

@[expose] public section
namespace Silmaril.Numeric.Ieee754.Rounding
open Float.Model Float.Model.UnpackedFloat LowPrecision

theorem sqrt_ge_lower (n : Nat) (e : Int) (hn : 0 < n) :
    (2 : ℝ) ^ ((totalExponent n e + 1) / 2 - 1) ≤
      Real.sqrt ((n : ℝ) * (2 : ℝ) ^ e) := by
  have hnl : (2 : ℝ) ^ n.log2 ≤ (n : ℝ) := by
    exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hn)
  have hl : (2 : ℝ) ^ (totalExponent n e - 1) ≤ (n : ℝ) * (2 : ℝ) ^ e := by
    have he : totalExponent n e - 1 = (n.log2 : Int) + e := by
      simp only [totalExponent]
      omega
    rw [he, zpow_add₀ (by norm_num), zpow_natCast]
    exact mul_le_mul_of_nonneg_right hnl (le_of_lt (zpow_pos (by norm_num) _))
  have hs : ((2 : ℝ) ^ ((totalExponent n e + 1) / 2 - 1)) ^ 2 ≤
      (n : ℝ) * (2 : ℝ) ^ e := by
    apply le_trans _ hl
    rw [pow_two, ← zpow_add₀ (by norm_num)]
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  have hnonneg : 0 ≤ (n : ℝ) * (2 : ℝ) ^ e :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos (by norm_num) _))
  have hroot := Real.sq_sqrt hnonneg
  have hroot0 := Real.sqrt_nonneg ((n : ℝ) * (2 : ℝ) ^ e)
  have hp := zpow_pos (by norm_num : (0 : ℝ) < 2) ((totalExponent n e + 1) / 2 - 1)
  nlinarith

theorem sqrtCore_ready (format : Format) (n : Nat) (e : Int) (hn : 0 < n) :
    let core := sqrtCore format n e
    core.2.1 ≤ format.targetExponent (totalExponent core.1 core.2.1) := by
  let core := sqrtCore format n e
  change core.2.1 ≤ format.targetExponent (totalExponent core.1 core.2.1)
  have he : core.2.1 ≤ format.targetExponent ((totalExponent n e + 1) / 2) := min_le_right _ _
  by_cases hmin : core.2.1 ≤ format.minExponent
  · exact hmin.trans (le_max_right _ _)
  · have ht : core.2.1 ≤ (totalExponent n e + 1) / 2 - format.mantissaBits := by
      dsimp [Format.targetExponent] at he
      omega
    have hpow : (2 : ℝ) ^ ((format.mantissaBits - 1 : Nat) : Int) ≤
        (2 : ℝ) ^ ((totalExponent n e + 1) / 2 - 1 - core.2.1) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
      omega
    have hroot := div_le_div_of_nonneg_right (sqrt_ge_lower n e hn)
      (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) core.2.1))
    rw [← zpow_sub₀ (by norm_num)] at hroot
    have hs := (Conformance.sqrtCore_accuracySound format n e).bounds.2
    have hm : 2 ^ (format.mantissaBits - 1) ≤ core.1 := by
      have hr : (2 : ℝ) ^ (format.mantissaBits - 1) < (core.1 : ℝ) + 1 := by
        rw [← zpow_natCast]
        exact (hpow.trans hroot).trans_lt hs
      have hn' : (2 ^ (format.mantissaBits - 1) : Nat) < core.1 + 1 := by exact_mod_cast hr
      omega
    have hpos : core.1 ≠ 0 := by
      have hp : 0 < 2 ^ (format.mantissaBits - 1) := Nat.pow_pos (by decide)
      omega
    have hlog := (Nat.le_log2 hpos).mpr hm
    apply le_trans _ (le_max_left _ _)
    change core.2.1 ≤ (core.1.log2 : Int) + 1 + core.2.1 - format.mantissaBits
    have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
    omega

theorem sqrtCore_relative_error (format : Format) (n : Nat) (e : Int) (hn : 0 < n) :
    let core := sqrtCore format n e
    let exact := Real.sqrt ((n : ℝ) * (2 : ℝ) ^ e)
    ∃ v : ℝ, Magnitude (roundWithAccuracy format .nearestTiesToEven .positive core.1 core.2.1 core.2.2) v ∧
      |v - exact| ≤ unitRoundoff format * exact + halfMinSubnormal format := by
  let core := sqrtCore format n e
  have h := roundWithAccuracy_relative_error format .positive core.1 core.2.1 core.2.2 _
    (Conformance.sqrtCore_accuracySound format n e) (sqrtCore_ready format n e hn)
  simpa only [core, div_mul_cancel₀ _ (zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))] using h

/-- The unbounded rounded result used by `sqrtRounded` before interchange packing. -/
def sqrtUnpacked (format : Format) (x : UnpackedFloat) : UnpackedFloat :=
  match x with
  | .finite .positive n e _ =>
    let core := sqrtCore format n e
    roundWithAccuracy format .nearestTiesToEven .positive core.1 core.2.1 core.2.2
  | _ => UnpackedFloat.sqrt format x

theorem sqrtRounded_eq_pack (format : Format) (x : UnpackedFloat) :
    sqrtRounded format .nearestTiesToEven x =
      packNormalized format .nearestTiesToEven (sqrtUnpacked format x) := rfl

theorem sqrtUnpacked_approx (format : Format) (x : UnpackedFloat) (a : ℚ)
    (hx : unpackedRat? x = some a) (ha : 0 ≤ a) :
    RoundedRealApprox format (sqrtUnpacked format x) (Real.sqrt (a : ℝ)) := by
  cases x with
  | notANumber | infinity => simp [unpackedRat?] at hx
  | zero sign =>
    have ha0 : a = 0 := by simpa [unpackedRat?] using hx.symm
    subst a
    refine ⟨trivial, 0, rfl, ?_⟩
    simp only [Rat.cast_zero, Real.sqrt_zero, sub_self, abs_zero, mul_zero, zero_add]
    exact div_nonneg (le_of_lt (zpow_pos (by norm_num) _)) (by norm_num)
  | finite sign n e hn =>
    cases sign with
    | negative =>
      have haeq : -((n : ℚ) * (2 : ℚ) ^ e) = a := by
        simpa [unpackedRat?, signedRat] using hx
      have hp : (0 : ℚ) < (n : ℚ) * (2 : ℚ) ^ e :=
        mul_pos (by exact_mod_cast hn) (zpow_pos (by norm_num) _)
      linarith
    | positive =>
      have haeq : (a : ℝ) = (n : ℝ) * (2 : ℝ) ^ e := by
        have h : (n : ℚ) * (2 : ℚ) ^ e = a := by
          simpa [unpackedRat?, signedRat] using hx
        rw [← h]
        simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat]
      let core := sqrtCore format n e
      obtain ⟨v, hv, he⟩ := sqrtCore_relative_error format n e hn
      obtain ⟨r, hr, hreal⟩ := unpackedRat_of_magnitude
        (roundWithAccuracy_sign format _ .positive core.1 core.2.1 core.2.2) hv
      refine ⟨roundWithAccuracy_canonical_of_ready format _ .positive core.1 core.2.1 core.2.2
        (sqrtCore_ready format n e hn), r, hr, ?_⟩
      rw [hreal, haeq, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact he

end Silmaril.Numeric.Ieee754.Rounding
