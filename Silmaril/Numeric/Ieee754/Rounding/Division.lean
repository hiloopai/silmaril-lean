module

public import Silmaril.Numeric.Ieee754.Rounding.Approximation

/-! # Relative error of the executable quotient-residual division rounder -/

@[expose] public section
namespace Silmaril.Numeric.Ieee754.Rounding
open Float.Model Float.Model.UnpackedFloat LowPrecision

private theorem sign_div_nn : (Sign.negative / Sign.negative) = Sign.positive := rfl
private theorem sign_div_np : (Sign.negative / Sign.positive) = Sign.negative := rfl
private theorem sign_div_pn : (Sign.positive / Sign.negative) = Sign.negative := rfl
private theorem sign_div_pp : (Sign.positive / Sign.positive) = Sign.positive := rfl

/-- A division quotient is strictly above the lower binade estimate formed
from the two input significands. The denominator's upper bound is strict. -/
theorem quotient_gt_lower (n d : Nat) (en ed : Int) (hn : 0 < n) (hd : 0 < d) :
    (2 : ℝ) ^ (totalExponent n en - totalExponent d ed - 1) <
      (n : ℝ) * (2 : ℝ) ^ en / ((d : ℝ) * (2 : ℝ) ^ ed) := by
  have hnl : (2 : ℝ) ^ n.log2 ≤ (n : ℝ) := by
    exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hn)
  have hdu : (d : ℝ) < (2 : ℝ) ^ (d.log2 + 1) := by exact_mod_cast Nat.lt_log2_self (n := d)
  have hdl : 0 < (d : ℝ) * (2 : ℝ) ^ ed := mul_pos (by exact_mod_cast hd) (zpow_pos (by norm_num) _)
  have hnum : 0 < (2 : ℝ) ^ ((n.log2 : Int) + en) := zpow_pos (by norm_num) _
  have hl : (2 : ℝ) ^ ((n.log2 : Int) + en) ≤ (n : ℝ) * (2 : ℝ) ^ en := by
    rw [zpow_add₀ (by norm_num), zpow_natCast]
    exact mul_le_mul_of_nonneg_right hnl (le_of_lt (zpow_pos (by norm_num) _))
  have hu : (d : ℝ) * (2 : ℝ) ^ ed < (2 : ℝ) ^ ((d.log2 : Int) + 1 + ed) := by
    rw [zpow_add₀ (by norm_num), show (d.log2 : Int) + 1 = ((d.log2 + 1 : Nat) : Int) by omega,
      zpow_natCast]
    exact mul_lt_mul_of_pos_right hdu (zpow_pos (by norm_num) _)
  have he : (2 : ℝ) ^ (totalExponent n en - totalExponent d ed - 1) =
      (2 : ℝ) ^ ((n.log2 : Int) + en) / (2 : ℝ) ^ ((d.log2 : Int) + 1 + ed) := by
    rw [← zpow_sub₀ (by norm_num)]
    congr 1
    simp only [totalExponent]
    omega
  rw [he]
  exact (div_lt_div_of_pos_left hnum hdl hu).trans_le (div_le_div_of_nonneg_right hl hdl.le)

/-- The quotient core computes enough significand bits before rounding. This
also covers a zero truncated quotient in the subnormal range. -/
theorem divCore_ready (format : Format) (n d : Nat) (en ed : Int) (hn : 0 < n) (hd : 0 < d) :
    let core := divCore format n en d ed
    core.2.1 ≤ format.targetExponent (totalExponent core.1 core.2.1) := by
  let core := divCore format n en d ed
  change core.2.1 ≤ format.targetExponent (totalExponent core.1 core.2.1)
  have he : core.2.1 ≤ format.targetExponent (totalExponent n en - totalExponent d ed) :=
    min_le_right _ _
  by_cases hmin : core.2.1 ≤ format.minExponent
  · exact hmin.trans (le_max_right _ _)
  · have ht : core.2.1 ≤ totalExponent n en - totalExponent d ed - format.mantissaBits := by
      dsimp [Format.targetExponent] at he
      omega
    have hpow : (2 : ℝ) ^ ((format.mantissaBits - 1 : Nat) : Int) ≤
        (2 : ℝ) ^ (totalExponent n en - totalExponent d ed - 1 - core.2.1) := by
      apply zpow_le_zpow_right₀ (by norm_num)
      have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
      omega
    have hquot := div_lt_div_of_pos_right (quotient_gt_lower n d en ed hn hd)
      (zpow_pos (by norm_num : (0 : ℝ) < 2) core.2.1)
    rw [← zpow_sub₀ (by norm_num)] at hquot
    have hs := (Conformance.divCore_accuracySound (K := ℝ) format n d en ed hd).bounds.2
    have hm : 2 ^ (format.mantissaBits - 1) ≤ core.1 := by
      have hr : (2 : ℝ) ^ (format.mantissaBits - 1) < (core.1 : ℝ) + 1 := by
        rw [← zpow_natCast]
        exact (hpow.trans_lt hquot).trans hs
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

theorem divCore_relative_error (format : Format) (sign : Sign) (n d : Nat) (en ed : Int)
    (hn : 0 < n) (hd : 0 < d) :
    let core := divCore format n en d ed
    let exact := (n : ℝ) * (2 : ℝ) ^ en / ((d : ℝ) * (2 : ℝ) ^ ed)
    ∃ v : ℝ, Magnitude (roundWithAccuracy format .nearestTiesToEven sign core.1 core.2.1 core.2.2) v ∧
      |v - exact| ≤ unitRoundoff format * exact + halfMinSubnormal format := by
  let core := divCore format n en d ed
  have h := roundWithAccuracy_relative_error format sign core.1 core.2.1 core.2.2 _
    (Conformance.divCore_accuracySound (K := ℝ) format n d en ed hd)
    (divCore_ready format n d en ed hn hd)
  simpa only [core, div_mul_cancel₀ _ (zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))] using h

theorem divCore_packed_error (format : Format) (sign : Sign) (n d : Nat) (en ed : Int)
    (hn : 0 < n) (hd : 0 < d)
    (safe : let core := divCore format n en d ed
      NoOverflow format (roundWithAccuracy format .nearestTiesToEven sign core.1 core.2.1 core.2.2)) :
    let core := divCore format n en d ed
    let exact := (n : ℝ) * (2 : ℝ) ^ en / ((d : ℝ) * (2 : ℝ) ^ ed)
    ∃ q : ℚ, exactValue? (coreSpec format)
      (packNormalized format .nearestTiesToEven
        (roundWithAccuracy format .nearestTiesToEven sign core.1 core.2.1 core.2.2)).toNat = some q ∧
      |(q : ℝ) - signedReal sign exact| ≤ unitRoundoff format * exact + halfMinSubnormal format := by
  let core := divCore format n en d ed
  obtain ⟨v, hv, he⟩ := divCore_relative_error format sign n d en ed hn hd
  obtain ⟨q, hq, hreal⟩ := unpackedRat_of_magnitude
    (roundWithAccuracy_sign format _ sign core.1 core.2.1 core.2.2) hv
  refine ⟨q, ?_, ?_⟩
  · rw [packNormalized_nearestEven]
    exact (pack_value format _
      (roundWithAccuracy_canonical_of_ready format _ sign core.1 core.2.1 core.2.2
        (divCore_ready format n d en ed hn hd)) safe).trans hq
  · rw [hreal, signedReal_sub_abs]
    exact he

/-- The unbounded rounded result used by `divRounded`, before interchange packing. -/
def divUnpacked (format : Format) (x y : UnpackedFloat) : UnpackedFloat :=
  match x, y with
  | .finite left lm le _, .finite right rm re _ =>
    let core := divCore format lm le rm re
    roundWithAccuracy format .nearestTiesToEven (left / right) core.1 core.2.1 core.2.2
  | _, _ => UnpackedFloat.div format x y

theorem divRounded_eq_pack (format : Format) (x y : UnpackedFloat) :
    divRounded format .nearestTiesToEven x y =
      packNormalized format .nearestTiesToEven (divUnpacked format x y) := rfl

theorem divUnpacked_approx (format : Format) (x y : UnpackedFloat) (a b : ℚ)
    (hx : unpackedRat? x = some a) (hy : unpackedRat? y = some b) (hb : b ≠ 0) :
    RoundedApprox format (divUnpacked format x y) (a / b) := by
  cases y with
  | notANumber | infinity => simp [unpackedRat?] at hy
  | zero => simp [unpackedRat?] at hy; exact (hb hy.symm).elim
  | finite sy d ed hd =>
    cases x with
    | notANumber | infinity => simp [unpackedRat?] at hx
    | zero sx =>
      have ha : a = 0 := by simpa [unpackedRat?] using hx.symm
      subst a
      refine ⟨trivial, 0, rfl, ?_⟩
      simp only [zero_div, Rat.cast_zero, sub_self, abs_zero, mul_zero, zero_add]
      exact div_nonneg (le_of_lt (zpow_pos (by norm_num) _)) (by norm_num)
    | finite sx n en hn =>
      let core := divCore format n en d ed
      let exact := (n : ℝ) * (2 : ℝ) ^ en / ((d : ℝ) * (2 : ℝ) ^ ed)
      have positive : 0 < exact := div_pos
        (mul_pos (by exact_mod_cast hn) (zpow_pos (by norm_num) _))
        (mul_pos (by exact_mod_cast hd) (zpow_pos (by norm_num) _))
      have hsign : ((a / b : ℚ) : ℝ) = signedReal (sx / sy) exact := by
        cases sx <;> cases sy <;> simp only [unpackedRat?, signedRat] at hx hy
        all_goals simp only [Option.some.injEq] at hx hy
        all_goals subst a; subst b
        all_goals simp [signedReal, exact, sign_div_nn, sign_div_np, sign_div_pn, sign_div_pp,
          neg_div, div_neg]
      have habs : |((a / b : ℚ) : ℝ)| = exact := by
        rw [hsign]
        cases sx <;> cases sy <;>
          simpa only [sign_div_nn, sign_div_np, sign_div_pn, sign_div_pp, signedReal, abs_neg] using
            abs_of_pos positive
      obtain ⟨v, hv, he⟩ := divCore_relative_error format (sx / sy) n d en ed hn hd
      obtain ⟨r, hr, hreal⟩ := unpackedRat_of_magnitude
        (roundWithAccuracy_sign format _ (sx / sy) core.1 core.2.1 core.2.2) hv
      refine ⟨roundWithAccuracy_canonical_of_ready format _ (sx / sy) core.1 core.2.1 core.2.2
        (divCore_ready format n d en ed hn hd), r, hr, ?_⟩
      rw [hreal, habs, hsign, signedReal_sub_abs]
      exact he

end Silmaril.Numeric.Ieee754.Rounding
