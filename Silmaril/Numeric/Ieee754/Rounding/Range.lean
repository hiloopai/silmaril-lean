module

public import Silmaril.Numeric.Ieee754.Rounding.PackedError

/-! # Sufficient magnitude bounds for finite nearest-even results

The bound includes the rounder's possible carry and gradual-underflow error.
The threshold is the magnitude at the reserved exponent, not the largest
finite input. No-overflow is derived from the actual canonical rounded value.
-/

@[expose] public section
namespace Silmaril.Numeric.Ieee754.Rounding
open Float.Model Float.Model.UnpackedFloat LowPrecision

def overflowExponent (format : Format) : Int :=
  ((2 ^ format.exponentBits - 1 : Nat) : Int) - format.exponentBias

noncomputable def overflowThreshold (format : Format) : ℝ := (2 : ℝ) ^ overflowExponent format

theorem noOverflow_of_magnitude_lt (format : Format) (value : UnpackedFloat) (v : ℝ)
    (hc : CanonicalValue format value) (hv : Magnitude value v)
    (hbound : v < overflowThreshold format) : NoOverflow format value := by
  cases value with
  | notANumber | infinity => contradiction
  | zero => trivial
  | finite sign m e hm =>
    change Canonical format m e at hc
    change v = (m : ℝ) * (2 : ℝ) ^ e at hv
    subst v
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) format.he
    have hreserved : 1 < 2 ^ format.exponentBits - 1 := by norm_num at hp; omega
    change (e + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat <
      2 ^ format.exponentBits - 1
    by_cases hsub : m < 2 ^ format.mantissaBitsWithoutImplicit
    · have he := hc.subnormal_exponent hsub
      rw [minExponent_eq] at he
      have hfield : e + format.exponentBias + format.mantissaBitsWithoutImplicit = 1 := by omega
      simpa only [hfield, Int.toNat_one] using hreserved
    · have hmantissa : (2 : ℝ) ^ (format.mantissaBitsWithoutImplicit : Int) ≤ (m : ℝ) := by
        rw [zpow_natCast]
        exact_mod_cast (Nat.le_of_not_gt hsub)
      have he : e + (format.mantissaBitsWithoutImplicit : Int) < overflowExponent format := by
        apply (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
        calc
          (2 : ℝ) ^ (e + (format.mantissaBitsWithoutImplicit : Int)) =
              (2 : ℝ) ^ (format.mantissaBitsWithoutImplicit : Int) * (2 : ℝ) ^ e := by
            rw [zpow_add₀ (by norm_num)]
            ring
          _ ≤ (m : ℝ) * (2 : ℝ) ^ e :=
            mul_le_mul_of_nonneg_right hmantissa (le_of_lt (zpow_pos (by norm_num) _))
          _ < _ := hbound
      dsimp [overflowExponent] at he
      omega

/-- A bound on the exact input suffices; no hypothesis mentions the rounded
result. The strict inequality includes the worst-case rounding carry. -/
theorem roundUnpacked_noOverflow_of_bound (format : Format) (value : UnpackedFloat) (q : ℚ)
    (hq : unpackedRat? value = some q)
    (hbound : (1 + unitRoundoff format) * |(q : ℝ)| + halfMinSubnormal format <
      overflowThreshold format) :
    NoOverflow format (roundUnpacked format .nearestTiesToEven value) := by
  cases value with
  | notANumber | infinity => simp [unpackedRat?] at hq
  | zero => trivial
  | finite sign m e hm =>
    obtain ⟨v, hv, he⟩ := roundUnpacked_relative_error format sign m e hm
    have hmag := magnitude_of_unpackedRat hq
    change |(q : ℝ)| = (m : ℝ) * (2 : ℝ) ^ e at hmag
    have hupper : v ≤ (1 + unitRoundoff format) * |(q : ℝ)| + halfMinSubnormal format := by
      rw [hmag]
      have hle := le_abs_self (v - (m : ℝ) * (2 : ℝ) ^ e)
      nlinarith
    exact noOverflow_of_magnitude_lt format _ v
      (roundUnpacked_canonical format _ sign m e hm) hv (hupper.trans_lt hbound)

end Silmaril.Numeric.Ieee754.Rounding
