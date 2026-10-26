module

public import Silmaril.Numeric.Ieee754.Rounding.Canonical

/-! # Error bounds after finite-format packing -/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Rounding

open Float.Model Float.Model.UnpackedFloat LowPrecision

/-- The rounded exponent fits below the reserved infinity/NaN exponent. -/
def NoOverflow (format : Format) : UnpackedFloat → Prop
  | .zero _ => True
  | .finite _ _ e _ =>
    (e + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat <
      2 ^ format.exponentBits - 1
  | _ => False

theorem pack_zero_value (format : Format) (sign : Sign) :
    exactValue? (coreSpec format) (packedZero format sign).toNat = some 0 := by
  have he : (0 : BitVec format.exponentBits).toNat ≠ 2 ^ format.exponentBits - 1 := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) format.he
    change 0 ≠ 2 ^ format.exponentBits - 1
    norm_num at hp
    omega
  unfold packedZero
  rw [decode_packComponents format sign (0 : BitVec format.exponentBits) (0 : BitVec format.mantissaBitsWithoutImplicit) he]
  cases sign <;> simp [signedRat]

theorem pack_value (format : Format) (value : UnpackedFloat)
    (hc : CanonicalValue format value) (ho : NoOverflow format value) :
    exactValue? (coreSpec format) (value.pack format).toNat = unpackedRat? value := by
  cases value with
  | notANumber | infinity => contradiction
  | zero sign => exact pack_zero_value format sign
  | finite sign m e hm => exact pack_finite_value format sign m e hm hc ho

theorem packNormalized_nearestEven (format : Format) (value : UnpackedFloat) :
    packNormalized format .nearestTiesToEven value = value.pack format := by
  cases value <;> simp [packNormalized, overflowToInfinity]

/-- Packing the actual rounded result preserves its value when it does not overflow. -/
theorem packRounded_finite_value (format : Format) (sign : Sign)
    (m : Nat) (e : Int) (hm : 0 < m)
    (ho : NoOverflow format (roundUnpacked format .nearestTiesToEven (.finite sign m e hm))) :
    exactValue? (coreSpec format)
      (packRounded format .nearestTiesToEven (.finite sign m e hm)).toNat =
      unpackedRat? (roundUnpacked format .nearestTiesToEven (.finite sign m e hm)) := by
  rw [packRounded, packNormalized_nearestEven]
  exact pack_value format _ (roundUnpacked_canonical format _ sign m e hm) ho

/-- The finite rounder retains the input sign, including a rounded zero. -/
def HasSign (sign : Sign) : UnpackedFloat → Prop
  | .zero s | .finite s _ _ _ => s = sign
  | _ => False

theorem roundUnpacked_sign (format : Format) (mode : RoundingMode) (sign : Sign)
    (m : Nat) (e : Int) (hm : 0 < m) :
    HasSign sign (roundUnpacked format mode (.finite sign m e hm)) := by
  unfold roundUnpacked roundWithAccuracy
  dsimp only
  split <;> rfl

noncomputable def signedReal (sign : Sign) (v : ℝ) : ℝ :=
  match sign with
  | .positive => v
  | .negative => -v

theorem signedReal_sub_abs (sign : Sign) (a b : ℝ) :
    |signedReal sign a - signedReal sign b| = |a - b| := by
  cases sign with
  | positive => rfl
  | negative => simpa only [signedReal, neg_sub_neg] using abs_sub_comm b a

theorem unpackedRat_of_magnitude {value : UnpackedFloat} {sign : Sign} {v : ℝ}
    (hs : HasSign sign value) (hv : Magnitude value v) :
    ∃ q : ℚ, unpackedRat? value = some q ∧ (q : ℝ) = signedReal sign v := by
  cases value with
  | notANumber | infinity => contradiction
  | zero s =>
    change s = sign at hs
    subst s
    change v = 0 at hv
    subst v
    exact ⟨0, rfl, by cases sign <;> simp [signedReal]⟩
  | finite s m e hm =>
    change s = sign at hs
    subst s
    change v = (m : ℝ) * (2 : ℝ) ^ e at hv
    subst v
    refine ⟨signedRat (sign == .negative) ((m : ℚ) * (2 : ℚ) ^ e), rfl, ?_⟩
    cases sign <;> simp [signedRat, signedReal]

/-- A uniform signed error bound for actual packed nearest-even rounding.
The hypothesis is on the rounded exponent, so overflow is excluded explicitly;
subnormal outputs and rounding to signed zero are included. -/
theorem packRounded_relative_error (format : Format) (sign : Sign)
    (m : Nat) (e : Int) (hm : 0 < m)
    (ho : NoOverflow format (roundUnpacked format .nearestTiesToEven (.finite sign m e hm))) :
    ∃ q : ℚ, exactValue? (coreSpec format)
      (packRounded format .nearestTiesToEven (.finite sign m e hm)).toNat = some q ∧
      |(q : ℝ) - signedReal sign ((m : ℝ) * (2 : ℝ) ^ e)| ≤
        unitRoundoff format * ((m : ℝ) * (2 : ℝ) ^ e) + halfMinSubnormal format := by
  obtain ⟨v, hv, herr⟩ := roundUnpacked_relative_error format sign m e hm
  obtain ⟨q, hq, hreal⟩ := unpackedRat_of_magnitude (roundUnpacked_sign format _ sign m e hm) hv
  refine ⟨q, ?_, ?_⟩
  · rw [packRounded_finite_value format sign m e hm ho]
    exact hq
  · rw [hreal, signedReal_sub_abs]
    exact herr

/-- Precision-dependent rounding error stated entirely through exact rational decoding. -/
theorem packRounded_error (format : Format) (value : UnpackedFloat) (q : ℚ)
    (hq : unpackedRat? value = some q)
    (ho : NoOverflow format (roundUnpacked format .nearestTiesToEven value)) :
    ∃ r : ℚ, exactValue? (coreSpec format)
      (packRounded format .nearestTiesToEven value).toNat = some r ∧
      |(r : ℝ) - (q : ℝ)| ≤ unitRoundoff format * |(q : ℝ)| + halfMinSubnormal format := by
  cases value with
  | notANumber | infinity => simp [unpackedRat?] at hq
  | zero sign =>
    simp only [unpackedRat?, Option.some.injEq] at hq
    subst q
    refine ⟨0, pack_zero_value format sign, ?_⟩
    simp only [Rat.cast_zero, sub_self, abs_zero, mul_zero, zero_add]
    exact div_nonneg (le_of_lt (zpow_pos (by norm_num) _)) (by norm_num)
  | finite sign m e hm =>
    obtain ⟨r, hr, herr⟩ := packRounded_relative_error format sign m e hm ho
    have hmag := magnitude_of_unpackedRat hq
    change |(q : ℝ)| = (m : ℝ) * (2 : ℝ) ^ e at hmag
    have hreal : (q : ℝ) = signedReal sign ((m : ℝ) * (2 : ℝ) ^ e) := by
      cases sign <;> simp [unpackedRat?, signedRat] at hq
      all_goals subst q
      all_goals simp [signedReal]
    refine ⟨r, hr, ?_⟩
    rw [hmag, hreal]
    exact herr

end Silmaril.Numeric.Ieee754.Rounding
