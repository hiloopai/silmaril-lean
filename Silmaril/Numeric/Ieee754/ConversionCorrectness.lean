module

public import Silmaril.Numeric.Ieee754.PackingCorrectness

/-!
# Exact widening conversions

If the destination's selected exponent is no greater than the exact input
exponent, normalization only aligns the significand to the left. These proofs
establish that such conversions lose no numerical information, in every rounding
direction. The binary32-to-binary64 corollary covers every raw source encoding;
its rational statement identifies signed zeros and assigns no rational value
to infinity or NaN.

IEEE 754-2019 §5.4.2 specifies conversion between supported formats:
<https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Conformance

open Float.Model Float.Model.UnpackedFloat

/-- An exact significand that fits at its current exponent needs no rounding. -/
theorem roundWithAccuracy_exact_of_fits (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (hprec : mantissa < 2 ^ format.mantissaBits) (he : format.minExponent ≤ exponent) :
    Rounding.roundWithAccuracy format mode sign mantissa exponent .exact =
      .finite sign mantissa exponent hm := by
  have hs := shiftToTargetExponent_noCarry format mantissa exponent hprec he
  simp [Rounding.roundWithAccuracy, hs, Rounding.roundMantissa,
    ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.accuracy, Nat.ne_of_gt hm]

/-- When left alignment suffices, destination normalization is exact and its
exponent is precisely the selected target exponent. -/
theorem roundUnpacked_finite_of_target_le (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (he : format.targetExponent (totalExponent mantissa exponent) ≤ exponent) :
    let target := format.targetExponent (totalExponent mantissa exponent)
    Rounding.roundUnpacked format mode (.finite sign mantissa exponent hm) =
      .finite sign (mantissa <<< (exponent - target).toNat) target
        (Nat.shiftLeft_pos_iff.mpr hm) := by
  let target := format.targetExponent (totalExponent mantissa exponent)
  let aligned := mantissa <<< (exponent - target).toNat
  have htarget := decreaseExponent_exponent_of_le mantissa he
  have htotal := decreaseExponent_totalExponent mantissa exponent target (Nat.ne_of_gt hm)
  have haligned : ExponentNormalized format
      (.finite sign aligned target (Nat.shiftLeft_pos_iff.mpr hm)) := by
    change format.targetExponent (totalExponent aligned target) = target
    have htot : totalExponent aligned target = totalExponent mantissa exponent := by
      rw [htarget] at htotal
      exact htotal
    rw [htot]
  have bounds := haligned.finite_bounds format sign aligned target (Nat.shiftLeft_pos_iff.mpr hm)
  change Rounding.roundWithAccuracy format mode sign aligned
      (decreaseExponent mantissa exponent target).2 .exact = _
  rw [htarget]
  exact roundWithAccuracy_exact_of_fits format mode sign aligned target
    (Nat.shiftLeft_pos_iff.mpr hm) bounds.2.1 bounds.1

/-- Exactness of a conversion requiring no discarded significand bits. -/
theorem value?_roundUnpacked_of_target_le (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (he : format.targetExponent (totalExponent mantissa exponent) ≤ exponent) :
    value? (Rounding.roundUnpacked format mode (.finite sign mantissa exponent hm)) =
      value? (.finite sign mantissa exponent hm) := by
  rw [roundUnpacked_finite_of_target_le format mode sign mantissa exponent hm he]
  simp only [value?]
  congr 1
  exact decreaseExponent_value_of_le sign mantissa he

/-- Every finite binary32 decoder exponent is at most the largest normal
significand exponent, independently of the source payload bits. -/
theorem unpack32_finite_exponent_le (bits : BitVec Format.binary32.numBits) :
    match UnpackedFloat.unpack .binary32 bits with
    | .finite _ _ exponent _ => exponent ≤ 104
    | _ => True := by
  have he := (unpackExponent (spec := Format.binary32) bits).isLt
  have hpow : 2 ^ Format.binary32.exponentBits = 256 := by decide
  rw [hpow] at he
  unfold UnpackedFloat.unpack
  dsimp only
  by_cases hmax : unpackExponent (spec := Format.binary32) bits = -1#_
  · by_cases hmzero : unpackMantissa (spec := Format.binary32) bits = 0#_
    all_goals simp [hmax, hmzero]
  ·
    have hnmax : (unpackExponent (spec := Format.binary32) bits).toNat ≠ 255 := by
      intro h
      apply hmax
      apply BitVec.eq_of_toNat_eq
      simpa using h
    by_cases hezero : unpackExponent (spec := Format.binary32) bits = 0#_
    · by_cases hmzero : unpackMantissa (spec := Format.binary32) bits = 0#_
      all_goals simp [hezero, hmzero, Format.exponentBias, Format.binary32]
    · simp only [hmax, hezero, ↓reduceIte]
      norm_num [Format.exponentBias, Format.binary32]
      omega

/-- Binary32-normalized finite inputs require no right shift in binary64. -/
theorem widening32_target_le (sign : Sign) (mantissa : Nat) (exponent : Int)
    (hm : 0 < mantissa)
    (normalized : ExponentNormalized .binary32 (.finite sign mantissa exponent hm)) :
    Format.binary64.targetExponent (totalExponent mantissa exponent) ≤ exponent := by
  have hb := normalized.finite_bounds .binary32 sign mantissa exponent hm
  have hlog := (Nat.log2_lt (Nat.ne_of_gt hm)).mpr hb.2.1
  norm_num [Format.minExponent, Format.mantissaBits, Format.binary32] at hb hlog
  norm_num [Format.targetExponent, Format.minExponent, Format.mantissaBits,
    Format.binary64, totalExponent]
  omega

/-- Widening any binary32-normalized value into binary64 preserves its rational
meaning in every rounding direction, including all exceptional input classes. -/
theorem value?_widen32 (mode : RoundingMode) (value : UnpackedFloat)
    (upper : match value with | .finite _ _ exponent _ => exponent ≤ 104 | _ => True)
    (normalized : ExponentNormalized .binary32 value) :
    value? (UnpackedFloat.unpack .binary64 (Rounding.packRounded .binary64 mode value)) =
      value? value := by
  cases value with
  | notANumber => simp [Rounding.packRounded_notANumber]
  | infinity sign => simp [Rounding.packRounded_infinity]
  | zero sign => simp [Rounding.packRounded_zero]
  | finite sign mantissa exponent hm =>
    have ht := widening32_target_le sign mantissa exponent hm normalized
    have inRange : NoExponentOverflow .binary64
        (Rounding.roundUnpacked .binary64 mode (.finite sign mantissa exponent hm)) := by
      rw [roundUnpacked_finite_of_target_le .binary64 mode sign mantissa exponent hm ht]
      change (Format.binary64.targetExponent (totalExponent mantissa exponent) + 1023 + 52).toNat < 2047
      omega
    rw [unpack_packRounded .binary64 mode _ inRange]
    exact value?_roundUnpacked_of_target_le .binary64 mode sign mantissa exponent hm ht

end Silmaril.Numeric.Ieee754.Conformance

namespace Silmaril.Numeric.Ieee754.F32

/-- Binary32-to-binary64 conversion preserves the independent rational value
for every source encoding. NaNs and infinities have value `none` on both sides. -/
@[simp] theorem toRat?_toF64 (x : F32) : x.toF64.toRat? = x.toRat? := by
  rw [← Conformance.value?_model_unpack64]
  change Conformance.value? (Float.Model.UnpackedFloat.unpack .binary64
    (Float.Model.UnpackedFloat.pack .binary64
      (Float.Model.UnpackedFloat.unpack .binary64
        (Rounding.packRounded .binary64 .nearestTiesToEven x.model.unpack)))) = _
  rw [Conformance.value?_unpack_pack_unpack]
  have normalized : Conformance.ExponentNormalized .binary32 x.model.unpack :=
    Conformance.unpack_exponent_normalized _ _
  have upper : match x.model.unpack with
      | .finite _ _ exponent _ => exponent ≤ 104
      | _ => True := Conformance.unpack32_finite_exponent_le _
  rw [Conformance.value?_widen32 _ _ upper normalized, Conformance.value?_model_unpack32]

end Silmaril.Numeric.Ieee754.F32
