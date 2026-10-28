module

public import Silmaril.Numeric.Ieee754.EncodingCorrectness
public import Silmaril.Numeric.Ieee754.Normalization

/-!
# Packing normalized finite values

These proofs connect the core model's packing operation to its decoder.
An in-range finite input with a canonical exponent is recovered exactly,
including its sign and significand, by unpacking the packed encoding. Directed
packing uses the same encoding in range and selects infinity or the largest
finite magnitude on exponent overflow.

This is an encoding theorem. Relating a mathematical source to its rounded
finite input, and deriving the overflow condition from that source, are
separate obligations.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Conformance

open Float.Model Float.Model.UnpackedFloat

/-- A finite normalized exponent corresponds to a positive biased exponent.
Subnormals have this intermediate value equal to one, before packing chooses
the zero exponent field. -/
theorem normalized_biasedExponent_pos (format : Format) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (normalized : ExponentNormalized format (.finite sign mantissa exponent hm)) :
    0 < exponent + (format.exponentBias : Int) + format.mantissaBitsWithoutImplicit := by
  have he := (normalized.finite_bounds format sign mantissa exponent hm).1
  rw [minExponent_eq_bias] at he
  omega

/-- Round-trip of a normalized finite value whose exponent is below the
infinity/NaN exponent field. This theorem preserves the entire unpacked datum. -/
theorem unpack_pack_finite (format : Format) (sign : Sign) (mantissa : Nat) (exponent : Int)
    (hm : 0 < mantissa)
    (normalized : ExponentNormalized format (.finite sign mantissa exponent hm))
    (inRange : (exponent + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat <
      2 ^ format.exponentBits - 1) :
    UnpackedFloat.unpack format (UnpackedFloat.pack format (.finite sign mantissa exponent hm)) =
      .finite sign mantissa exponent hm := by
  let biased := (exponent + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat
  have hbiased := normalized_biasedExponent_pos format sign mantissa exponent hm normalized
  have hcast : (biased : Int) = exponent + format.exponentBias + format.mantissaBitsWithoutImplicit :=
    Int.toNat_of_nonneg (by omega)
  have hpositive : 0 < biased := by omega
  have hbound : biased < 2 ^ format.exponentBits := by dsimp [biased]; omega
  have hmax : (BitVec.ofNat format.exponentBits biased) ≠ -1#_ := by
    intro h
    have h := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound,
      BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at h
    change biased < _ at inRange
    omega
  have hzero : (BitVec.ofNat format.exponentBits biased) ≠ 0#_ := by
    intro h
    have h := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound, Nat.zero_mod] at h
    omega
  have hnoOverflow : ¬2 ^ format.exponentBits ≤ biased + 1 := by
    change biased < _ at inRange
    omega
  have hprecision := normalized.finite_bounds format sign mantissa exponent hm
  change UnpackedFloat.unpack format
    (if 2 ^ format.exponentBits ≤ biased + 1 then packedInfinity format sign
     else if mantissa.log2 + 1 = format.mantissaBits then
       packComponents format sign (BitVec.ofNat _ biased) (BitVec.ofNat _ mantissa)
     else packComponents format sign 0#_ (BitVec.ofNat _ mantissa)) = _
  rw [ite_eq_right hnoOverflow]
  by_cases hnormal : mantissa.log2 + 1 = format.mantissaBits
  · rw [ite_eq_left hnormal]
    have hl : 2 ^ format.mantissaBitsWithoutImplicit ≤ mantissa := by
      apply (Nat.le_log2 (Nat.ne_of_gt hm)).mp
      simp only [Format.mantissaBits] at hnormal
      omega
    have hu : mantissa < 2 ^ format.mantissaBitsWithoutImplicit * 2 := by
      have hu := hprecision.2.1
      simpa [Format.mantissaBits, Nat.add_comm, Nat.pow_succ] using hu
    have hrem : mantissa % 2 ^ format.mantissaBitsWithoutImplicit =
        mantissa - 2 ^ format.mantissaBitsWithoutImplicit := by
      rw [Nat.mod_eq_sub_mod hl, Nat.mod_eq_of_lt (by omega)]
    have hmdecode : (1#1 ++ BitVec.ofNat format.mantissaBitsWithoutImplicit mantissa).toNat = mantissa := by
      rw [normalMantissa_toNat, BitVec.toNat_ofNat, hrem]
      omega
    simp only [UnpackedFloat.unpack, unpackMantissa_packComponents,
      unpackExponent_packComponents, unpackSign_packComponents, sign_ofBitVec_toBitVec,
      hmax, hzero, ↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound, hmdecode]
    congr 1
    omega
  · rw [ite_eq_right hnormal]
    have hsmall : mantissa < 2 ^ format.mantissaBitsWithoutImplicit := by
      apply (Nat.log2_lt (Nat.ne_of_gt hm)).mp
      have hlog := (Nat.log2_lt (Nat.ne_of_gt hm)).mpr hprecision.2.1
      simp only [Format.mantissaBits] at hnormal hlog
      omega
    have he : exponent = format.minExponent := by
      rcases hprecision.2.2 with he | hl
      · exact he
      · have : format.mantissaBits - 1 = format.mantissaBitsWithoutImplicit := by
          simp [Format.mantissaBits]
        rw [this] at hl
        omega
    have hnzero : (BitVec.ofNat format.mantissaBitsWithoutImplicit mantissa) ≠ 0#_ := by
      intro h
      have h := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, Nat.zero_mod] at h
      omega
    have hempty : (0#format.exponentBits) ≠ -1#_ := by
      intro h
      have h := congrArg BitVec.toNat h
      simp only [BitVec.toNat_zero, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at h
      have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) format.he
      norm_num at hp
      omega
    simp only [UnpackedFloat.unpack, unpackMantissa_packComponents,
      unpackExponent_packComponents, unpackSign_packComponents, sign_ofBitVec_toBitVec,
      hempty, ↓reduceIte, hnzero, ↓reduceDIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
    congr 1
    rw [he, minExponent_eq_bias]
    simp
    omega

/-- Directed packing agrees with ordinary encoding in the finite exponent range. -/
theorem packNormalized_eq_pack_of_inRange (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (inRange : (exponent + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat <
      2 ^ format.exponentBits - 1) :
    Rounding.packNormalized format mode (.finite sign mantissa exponent hm) =
      UnpackedFloat.pack format (.finite sign mantissa exponent hm) := by
  unfold Rounding.packNormalized
  have h : ¬2 ^ format.exponentBits ≤
      (exponent + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat + 1 := by omega
  simp [h]

/-- In-range directed packing preserves the full normalized finite datum. -/
theorem unpack_packNormalized_finite (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (normalized : ExponentNormalized format (.finite sign mantissa exponent hm))
    (inRange : (exponent + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat <
      2 ^ format.exponentBits - 1) :
    UnpackedFloat.unpack format (Rounding.packNormalized format mode (.finite sign mantissa exponent hm)) =
      .finite sign mantissa exponent hm := by
  rw [packNormalized_eq_pack_of_inRange format mode sign mantissa exponent hm inRange]
  exact unpack_pack_finite format sign mantissa exponent hm normalized inRange

/-- In particular, in-range packing preserves the independent rational value. -/
theorem value?_unpack_packNormalized_finite (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (normalized : ExponentNormalized format (.finite sign mantissa exponent hm))
    (inRange : (exponent + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat <
      2 ^ format.exponentBits - 1) :
    value? (UnpackedFloat.unpack format
      (Rounding.packNormalized format mode (.finite sign mantissa exponent hm))) =
      some (dyadic (sign.apply mantissa) exponent) := by
  rw [unpack_packNormalized_finite format mode sign mantissa exponent hm normalized inRange]
  rfl

/-- Exponent overflow selects the sign- and mode-dependent default result. -/
theorem packNormalized_overflow (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (overflow : 2 ^ format.exponentBits ≤
      (exponent + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat + 1) :
    Rounding.packNormalized format mode (.finite sign mantissa exponent hm) =
      if Rounding.overflowToInfinity mode sign then packedInfinity format sign
      else Rounding.packedMaxFinite format sign := by
  unfold Rounding.packNormalized
  cases hd : Rounding.overflowToInfinity mode sign <;>
    simp [hd, overflow, UnpackedFloat.pack]

@[simp] theorem unpack_packedInfinity (format : Format) (sign : Sign) :
    UnpackedFloat.unpack format (packedInfinity format sign) = .infinity sign := by
  simp [UnpackedFloat.unpack, packedInfinity]

@[simp] theorem unpack_packedZero (format : Format) (sign : Sign) :
    UnpackedFloat.unpack format (packedZero format sign) = .zero sign := by
  have hzero : (0#format.exponentBits) ≠ -1#_ := by
    intro h
    have h := congrArg BitVec.toNat h
    simp only [BitVec.toNat_zero, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at h
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) format.he
    norm_num at hp
    omega
  simp [UnpackedFloat.unpack, packedZero, hzero]

@[simp] theorem unpack_packedNaN (format : Format) :
    UnpackedFloat.unpack format (packedNaN format) = .notANumber := by
  have hquiet : (1#format.mantissaBitsWithoutImplicit <<< (format.mantissaBitsWithoutImplicit - 1)) ≠ 0#_ := by
    have hp := format.hm
    have hpow : 2 ^ (format.mantissaBitsWithoutImplicit - 1) < 2 ^ format.mantissaBitsWithoutImplicit :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    have hpos : 0 < 2 ^ (format.mantissaBitsWithoutImplicit - 1) := Nat.pow_pos (by decide)
    intro h
    have h := congrArg BitVec.toNat h
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_one hp, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.mod_eq_of_lt hpow, BitVec.toNat_zero] at h
    omega
  simp [UnpackedFloat.unpack, packedNaN, hquiet]

/-- Largest finite value, expressed directly as a signed integer significand
and exponent, independently of the encoder's bit construction. -/
def largestFinite (format : Format) (sign : Sign) : UnpackedFloat :=
  .finite sign (2 ^ format.mantissaBits - 1)
    ((2 ^ format.exponentBits - 2 : Nat) - (format.exponentBias : Int) -
      format.mantissaBitsWithoutImplicit)
    (by
      have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
      have hp : 1 < 2 ^ format.mantissaBits := Nat.one_lt_two_pow (by omega)
      omega)

/-- The saturation encoding denotes the largest finite value, including sign. -/
@[simp] theorem unpack_packedMaxFinite (format : Format) (sign : Sign) :
    UnpackedFloat.unpack format (Rounding.packedMaxFinite format sign) = largestFinite format sign := by
  have hrange : 2 < 2 ^ format.exponentBits := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) format.he
    norm_num at hp
    omega
  have hbound : 2 ^ format.exponentBits - 2 < 2 ^ format.exponentBits := by omega
  have hmax : (BitVec.ofNat format.exponentBits (2 ^ format.exponentBits - 2)) ≠ -1#_ := by
    intro h
    have h := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound,
      BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at h
    omega
  have hzero : (BitVec.ofNat format.exponentBits (2 ^ format.exponentBits - 2)) ≠ 0#_ := by
    intro h
    have h := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound, Nat.zero_mod] at h
    omega
  have hm : (1#1 ++ (-1#format.mantissaBitsWithoutImplicit)).toNat = 2 ^ format.mantissaBits - 1 := by
    rw [normalMantissa_toNat]
    simp only [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
    have hp : 0 < 2 ^ format.mantissaBitsWithoutImplicit := Nat.pow_pos (by decide)
    simp only [Format.mantissaBits, Nat.pow_add, Nat.pow_one]
    omega
  simp only [Rounding.packedMaxFinite, UnpackedFloat.unpack, unpackMantissa_packComponents,
    unpackExponent_packComponents, unpackSign_packComponents, sign_ofBitVec_toBitVec,
    hmax, hzero, ↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound, hm, largestFinite]
  congr 1
  omega

/-- Overflow packing realizes IEEE's sign-dependent infinity/finite choice
as an unpacked numerical result. The exponent-overflow premise is explicit. -/
theorem unpack_packNormalized_overflow (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (overflow : 2 ^ format.exponentBits ≤
      (exponent + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat + 1) :
    UnpackedFloat.unpack format (Rounding.packNormalized format mode (.finite sign mantissa exponent hm)) =
      if Rounding.overflowToInfinity mode sign then .infinity sign else largestFinite format sign := by
  rw [packNormalized_overflow format mode sign mantissa exponent hm overflow]
  cases Rounding.overflowToInfinity mode sign <;> simp

/-- The finite exponent can be encoded without invoking overflow handling.
This condition does not exclude infinities or NaNs supplied as input data. -/
def NoExponentOverflow (format : Format) : UnpackedFloat → Prop
  | .finite _ _ exponent _ =>
    (exponent + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat <
      2 ^ format.exponentBits - 1
  | _ => True

instance (format : Format) (value : UnpackedFloat) : Decidable (NoExponentOverflow format value) := by
  cases value <;> dsimp [NoExponentOverflow] <;> infer_instance

/-- Normalized packing followed by unpacking is identity when finite exponents
are in range. Signed zeros and non-finite classes are recovered as well. -/
theorem unpack_packNormalized (format : Format) (mode : RoundingMode) (value : UnpackedFloat)
    (normalized : ExponentNormalized format value) (inRange : NoExponentOverflow format value) :
    UnpackedFloat.unpack format (Rounding.packNormalized format mode value) = value := by
  cases value with
  | notANumber => simp [Rounding.packNormalized, UnpackedFloat.pack]
  | infinity sign => simp [Rounding.packNormalized, UnpackedFloat.pack]
  | zero sign => simp [Rounding.packNormalized, UnpackedFloat.pack]
  | finite sign mantissa exponent hm =>
    exact unpack_packNormalized_finite format mode sign mantissa exponent hm normalized inRange

/-- Encoding does not change a rounded result whose finite exponent is in
range. The normalization premise is discharged by `roundUnpacked_normalized`. -/
theorem unpack_packRounded (format : Format) (mode : RoundingMode) (value : UnpackedFloat)
    (inRange : NoExponentOverflow format (Rounding.roundUnpacked format mode value)) :
    UnpackedFloat.unpack format (Rounding.packRounded format mode value) =
      Rounding.roundUnpacked format mode value := by
  exact unpack_packNormalized format mode _ (roundUnpacked_normalized format mode value) inRange

end Silmaril.Numeric.Ieee754.Conformance
