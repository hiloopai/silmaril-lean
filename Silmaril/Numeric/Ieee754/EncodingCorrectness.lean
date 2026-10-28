module

public import Silmaril.Numeric.Ieee754.Exact
public import Mathlib.Data.BitVec
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Correctness of the binary interchange decoder

This module connects the core model's bitvector decoder to the independent
IEEE 754 field formula used by `F32.toRat?` and `F64.toRat?`. The statement
quantifies over every interchange encoding, including both zero signs,
subnormals, infinities, and all NaN payloads.

The finite-value formula follows IEEE 754-2019 §3.4. NaN canonicalization
does not change the rational interpretation, which is undefined for NaNs.
Reference: <https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Conformance

open Float.Model Float.Model.UnpackedFloat

theorem unpackMantissa_toNat (format : Format) (bits : BitVec format.numBits) :
    (unpackMantissa bits).toNat = (decode format.exponentBits
      format.mantissaBitsWithoutImplicit bits.toNat).trailingSignificand := by
  simp [unpackMantissa, decode, field]

theorem unpackExponent_toNat (format : Format) (bits : BitVec format.numBits) :
    (unpackExponent bits).toNat = (decode format.exponentBits
      format.mantissaBitsWithoutImplicit bits.toNat).exponent := by
  simp [unpackExponent, decode, field, Nat.shiftRight_eq_div_pow]

theorem unpackSign_toNat (format : Format) (bits : BitVec format.numBits) :
    (unpackSign bits).toNat = field bits.toNat
      (format.exponentBits + format.mantissaBitsWithoutImplicit) 1 := by
  simp [unpackSign, field, Nat.shiftRight_eq_div_pow, Nat.add_comm]

/-- Applying the decoded sign agrees with the signed rational field formula. -/
theorem dyadic_ofBitVec (sign : BitVec 1) (mantissa : Nat) (exponent : Int) :
    dyadic ((Sign.ofBitVec sign).apply mantissa) exponent =
      signed (sign.toNat == 1) ((mantissa : ℚ) * (2 : ℚ) ^ exponent) := by
  by_cases h : sign = 0#1
  · simp [h, Sign.ofBitVec, Sign.apply, dyadic, signed]
  · have hs : sign.toNat = 1 := by
      have hbound := sign.isLt
      have hn : sign.toNat ≠ 0 := by
        intro hz
        apply h
        exact BitVec.eq_of_toNat_eq hz
      simp only [Nat.pow_one] at hbound
      omega
    simp [Sign.ofBitVec, h, hs, Sign.apply, dyadic, signed]

private theorem exponent_eq_max_iff (format : Format) (exponent : BitVec format.exponentBits) :
    exponent.toNat = maxExponentField format.exponentBits ↔ exponent = -1#_ := by
  rw [← BitVec.toNat_inj, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
  rfl

/-- Restoring the implicit leading bit adds exactly one significand unit. -/
theorem normalMantissa_toNat (format : Format)
    (mantissa : BitVec format.mantissaBitsWithoutImplicit) :
    (1#1 ++ mantissa).toNat = 2 ^ format.mantissaBitsWithoutImplicit + mantissa.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt mantissa.isLt]
  simp [Nat.shiftLeft_eq]

private theorem fraction_scale (mantissa bits : Nat) (exponent : Int) :
    (mantissa : ℚ) * (2 : ℚ) ^ (exponent - bits) =
      (mantissa / (2 ^ bits : Nat) : ℚ) * (2 : ℚ) ^ exponent := by
  simp only [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast,
    Nat.cast_pow, Nat.cast_ofNat]
  ring

private theorem normal_scale (mantissa bits : Nat) (exponent : Int) :
    ((2 ^ bits + mantissa : Nat) : ℚ) * (2 : ℚ) ^ (exponent - bits) =
      (1 + mantissa / (2 ^ bits : Nat) : ℚ) * (2 : ℚ) ^ exponent := by
  rw [fraction_scale]
  simp [Nat.cast_add, add_div]

/-- Core bit extraction followed by unpacking agrees with IEEE's independent
field formula, for every format and every raw encoding. -/
theorem value?_unpack (format : Format) (bits : BitVec format.numBits) :
    value? (UnpackedFloat.unpack format bits) =
      finiteValue format.exponentBits format.mantissaBitsWithoutImplicit
        format.exponentBias (decode format.exponentBits format.mantissaBitsWithoutImplicit bits.toNat) := by
  have hm := unpackMantissa_toNat format bits
  have he := unpackExponent_toNat format bits
  have hs := unpackSign_toNat format bits
  unfold UnpackedFloat.unpack
  dsimp only
  unfold finiteValue
  rw [← hm, ← he]
  have hsign : (decode format.exponentBits format.mantissaBitsWithoutImplicit bits.toNat).sign =
      ((unpackSign bits).toNat == 1) := by
    rw [hs]
    rfl
  rw [hsign]
  by_cases hemax : unpackExponent (spec := format) bits = -1#_
  · have heNat := (exponent_eq_max_iff format _).mpr hemax
    rw [ite_eq_left hemax]
    simp only [heNat, beq_self_eq_true, ↓reduceIte]
    split <;> rfl
  · have heNat := (exponent_eq_max_iff format _).not.mpr hemax
    simp only [hemax, ↓reduceIte, beq_eq_false_iff_ne.mpr heNat, Bool.false_eq_true]
    by_cases hezero : unpackExponent (spec := format) bits = 0#_
    · have hz : (unpackExponent (spec := format) bits).toNat = 0 := by rw [hezero]; rfl
      simp only [hezero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.cast_zero,
        beq_self_eq_true, ↓reduceIte]
      by_cases hmzero : unpackMantissa (spec := format) bits = 0#_
      · simp [hmzero, value?, signed]
      · simp only [hmzero, ↓reduceDIte, value?, dyadic_ofBitVec]
        have hExp : 0 - (↑format.exponentBias + ↑format.mantissaBitsWithoutImplicit : Int) + 1 =
            1 - ↑format.exponentBias - ↑format.mantissaBitsWithoutImplicit := by omega
        rw [hExp, fraction_scale]
    · have hz : (unpackExponent (spec := format) bits).toNat ≠ 0 := by
        intro hz
        exact hezero (BitVec.eq_of_toNat_eq hz)
      simp only [hezero, ↓reduceIte, beq_eq_false_iff_ne.mpr hz, Bool.false_eq_true,
        value?, dyadic_ofBitVec, normalMantissa_toNat]
      have hExp : (↑(unpackExponent (spec := format) bits).toNat : Int) -
          (↑format.exponentBias + ↑format.mantissaBitsWithoutImplicit) =
          (↑(unpackExponent (spec := format) bits).toNat - ↑format.exponentBias) -
            ↑format.mantissaBitsWithoutImplicit := by omega
      rw [hExp, normal_scale]

@[simp] theorem sign_toBitVec_ofBitVec (sign : BitVec 1) :
    (Sign.ofBitVec sign).toBitVec = sign := by
  rcases sign.eq_zero_or_eq_one with rfl | rfl <;> rfl

@[simp] theorem sign_ofBitVec_toBitVec (sign : Sign) :
    Sign.ofBitVec sign.toBitVec = sign := by
  cases sign <;> rfl

@[simp] theorem unpackSign_packComponents (format : Format) (sign : Sign)
    (exponent : BitVec format.exponentBits) (mantissa : BitVec format.mantissaBitsWithoutImplicit) :
    unpackSign (packComponents format sign exponent mantissa) = sign.toBitVec := by
  unfold unpackSign packComponents
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  simp [BitVec.extractLsb'_append_eq_left]

/-- The three extracted fields reconstruct every original bit, including NaN payloads. -/
theorem packComponents_unpack (format : Format) (bits : BitVec format.numBits) :
    packComponents format (Sign.ofBitVec (unpackSign bits))
      (unpackExponent bits) (unpackMantissa bits) = bits := by
  unfold packComponents
  rw [sign_toBitVec_ofBitVec]
  unfold unpackSign unpackExponent unpackMantissa
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
  exact BitVec.extractLsb'_append_extractLsb'

private theorem normalMantissa_log2 (format : Format)
    (mantissa : BitVec format.mantissaBitsWithoutImplicit) :
    (1#1 ++ mantissa).toNat.log2 = format.mantissaBitsWithoutImplicit := by
  rw [normalMantissa_toNat]
  have hp : 0 < 2 ^ format.mantissaBitsWithoutImplicit := Nat.two_pow_pos _
  have hm := mantissa.isLt
  rw [Nat.log2_eq_iff (by omega), Nat.pow_succ]
  omega

/-- The minimum subnormal significand exponent in terms of the encoding bias. -/
theorem minExponent_eq_bias (format : Format) :
    format.minExponent = 1 - (format.exponentBias : Int) - format.mantissaBitsWithoutImplicit := by
  have hp : 0 < 2 ^ (format.exponentBits - 1) := Nat.pow_pos (by decide)
  unfold Format.minExponent Format.exponentBias Format.mantissaBits
  norm_cast
  simp only [Int.subNatNat_eq_coe]
  omega

/-- Every decoded finite encoding has the target exponent required by the
core arithmetic model. This invariant includes gradual subnormal encodings. -/
theorem unpack_exponent_normalized (format : Format) (bits : BitVec format.numBits) :
    match UnpackedFloat.unpack format bits with
    | .finite _ mantissa exponent _ =>
      format.targetExponent (totalExponent mantissa exponent) = exponent
    | _ => True := by
  unfold UnpackedFloat.unpack
  dsimp only
  by_cases hemax : unpackExponent (spec := format) bits = -1#_
  · rw [ite_eq_left hemax]
    by_cases hmzero : unpackMantissa (spec := format) bits = 0#_
    · rw [ite_eq_left hmzero]
      trivial
    · rw [ite_eq_right hmzero]
      trivial
  · rw [ite_eq_right hemax]
    by_cases hezero : unpackExponent (spec := format) bits = 0#_
    · rw [ite_eq_left hezero]
      by_cases hmzero : unpackMantissa (spec := format) bits = 0#_
      · rw [dite_eq_left hmzero]
        trivial
      · rw [dite_eq_right hmzero]
        have hmNat : (unpackMantissa (spec := format) bits).toNat ≠ 0 := by
          intro h
          exact hmzero (BitVec.eq_of_toNat_eq h)
        have hmLog : (unpackMantissa (spec := format) bits).toNat.log2 <
            format.mantissaBitsWithoutImplicit :=
          (Nat.log2_lt hmNat).mpr (unpackMantissa (spec := format) bits).isLt
        have he : (unpackExponent (spec := format) bits).toNat = 0 := by rw [hezero]; rfl
        dsimp only
        simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
          minExponent_eq_bias, he, Nat.cast_zero]
        omega
    · rw [ite_eq_right hezero]
      have he : 0 < (unpackExponent (spec := format) bits).toNat := by
        have hne : (unpackExponent (spec := format) bits).toNat ≠ 0 := by
          intro h
          exact hezero (BitVec.eq_of_toNat_eq h)
        omega
      dsimp only
      simp only [Format.targetExponent, totalExponent, normalMantissa_log2,
        Format.mantissaBits, minExponent_eq_bias]
      omega

private theorem exponent_range (format : Format) : 2 < 2 ^ format.exponentBits := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) format.he
  norm_num at hp
  omega

/-- Packing a decoded encoding preserves its bits except that a NaN payload
is replaced by the canonical quiet NaN, as the core model requires. -/
theorem pack_unpack (format : Format) (bits : BitVec format.numBits) :
    UnpackedFloat.pack format (UnpackedFloat.unpack format bits) =
      if unpackExponent bits = -1#_ ∧ unpackMantissa bits ≠ 0#_
      then packedNaN format else bits := by
  let e := unpackExponent (spec := format) bits
  let m := unpackMantissa (spec := format) bits
  let s := Sign.ofBitVec (unpackSign (spec := format) bits)
  have reconstruct : packComponents format s e m = bits := packComponents_unpack format bits
  have bound := e.isLt
  have hrange := exponent_range format
  change UnpackedFloat.pack format
    (if e = -1#_ then (if m = 0#_ then .infinity s else .notANumber)
     else if he : e = 0#_ then
       if hm : m = 0#_ then .zero s
       else .finite s m.toNat ((e.toNat : Int) - (format.exponentBias + format.mantissaBitsWithoutImplicit) + 1)
         (by simpa [BitVec.toNat_pos, BitVec.pos_iff_ne_zero] using hm)
     else .finite s (1#1 ++ m).toNat
       ((e.toNat : Int) - (format.exponentBias + format.mantissaBitsWithoutImplicit)) (by simp)) =
      if e = -1#_ ∧ m ≠ 0#_ then packedNaN format else bits
  by_cases hemax : e = -1#_
  · by_cases hmzero : m = 0#_
    · simp only [hemax, hmzero, ↓reduceIte, ne_eq, not_true_eq_false,
        and_false, UnpackedFloat.pack, packedInfinity]
      simpa only [hemax, hmzero, BitVec.ofNat_eq_ofNat] using reconstruct
    · simp [hemax, hmzero, UnpackedFloat.pack]
  · have heNat : e.toNat ≠ maxExponentField format.exponentBits :=
      (exponent_eq_max_iff format e).not.mpr hemax
    have hOverflow : ¬2 ^ format.exponentBits ≤ e.toNat + 1 := by
      unfold maxExponentField at heNat
      omega
    simp only [hemax, ↓reduceIte, false_and]
    by_cases hezero : e = 0#_
    · have heNatZero : e.toNat = 0 := by rw [hezero]; rfl
      by_cases hmzero : m = 0#_
      · simp only [hezero, hmzero, ↓reduceDIte, UnpackedFloat.pack, packedZero]
        simpa only [hezero, hmzero, BitVec.ofNat_eq_ofNat] using reconstruct
      · have hmNat : m.toNat ≠ 0 := by
          intro h
          exact hmzero (BitVec.eq_of_toNat_eq h)
        have hmLog : m.toNat.log2 < format.mantissaBitsWithoutImplicit :=
          (Nat.log2_lt hmNat).mpr m.isLt
        have hBias : ((e.toNat : Int) - (format.exponentBias + format.mantissaBitsWithoutImplicit) + 1 +
            format.exponentBias + format.mantissaBitsWithoutImplicit).toNat = 1 := by
          rw [heNatZero]
          omega
        simp only [dite_eq_left hezero, dite_eq_right hmzero, UnpackedFloat.pack, hBias]
        have hNoOverflow : ¬2 ^ format.exponentBits ≤ 1 + 1 := by omega
        have hNotNormal : ¬m.toNat.log2 + 1 = format.mantissaBits := by
          simp only [Format.mantissaBits]
          omega
        simp only [hNoOverflow, hNotNormal, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        simpa only [hezero] using reconstruct
    · have hBias : ((e.toNat : Int) - (format.exponentBias + format.mantissaBitsWithoutImplicit) +
          format.exponentBias + format.mantissaBitsWithoutImplicit).toNat = e.toNat := by omega
      simp only [hezero, ↓reduceDIte, UnpackedFloat.pack, hBias, hOverflow, ↓reduceIte,
        normalMantissa_log2, Format.mantissaBits]
      simp only [Nat.add_comm format.mantissaBitsWithoutImplicit 1, ↓reduceIte]
      rw [normalMantissa_toNat]
      have hFraction : BitVec.ofNat format.mantissaBitsWithoutImplicit
          (2 ^ format.mantissaBitsWithoutImplicit + m.toNat) = m := by
        apply BitVec.eq_of_toNat_eq
        simp [Nat.mod_eq_of_lt m.isLt]
      rw [hFraction, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact reconstruct

/-- An all-ones exponent has no finite rational value, for either infinity
or any NaN payload. -/
theorem value?_unpack_of_maxExponent (format : Format) (bits : BitVec format.numBits)
    (h : unpackExponent bits = -1#_) : value? (UnpackedFloat.unpack format bits) = none := by
  unfold UnpackedFloat.unpack
  dsimp only
  rw [ite_eq_left h]
  split <;> rfl

/-- The core model's NaN canonicalization preserves the decoded rational value. -/
theorem value?_unpack_pack_unpack (format : Format) (bits : BitVec format.numBits) :
    value? (UnpackedFloat.unpack format (UnpackedFloat.pack format
      (UnpackedFloat.unpack format bits))) = value? (UnpackedFloat.unpack format bits) := by
  rw [pack_unpack]
  split
  next h =>
    rw [value?_unpack_of_maxExponent format _ (by simp [packedNaN]),
      value?_unpack_of_maxExponent format bits h.1]
  next => rfl

/-- Every raw binary32 encoding has the IEEE field-formula value after it is
decoded by Lean's core arithmetic model. This includes exceptional encodings,
for which both rational accessors return `none`. -/
theorem value?_model_unpack32 (x : F32) : value? x.model.unpack = x.toRat? := by
  change value? (UnpackedFloat.unpack .binary32 (UnpackedFloat.pack .binary32
    (UnpackedFloat.unpack .binary32 x.bits.toBitVec))) = _
  rw [value?_unpack_pack_unpack, value?_unpack]
  rfl

/-- The corresponding decoder correctness theorem for all binary64 encodings. -/
theorem value?_model_unpack64 (x : F64) : value? x.model.unpack = x.toRat? := by
  change value? (UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64
    (UnpackedFloat.unpack .binary64 x.bits.toBitVec))) = _
  rw [value?_unpack_pack_unpack, value?_unpack]
  rfl

/-- Core binary32 construction preserves every non-NaN bit pattern, including
infinities and signed zero. -/
theorem model_bits32_of_not_nan (x : F32) (h : ¬x.IsNaN) : x.model.toBits = x.bits := by
  have hfields : ¬(unpackExponent (spec := .binary32) x.bits.toBitVec = -1#_ ∧
      unpackMantissa (spec := .binary32) x.bits.toBitVec ≠ 0#_) := by
    intro hn
    have he : (decode32 x.bits.toNat).exponent = maxExponentField binary32ExponentBits := by
      simpa [unpackExponent_toNat, decode32, binary32ExponentBits, binary32SignificandBits]
        using (exponent_eq_max_iff .binary32 _).mpr hn.1
    have hm : (decode32 x.bits.toNat).trailingSignificand ≠ 0 := by
      intro hm
      apply hn.2
      apply BitVec.eq_of_toNat_eq
      simpa [unpackMantissa_toNat, decode32, binary32ExponentBits, binary32SignificandBits] using hm
    apply h
    simp [F32.IsNaN, classify32, classify, he, hm, maxExponentField, binary32ExponentBits]
  apply UInt32.eq_of_toBitVec_eq
  change UnpackedFloat.pack .binary32 (UnpackedFloat.unpack .binary32 x.bits.toBitVec) = _
  rw [pack_unpack, ite_eq_right hfields]

/-- Core binary64 construction preserves all non-NaN encodings. -/
theorem model_bits64_of_not_nan (x : F64) (h : ¬x.IsNaN) : x.model.toBits = x.bits := by
  have hfields : ¬(unpackExponent (spec := .binary64) x.bits.toBitVec = -1#_ ∧
      unpackMantissa (spec := .binary64) x.bits.toBitVec ≠ 0#_) := by
    intro hn
    have he : (decode64 x.bits.toNat).exponent = maxExponentField binary64ExponentBits := by
      simpa [unpackExponent_toNat, decode64, binary64ExponentBits, binary64SignificandBits]
        using (exponent_eq_max_iff .binary64 _).mpr hn.1
    have hm : (decode64 x.bits.toNat).trailingSignificand ≠ 0 := by
      intro hm
      apply hn.2
      apply BitVec.eq_of_toNat_eq
      simpa [unpackMantissa_toNat, decode64, binary64ExponentBits, binary64SignificandBits] using hm
    apply h
    simp [F64.IsNaN, classify64, classify, he, hm, maxExponentField, binary64ExponentBits]
  apply UInt64.eq_of_toBitVec_eq
  change UnpackedFloat.pack .binary64 (UnpackedFloat.unpack .binary64 x.bits.toBitVec) = _
  rw [pack_unpack, ite_eq_right hfields]

end Silmaril.Numeric.Ieee754.Conformance
