module

public import Silmaril.Numeric.Ieee754.Rounding.Decoding

/-! # Finite-format packing and exact field recovery -/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Rounding

open Float.Model Float.Model.UnpackedFloat LowPrecision

def coreSpec (format : Format) : FormatSpec :=
  ⟨format.numBits, format.exponentBits, format.mantissaBitsWithoutImplicit, format.exponentBias, .ieee⟩

theorem fractionField_core (format : Format) (bits : BitVec format.numBits) :
    fractionField (coreSpec format) bits.toNat = (unpackMantissa bits).toNat := by
  simp [fractionField, coreSpec, unpackMantissa]

theorem exponentField_core (format : Format) (bits : BitVec format.numBits) :
    exponentField (coreSpec format) bits.toNat = (unpackExponent bits).toNat := by
  simp [exponentField, coreSpec, unpackExponent, Nat.shiftRight_eq_div_pow]

theorem unpackSign_packComponents (format : Format) (sign : Sign)
    (e : BitVec format.exponentBits) (m : BitVec format.mantissaBitsWithoutImplicit) :
    unpackSign (packComponents format sign e m) = sign.toBitVec := by
  ext i hi
  have hi0 : i = 0 := by omega
  subst i
  have hsum : ¬ format.mantissaBitsWithoutImplicit + format.exponentBits < format.mantissaBitsWithoutImplicit := by omega
  have hsub : format.mantissaBitsWithoutImplicit + format.exponentBits - format.mantissaBitsWithoutImplicit = format.exponentBits := by omega
  simp [unpackSign, packComponents, BitVec.getLsbD_append, hsum, hsub, BitVec.getLsbD_eq_getElem, BitVec.getElem_append]

theorem signBit_core (format : Format) (bits : BitVec format.numBits) :
    signBit (coreSpec format) bits.toNat = ((unpackSign bits).toNat == 1) := by
  simp [signBit, coreSpec, FormatSpec.signMask, Format.numBits, unpackSign,
    Nat.shiftRight_eq_div_pow, Nat.add_comm]

theorem fields_packComponents (format : Format) (sign : Sign)
    (e : BitVec format.exponentBits) (m : BitVec format.mantissaBitsWithoutImplicit) :
    fractionField (coreSpec format) (packComponents format sign e m).toNat = m.toNat ∧
    exponentField (coreSpec format) (packComponents format sign e m).toNat = e.toNat ∧
    signBit (coreSpec format) (packComponents format sign e m).toNat = (sign == .negative) := by
  rw [fractionField_core, exponentField_core, signBit_core]
  simp only [unpackMantissa_packComponents, unpackExponent_packComponents, unpackSign_packComponents]
  cases sign <;> decide

/-- Exact decoding of packed finite components, including subnormal exponents. -/
theorem decode_packComponents (format : Format) (sign : Sign)
    (e : BitVec format.exponentBits) (m : BitVec format.mantissaBitsWithoutImplicit)
    (he : e.toNat ≠ 2 ^ format.exponentBits - 1) :
    exactValue? (coreSpec format) (packComponents format sign e m).toNat =
      if e.toNat = 0 then
        some (signedRat (sign == .negative) ((m.toNat : ℚ) *
          (2 : ℚ) ^ (1 - (format.exponentBias : Int) - format.mantissaBitsWithoutImplicit)))
      else
        some (signedRat (sign == .negative) (((2 ^ format.mantissaBitsWithoutImplicit + m.toNat : Nat) : ℚ) *
          (2 : ℚ) ^ ((e.toNat : Int) - format.exponentBias - format.mantissaBitsWithoutImplicit))) := by
  obtain ⟨hf, heq, hs⟩ := fields_packComponents format sign e m
  unfold exactValue? isNaNBits isInfinityBits
  change (if (exponentField (coreSpec format) (packComponents format sign e m).toNat ==
      (coreSpec format).maxExponent && fractionField (coreSpec format) (packComponents format sign e m).toNat != 0) ||
    (exponentField (coreSpec format) (packComponents format sign e m).toNat ==
      (coreSpec format).maxExponent && fractionField (coreSpec format) (packComponents format sign e m).toNat == 0)
    then none else _) = _
  simp only [hf, heq]
  simp only [FormatSpec.maxExponent, coreSpec]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, he, false_and, false_or, ite_false]
  change (if e.toNat = 0 then some (signedRat (signBit (coreSpec format)
    (packComponents format sign e m).toNat) _) else some (signedRat (signBit (coreSpec format)
    (packComponents format sign e m).toNat) _)) = _
  rw [hs]

/-- Canonical finite values have a p-bit mantissa, with smaller values at emin. -/
structure Canonical (format : Format) (m : Nat) (e : Int) : Prop where
  mantissa_lt : m < 2 ^ format.mantissaBits
  exponent_min : format.minExponent ≤ e
  subnormal_exponent : m < 2 ^ format.mantissaBitsWithoutImplicit → e = format.minExponent

theorem minExponent_eq (format : Format) :
    format.minExponent = 1 - (format.exponentBias : Int) - format.mantissaBitsWithoutImplicit := by
  have hp : 1 ≤ 2 ^ (format.exponentBits - 1) := Nat.one_le_pow _ _ (by decide)
  simp only [Format.minExponent, Format.exponentBias, Format.mantissaBits, Nat.cast_sub hp, Nat.cast_add]
  push_cast
  ring

/-- Packing a canonical, nonoverflowing finite value preserves its exact rational value. -/
theorem pack_finite_value (format : Format) (sign : Sign) (m : Nat) (e : Int) (hp : 0 < m)
    (hc : Canonical format m e)
    (ho : (e + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat <
      2 ^ format.exponentBits - 1) :
    exactValue? (coreSpec format) (UnpackedFloat.pack format (.finite sign m e hp)).toNat =
      unpackedRat? (.finite sign m e hp) := by
  have hbiased : 1 ≤ e + (format.exponentBias : Int) + format.mantissaBitsWithoutImplicit := by
    have hmin := hc.exponent_min
    rw [minExponent_eq] at hmin
    omega
  have hno : ¬ 2 ^ format.exponentBits ≤
      (e + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat + 1 := by omega
  simp only [UnpackedFloat.pack, ite_eq_right hno, unpackedRat?]
  by_cases hsub : m < 2 ^ format.mantissaBitsWithoutImplicit
  · have he := hc.subnormal_exponent hsub
    have hl := (Nat.log2_lt (Nat.ne_of_gt hp)).mpr hsub
    have hnormal : ¬ m.log2 + 1 = format.mantissaBits := by
      simp only [Format.mantissaBits]
      omega
    rw [ite_eq_right hnormal]
    have hexp : (0#format.exponentBits).toNat ≠ 2 ^ format.exponentBits - 1 := by
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) format.he
      norm_num at hpow ⊢
      omega
    rw [decode_packComponents format sign (0#format.exponentBits) (BitVec.ofNat _ m) hexp]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, ite_true, Nat.mod_eq_of_lt hsub]
    rw [← minExponent_eq, ← he]
  · have hlow : 2 ^ format.mantissaBitsWithoutImplicit ≤ m := by omega
    have hlog : m.log2 = format.mantissaBitsWithoutImplicit := by
      apply (Nat.log2_eq_iff (Nat.ne_of_gt hp)).mpr
      exact ⟨hlow, by simpa [Format.mantissaBits, Nat.add_comm] using hc.mantissa_lt⟩
    have hnormal : m.log2 + 1 = format.mantissaBits := by simp [hlog, Format.mantissaBits, Nat.add_comm]
    rw [ite_eq_left hnormal]
    let biased := (e + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat
    have hfield : (BitVec.ofNat format.exponentBits biased).toNat = biased := by
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hexp : (BitVec.ofNat format.exponentBits biased).toNat ≠ 2 ^ format.exponentBits - 1 := by
      rw [hfield]
      exact Nat.ne_of_lt ho
    rw [decode_packComponents format sign (BitVec.ofNat _ biased) (BitVec.ofNat _ m) hexp, hfield]
    have hbpos : biased ≠ 0 := by dsimp [biased]; omega
    rw [ite_eq_right hbpos]
    have hmantHi : m < 2 ^ format.mantissaBitsWithoutImplicit * 2 := by
      simpa [Format.mantissaBits, pow_add, Nat.mul_comm] using hc.mantissa_lt
    have hrem : 2 ^ format.mantissaBitsWithoutImplicit + m % 2 ^ format.mantissaBitsWithoutImplicit = m := by
      rw [Nat.mod_eq_sub_mod hlow, Nat.mod_eq_of_lt (by omega)]
      omega
    have heq : (biased : Int) - format.exponentBias - format.mantissaBitsWithoutImplicit = e := by
      dsimp [biased]
      omega
    simp only [BitVec.toNat_ofNat, hrem, heq]

end Silmaril.Numeric.Ieee754.Rounding
