module

public import Silmaril.Numeric.Ieee754.Inspection
import Mathlib.Tactic.NormNum

/-! # Binary64 sign and magnitude utilities

Bit-exact sign reconstruction includes signed zeros, infinities and arbitrary
NaN payloads. Magnitude extraction is also related to natural modulo arithmetic.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Binary64Signs

def magnitudeBits (bits : UInt64) : UInt64 := bits &&& 0x7fffffffffffffff

def withSign (negative : Bool) (bits : UInt64) : UInt64 :=
  if negative then bits ||| 0x8000000000000000 else bits

@[simp] theorem magnitudeBits_toNat (bits : UInt64) :
    (magnitudeBits bits).toNat = bits.toNat % 2 ^ 63 := by
  rw [magnitudeBits, UInt64.toNat_and]
  change bits.toNat &&& (2 ^ 63 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod bits.toNat 63

/-- Reattach the extracted sign without losing any payload bits. -/
theorem withSign_magnitudeBits (bits : UInt64) :
    withSign (F64.ofBits bits).signBit (magnitudeBits bits) = bits := by
  have masked : bits &&& 0x8000000000000000 =
      if (F64.ofBits bits).signBit then 0x8000000000000000 else 0 := by
    apply UInt64.eq_of_toBitVec_eq
    rw [F64.signBit_eq_msb]
    change bits.toBitVec &&& BitVec.twoPow 64 63 =
      (if bits.toBitVec.msb then (0x8000000000000000 : UInt64) else 0).toBitVec
    rw [BitVec.and_twoPow]
    rw [BitVec.msb_eq_getLsbD_last]
    cases bits.toBitVec.getLsbD 63 <;> rfl
  have recombined : (bits &&& 0x7fffffffffffffff) ||| (bits &&& 0x8000000000000000) = bits := by
    exact congrArg F64.bits (F64.copySign_self (F64.ofBits bits))
  rw [masked] at recombined
  cases sign : (F64.ofBits bits).signBit <;>
    simpa only [withSign, magnitudeBits, sign, Bool.false_eq_true, ↓reduceIte, UInt64.or_zero] using recombined

@[simp] theorem magnitudeBits_withSign (negative : Bool) (bits : UInt64) :
    magnitudeBits (withSign negative bits) = magnitudeBits bits := by
  cases negative with
  | false => rfl
  | true =>
    simp only [magnitudeBits, withSign, ↓reduceIte]
    apply UInt64.eq_of_toBitVec_eq
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, BitVec.and_or_distrib_right]
    change (bits.toBitVec &&& 0x7fffffffffffffff#64) ||| 0#64 = _
    exact BitVec.or_zero

theorem signBit_withSign (negative : Bool) (bits : UInt64)
    (clear : magnitudeBits bits = bits) : (F64.ofBits (withSign negative bits)).signBit = negative := by
  cases negative with
  | false =>
    have sign := F64.signBit_abs (F64.ofBits bits)
    change (F64.ofBits (magnitudeBits bits)).signBit = false at sign
    rw [clear] at sign
    exact sign
  | true =>
    simp only [F64.signBit_eq_msb, F64.ofBits, withSign, ↓reduceIte,
      UInt64.toBitVec_or, BitVec.msb_or]
    change (bits.toBitVec.msb || true) = true
    exact Bool.or_true _

theorem magnitudeBits_lt (bits : UInt64) : (magnitudeBits bits).toNat < 2 ^ 63 := by
  rw [magnitudeBits_toNat]
  exact Nat.mod_lt _ (by decide)

theorem exponent_magnitude (bits : UInt64) :
    (decode64 bits.toNat).exponent = (magnitudeBits bits).toNat / 2 ^ 52 := by
  rw [magnitudeBits_toNat]
  change bits.toNat / 2 ^ 52 % 2 ^ 11 = bits.toNat % 2 ^ 63 / 2 ^ 52
  exact (Nat.mod_mul_right_div_self bits.toNat (2 ^ 52) (2 ^ 11)).symm

theorem trailing_magnitude (bits : UInt64) :
    (decode64 bits.toNat).trailingSignificand = (magnitudeBits bits).toNat % 2 ^ 52 := by
  rw [magnitudeBits_toNat]
  change bits.toNat / 1 % 2 ^ 52 = bits.toNat % 2 ^ 63 % 2 ^ 52
  rw [Nat.div_one, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 52 ∣ 2 ^ 63)]

/-- All five IEEE classes are determined by magnitude bits alone. -/
theorem classification_magnitude (bits : UInt64) :
    (F64.ofBits bits).classification =
      if (magnitudeBits bits).toNat = 0 then .zero
      else if (magnitudeBits bits).toNat < 0x0010000000000000 then .subnormal
      else if (magnitudeBits bits).toNat < 0x7ff0000000000000 then .normal
      else if (magnitudeBits bits).toNat = 0x7ff0000000000000 then .infinity else .nan := by
  have bound := magnitudeBits_lt bits
  simp only [F64.classification, F64.ofBits, classify64, classify, binary64ExponentBits,
    exponent_magnitude, trailing_magnitude, maxExponentField]
  norm_num only [Nat.reducePow, Nat.reduceSub] at bound ⊢
  split_ifs <;> simp_all <;> omega

/-- Excluding zero and both nonfinite classes gives the exact positive-finite
magnitude range required by decimal selection and conversion. -/
theorem finite_nonzero_bounds (bits : UInt64)
    (notNaN : (F64.ofBits bits).isNaN = false)
    (notInfinite : (F64.ofBits bits).isInfinite = false)
    (notZero : (F64.ofBits bits).isZero = false) :
    0 < (magnitudeBits bits).toNat ∧ (magnitudeBits bits).toNat ≤ 0x7fefffffffffffff := by
  have classNaN : (F64.ofBits bits).classification ≠ .nan := by
    simpa only [F64.isNaN, F64.IsNaN, F64.classification, decide_eq_false_iff_not] using notNaN
  have classInfinite : (F64.ofBits bits).classification ≠ .infinity := by
    simpa only [F64.isInfinite, beq_eq_false_iff_ne] using notInfinite
  have classZero : (F64.ofBits bits).classification ≠ .zero := by
    simpa only [F64.isZero, beq_eq_false_iff_ne] using notZero
  rw [classification_magnitude] at classNaN classInfinite classZero
  split_ifs at classNaN classInfinite classZero <;> simp_all <;> omega

end Silmaril.Numeric.Ieee754.Binary64Signs
