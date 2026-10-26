module

public import Silmaril.Numeric.Ieee754.SignedRationalRounding
import Mathlib.Tactic.Linarith

/-! # Signed conversion against the actual binary64 rational decoder

Sign symmetry is related to the existing core decoder, and signed nearest
conversion is compared with every finite binary64 encoding of either sign.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Binary64Signs

@[simp] theorem magnitudeBits_idempotent (bits : UInt64) :
    magnitudeBits (magnitudeBits bits) = magnitudeBits bits := by
  simp only [magnitudeBits, UInt64.and_assoc]
  rfl

@[simp] theorem signBit_magnitudeBits (bits : UInt64) :
    (F64.ofBits (magnitudeBits bits)).signBit = false :=
  F64.signBit_abs (F64.ofBits bits)

/-- The decoder's arithmetic sign field is the existing raw sign-bit query. -/
theorem decode_sign (bits : UInt64) : (decode64 bits.toNat).sign = (F64.ofBits bits).signBit := by
  rw [F64.signBit_eq_msb, BitVec.msb_eq_decide]
  apply Bool.eq_iff_iff.mpr
  simp only [decode64, decode, field, binary64ExponentBits, binary64SignificandBits,
    F64.ofBits, UInt64.toNat_toBitVec, beq_iff_eq, decide_eq_true_eq]
  have bound := bits.toNat_lt
  norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.reducePow] at bound ⊢
  omega

theorem decoded_ext (left right : Decoded) (sign : left.sign = right.sign)
    (exponent : left.exponent = right.exponent) (trailing : left.trailingSignificand = right.trailingSignificand) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Clearing the sign leaves the exponent and significand untouched. -/
theorem decode_magnitudeBits (bits : UInt64) :
    decode64 (magnitudeBits bits).toNat = { decode64 bits.toNat with sign := false } := by
  apply decoded_ext
  · rw [decode_sign, signBit_magnitudeBits]
  · rw [exponent_magnitude, magnitudeBits_idempotent, ← exponent_magnitude]
  · rw [trailing_magnitude, magnitudeBits_idempotent, ← trailing_magnitude]

/-- Sign symmetry holds for the actual core-decoded rational. The convenience
`rational` value is zero on nonfinite inputs, so this identity is total. -/
theorem rational_signed_magnitude (bits : UInt64) :
    Decimal.rational bits = signed (F64.ofBits bits).signBit (Decimal.rational (magnitudeBits bits)) := by
  simp only [Decimal.rational, Conformance.value?_model_unpack64, F64.toRat?, F64.ofBits, value64?]
  rw [decode_magnitudeBits]
  simp only [finiteValue]
  rw [decode_sign]
  simp only [F64.ofBits]
  split_ifs <;> cases sign : (F64.mk bits).signBit <;> simp [signed]

end Silmaril.Numeric.Ieee754.Binary64Signs

namespace Silmaril.Numeric.Ieee754.RationalRounding

open Binary64Signs

/-- The exact signed meaning of the returned bits follows from the existing
core decoder; magnitude and sign are not merely output metadata. -/
theorem rational_roundSigned (negative : Bool) (query : ℚ) :
    Decimal.rational (roundSigned negative query) = signed negative (Decimal.rational (roundPositive query)) := by
  rw [rational_signed_magnitude, signBit_roundSigned, magnitudeBits_roundSigned]

/-- Global nearest-distance correctness compares with all finite raw encodings,
including competitors whose sign differs from the exact query. -/
theorem roundSigned_nearestFinite (negative : Bool) (query : ℚ) (nonnegative : 0 ≤ query)
    (below : query < overflowThreshold) (candidate : UInt64)
    (finite : (magnitudeBits candidate).toNat ≤ 0x7fefffffffffffff) :
    |signed negative query - Decimal.rational (roundSigned negative query)| ≤
      |signed negative query - Decimal.rational candidate| := by
  obtain ⟨_, nearest, _⟩ := roundPositive_nearestFinite query nonnegative below
  have same := nearest (magnitudeBits candidate) finite
  have zero := nearest 0 (by decide)
  have candidateNonnegative : 0 ≤ Decimal.rational (magnitudeBits candidate) := by
    rw [Decimal.rational_eq_binaryMagnitude _ finite]
    exact BinaryMagnitude.value_nonneg 52 1023 _
  have rationalZero : Decimal.rational 0 = 0 := by
    rw [Decimal.rational_eq_binaryMagnitude 0 (by decide)]
    exact BinaryMagnitude.value_zero 52 1023
  rw [rationalZero, sub_zero, abs_of_nonneg nonnegative] at zero
  rw [rational_roundSigned, rational_signed_magnitude candidate]
  have negDistance (a b : ℚ) : |-a - -b| = |a - b| := by
    have identity : -a - -b = -(a - b) := by ring
    rw [identity, abs_neg]
  cases negative <;> cases (F64.ofBits candidate).signBit <;> simp only [signed, Bool.false_eq_true, ↓reduceIte]
  · exact same
  · rw [sub_neg_eq_add, abs_of_nonneg (add_nonneg nonnegative candidateNonnegative)]
    exact zero.trans (le_add_of_nonneg_right candidateNonnegative)
  · rw [negDistance, abs_of_nonpos (by linarith : -query - Decimal.rational (magnitudeBits candidate) ≤ 0)]
    linarith
  · simpa only [negDistance] using same

end Silmaril.Numeric.Ieee754.RationalRounding
