module

public import Silmaril.Numeric.Ieee754.DecimalLayout
public import Silmaril.Numeric.Ieee754.SignedRationalRounding

/-! # Universal binary64 formatter round-trips

The complete rendered string is parsed and rounded by exact rational arithmetic.
All non-NaN encodings round-trip bit-for-bit, including negative zero and both
infinities. NaN spelling deliberately discards sign and payload and parses to
the canonical quiet NaN.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

open Binary64Signs RationalRounding

theorem magnitudeBits_eq_zero_of_isZero (bits : UInt64) (zero : (F64.ofBits bits).isZero = true) :
    magnitudeBits bits = 0 := by
  have classification : (F64.ofBits bits).classification = .zero := by
    simpa only [F64.isZero, beq_iff_eq] using zero
  rw [classification_magnitude] at classification
  apply UInt64.toNat_inj.mp
  change (magnitudeBits bits).toNat = 0
  split_ifs at classification
  simp_all

theorem magnitudeBits_eq_infinity_of_isInfinite (bits : UInt64)
    (infinite : (F64.ofBits bits).isInfinite = true) : magnitudeBits bits = 0x7ff0000000000000 := by
  have classification : (F64.ofBits bits).classification = .infinity := by
    simpa only [F64.isInfinite, beq_iff_eq] using infinite
  rw [classification_magnitude] at classification
  apply UInt64.toNat_inj.mp
  change (magnitudeBits bits).toNat = 0x7ff0000000000000
  split_ifs at classification
  simp_all

/-- The exact spellings of infinities preserve the sign. -/
theorem parse_signed_infinity (negative : Bool) :
    parseBinary64 ((if negative then "-" else "") ++ "inf") =
      some (withSign negative 0x7ff0000000000000) := by
  cases negative <;> rfl

/-- A zero decimal mantissa retains its explicit sign through parsing and
conversion, independently of the rational value being zero in both cases. -/
theorem parse_signed_zero (negative : Bool) :
    parseBinary64 ((if negative then "-" else "") ++ "0.0") =
      some (withSign negative 0) := by
  cases negative <;>
    simp [parseBinary64, DecimalText.parse, DecimalText.parseFinite, DecimalText.scan,
      DecimalText.finish, roundFinite, roundSigned_zero, withSign, Char.isDigit]

theorem parse_signed_layout (negative : Bool) (number : Number) :
    parseBinary64 ((if negative then "-" else "") ++ layout number) =
      some (roundSigned negative number.value) := by
  cases negative with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, String.empty_append, parseBinary64, parse_layout,
      Option.map_some, roundFinite]
  | true =>
    simp only [↓reduceIte, parseBinary64, parse_negative_layout, Option.map_some, roundFinite]

/-- Every raw binary64 encoding has a complete render/parse/round result.
Only NaN payload/sign canonicalization prevents literal raw-bit identity. -/
theorem parseBinary64_repr (bits : UInt64) :
    parseBinary64 (repr bits) =
      some (if (F64.ofBits bits).isNaN then 0x7ff8000000000000 else bits) := by
  by_cases nan : (F64.ofBits bits).isNaN = true
  · simp only [repr, nan, ↓reduceIte, parseBinary64, DecimalText.parse, beq_self_eq_true,
      Option.map_some]
  · have notNaN : (F64.ofBits bits).isNaN = false := Bool.eq_false_iff.mpr nan
    simp only [repr, notNaN, Bool.false_eq_true, ↓reduceIte]
    by_cases infinite : (F64.ofBits bits).isInfinite = true
    · rw [ite_eq_left infinite, parse_signed_infinity]
      congr 1
      rw [← magnitudeBits_eq_infinity_of_isInfinite bits infinite, withSign_magnitudeBits]
    · have notInfinite : (F64.ofBits bits).isInfinite = false := Bool.eq_false_iff.mpr infinite
      rw [ite_eq_right infinite]
      by_cases zero : (F64.ofBits bits).isZero = true
      · rw [ite_eq_left zero, parse_signed_zero]
        congr 1
        rw [← magnitudeBits_eq_zero_of_isZero bits zero, withSign_magnitudeBits]
      · have notZero : (F64.ofBits bits).isZero = false := Bool.eq_false_iff.mpr zero
        rw [ite_eq_right zero, parse_signed_layout]
        obtain ⟨positive, finite⟩ := finite_nonzero_bounds bits notNaN notInfinite notZero
        congr 1
        apply roundSigned_of_magnitude
        exact shortest_roundtrips (magnitudeBits bits) positive finite

/-- Bit-for-bit round-trip for every non-NaN encoding, with no sign or
finiteness restriction and no exception for negative zero. -/
theorem parseBinary64_repr_of_notNaN (bits : UInt64) (notNaN : (F64.ofBits bits).isNaN = false) :
    parseBinary64 (repr bits) = some bits := by
  rw [parseBinary64_repr, notNaN]
  rfl

/-- All NaN encodings have the same spelling, regardless of sign or payload. -/
theorem repr_of_isNaN (bits : UInt64) (nan : (F64.ofBits bits).isNaN = true) : repr bits = "nan" := by
  simp only [repr, nan, ↓reduceIte]

/-- The formatter's zero spelling includes `.0` and the raw zero sign. -/
theorem repr_of_isZero (bits : UInt64) (zero : (F64.ofBits bits).isZero = true) :
    repr bits = (if (F64.ofBits bits).signBit then "-" else "") ++ "0.0" := by
  have classification : (F64.ofBits bits).classification = .zero := by
    simpa only [F64.isZero, beq_iff_eq] using zero
  have notNaN : (F64.ofBits bits).isNaN = false := by
    change decide ((F64.ofBits bits).classification = .nan) = false
    rw [classification]; rfl
  have notInfinite : (F64.ofBits bits).isInfinite = false := by
    simp only [F64.isInfinite, classification]; rfl
  simp only [repr, notNaN, notInfinite, zero, Bool.false_eq_true, ↓reduceIte]

/-- Both infinity signs use the conventional `inf` spelling. -/
theorem repr_of_isInfinite (bits : UInt64) (infinite : (F64.ofBits bits).isInfinite = true) :
    repr bits = (if (F64.ofBits bits).signBit then "-" else "") ++ "inf" := by
  have classification : (F64.ofBits bits).classification = .infinity := by
    simpa only [F64.isInfinite, beq_iff_eq] using infinite
  have notNaN : (F64.ofBits bits).isNaN = false := by
    change decide ((F64.ofBits bits).classification = .nan) = false
    rw [classification]; rfl
  simp only [repr, notNaN, infinite, Bool.false_eq_true, ↓reduceIte]

end Silmaril.Numeric.Ieee754.Decimal
