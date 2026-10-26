module

public import Silmaril.Numeric.Float.Encoding
public import Silmaril.Numeric.Ieee754.Flags
public import Silmaril.Numeric.Ieee754.IntegerRounding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Raw encodings as operands of the exception specification

The IEEE exception flags of `Silmaril.Numeric.Ieee754.Flags` classify operands
as `FlagSpec.Datum` values: signaling or quiet NaN, signed infinity, or a finite
value with its sign bit and exact rational value. `Bits.datum` reads a raw
encoding of any format this way, and this module relates it to the bit-level
predicates the profile operations use:

* `datum_isNaN`, `datum_isSignaling`: the NaN and signaling-NaN tests agree
  (IEEE 754-2019 §6.2.1 quiet-bit convention);
* `isSubnormal_iff`: `Bits.isSubnormal` is exactly `Datum.IsSubnormal`, a nonzero
  value of magnitude below `2 ^ emin` (§3.4);
* `datum_flushSubnormal`: bit-level subnormal flushing is the specification's
  denormals-are-zero hook `FlagSpec.flushInput`;
* `value?_value`, `toInt?_value`: the exact value of the core decoder
  (`Bits.value`), used by the result computations, is the finite value of
  `datum`, and executable float-to-integer rounding is `FlagSpec.roundInt` of it.
-/

@[expose] public section

namespace Silmaril.Numeric.Float

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec

namespace Bits

variable {fmt : Format}

/-- The operand as the exception specification sees it. -/
def datum (b : Bits fmt) : Datum := Datum.decode fmt b.toNat

private theorem signBit_eq (b : Bits fmt) : b.signBit = ((unpackSign b).toNat == 1) := by
  unfold signBit
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj]
  simp

/-- The field decoder of `Silmaril.Numeric.Ieee754` reads the unpacked fields. -/
theorem decode_eq (b : Bits fmt) :
    Silmaril.Numeric.Ieee754.decode fmt.exponentBits fmt.mantissaBitsWithoutImplicit b.toNat =
      ⟨b.signBit, (unpackExponent b).toNat, (unpackMantissa b).toNat⟩ := by
  rw [signBit_eq, Silmaril.Numeric.Ieee754.Conformance.unpackExponent_toNat,
    Silmaril.Numeric.Ieee754.Conformance.unpackMantissa_toNat,
    Silmaril.Numeric.Ieee754.Conformance.unpackSign_toNat]
  rfl

/-- `datum` in terms of the unpacked fields. -/
theorem datum_eq (b : Bits fmt) :
    b.datum = Datum.ofDecoded fmt.exponentBits fmt.mantissaBitsWithoutImplicit fmt.exponentBias
      ⟨b.signBit, (unpackExponent b).toNat, (unpackMantissa b).toNat⟩ := by
  rw [datum, Datum.decode, decode_eq]

private theorem exponent_eq_allOnes_iff (b : Bits fmt) :
    unpackExponent b = -1#_ ↔
      (unpackExponent b).toNat = Silmaril.Numeric.Ieee754.maxExponentField fmt.exponentBits := by
  rw [← BitVec.toNat_inj, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
  rfl

private theorem exponent_eq_zero_iff (b : Bits fmt) :
    unpackExponent b = 0#_ ↔ (unpackExponent b).toNat = 0 := by
  rw [← BitVec.toNat_inj]
  simp

private theorem mantissa_eq_zero_iff (b : Bits fmt) :
    unpackMantissa b = 0#_ ↔ (unpackMantissa b).toNat = 0 := by
  rw [← BitVec.toNat_inj]
  simp

private theorem maxExponentField_ne_zero (fmt : Format) :
    Silmaril.Numeric.Ieee754.maxExponentField fmt.exponentBits ≠ 0 := by
  have := fmt.he
  have : 1 < 2 ^ fmt.exponentBits := Nat.one_lt_two_pow_iff.mpr (by omega)
  unfold Silmaril.Numeric.Ieee754.maxExponentField
  omega

/-- A NaN encoding classifies as a NaN, signaling exactly when the quiet bit is
clear. -/
theorem datum_of_isNaN {b : Bits fmt} (h : b.isNaN = true) :
    b.datum = .nan b.isSignalingNaN := by
  have h' := h
  simp only [isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h'
  rw [exponent_eq_allOnes_iff, mantissa_eq_zero_iff] at h'
  rw [datum_eq]
  simp only [Datum.ofDecoded, Silmaril.Numeric.Ieee754.finiteValue, h'.1, beq_self_eq_true,
    ↓reduceIte, h'.2]
  congr 1
  rw [isSignalingNaN, h, Bool.true_and, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  have hm := fmt.hm
  have hlt := (unpackMantissa b).isLt
  generalize (unpackMantissa b).toNat = T at hlt
  have hpow : 2 ^ fmt.mantissaBitsWithoutImplicit =
      2 * 2 ^ (fmt.mantissaBitsWithoutImplicit - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at hlt
  generalize 2 ^ (fmt.mantissaBitsWithoutImplicit - 1) = P at hlt ⊢
  have hP : 0 < P := by omega
  by_cases hT : T < P
  · have : T / P = 0 := Nat.div_eq_of_lt hT
    simp [this, hT]
  · have h1 : T / P = 1 := by
      have : 1 ≤ T / P := (Nat.le_div_iff_mul_le hP).mpr (by omega)
      have : T / P < 2 := (Nat.div_lt_iff_lt_mul hP).mpr (by omega)
      omega
    simp [h1, hT]

/-- An infinity encoding classifies as the infinity of its sign. -/
theorem datum_of_isInfinite {b : Bits fmt} (h : b.isInfinite = true) :
    b.datum = .infinity b.signBit := by
  simp only [isInfinite, Bool.and_eq_true, beq_iff_eq] at h
  rw [exponent_eq_allOnes_iff, ] at h
  rw [mantissa_eq_zero_iff] at h
  rw [datum_eq]
  simp [Datum.ofDecoded, Silmaril.Numeric.Ieee754.finiteValue, h.1, h.2]

/-- A finite encoding classifies as a finite value with its sign bit. -/
theorem datum_of_finite {b : Bits fmt} (h : unpackExponent b ≠ -1#_) :
    ∃ value, b.datum = .finite b.signBit value ∧
      Silmaril.Numeric.Ieee754.finiteValue fmt.exponentBits fmt.mantissaBitsWithoutImplicit
        fmt.exponentBias ⟨b.signBit, (unpackExponent b).toNat, (unpackMantissa b).toNat⟩ =
          some value := by
  rw [ne_eq, exponent_eq_allOnes_iff] at h
  have hsome : ∃ value, Silmaril.Numeric.Ieee754.finiteValue fmt.exponentBits
      fmt.mantissaBitsWithoutImplicit fmt.exponentBias
        ⟨b.signBit, (unpackExponent b).toNat, (unpackMantissa b).toNat⟩ = some value := by
    unfold Silmaril.Numeric.Ieee754.finiteValue
    simp only [beq_iff_eq, h, ↓reduceIte]
    split <;> exact ⟨_, rfl⟩
  obtain ⟨value, hv⟩ := hsome
  refine ⟨value, ?_, hv⟩
  rw [datum_eq]
  unfold Datum.ofDecoded
  rw [hv]

@[simp] theorem datum_isNaN (b : Bits fmt) : b.datum.isNaN = b.isNaN := by
  by_cases hn : b.isNaN = true
  · rw [datum_of_isNaN hn, hn]
    rfl
  · rw [Bool.not_eq_true] at hn
    rw [hn]
    by_cases hi : b.isInfinite = true
    · rw [datum_of_isInfinite hi]
      rfl
    · have he : unpackExponent b ≠ -1#_ := by
        intro he
        simp only [isNaN, he, beq_self_eq_true, Bool.true_and, bne_eq_false_iff_eq] at hn
        simp [isInfinite, he, hn] at hi
      obtain ⟨v, hv, -⟩ := datum_of_finite he
      rw [hv]
      rfl

@[simp] theorem datum_isSignaling (b : Bits fmt) : b.datum.isSignaling = b.isSignalingNaN := by
  by_cases hn : b.isNaN = true
  · rw [datum_of_isNaN hn]
    rfl
  · have hs : b.isSignalingNaN = false := by
      simp only [isSignalingNaN, Bool.not_eq_true] at hn ⊢
      simp [hn]
    rw [hs]
    cases h : b.datum with
    | nan s =>
      have := datum_isNaN b
      rw [h] at this
      simp_all [Datum.isNaN]
    | infinity _ => rfl
    | finite _ _ => rfl

/-- The exact value of a zero-exponent encoding. -/
private theorem finiteValue_zeroExponent (s : Bool) (T : ℕ) :
    Silmaril.Numeric.Ieee754.finiteValue fmt.exponentBits fmt.mantissaBitsWithoutImplicit
        fmt.exponentBias ⟨s, 0, T⟩ =
      some (Silmaril.Numeric.Ieee754.signed s
        ((T : ℚ) / ((2 ^ fmt.mantissaBitsWithoutImplicit : ℕ) : ℚ) * 2 ^ emin fmt)) := by
  simp only [Silmaril.Numeric.Ieee754.finiteValue, beq_iff_eq,
    (maxExponentField_ne_zero fmt).symm, ↓reduceIte]
  rfl

private theorem abs_signed (s : Bool) (q : ℚ) : |Silmaril.Numeric.Ieee754.signed s q| = |q| := by
  cases s <;> simp [Silmaril.Numeric.Ieee754.signed]

private theorem signed_eq_zero_iff (s : Bool) (q : ℚ) :
    Silmaril.Numeric.Ieee754.signed s q = 0 ↔ q = 0 := by
  cases s <;> simp [Silmaril.Numeric.Ieee754.signed]

/-- `Bits.isSubnormal` is the specification's subnormal class: a nonzero finite
value of magnitude below `2 ^ emin`. -/
theorem isSubnormal_iff (b : Bits fmt) : b.isSubnormal = true ↔ b.datum.IsSubnormal fmt := by
  have hmax := maxExponentField_ne_zero fmt
  have hTlt := (unpackMantissa b).isLt
  have h2t : (0 : ℚ) < ((2 ^ fmt.mantissaBitsWithoutImplicit : ℕ) : ℚ) := by positivity
  have hTq : ((unpackMantissa b).toNat : ℚ) < ((2 ^ fmt.mantissaBitsWithoutImplicit : ℕ) : ℚ) := by
    exact_mod_cast hTlt
  simp only [isSubnormal, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, exponent_eq_zero_iff,
    mantissa_eq_zero_iff]
  by_cases hE : (unpackExponent b).toNat = 0
  · have he : unpackExponent b ≠ -1#_ := by
      rw [ne_eq, exponent_eq_allOnes_iff, hE]
      exact Ne.symm hmax
    obtain ⟨v, hv, hfv⟩ := datum_of_finite he
    rw [hE, finiteValue_zeroExponent, Option.some.injEq] at hfv
    rw [hv]
    simp only [hE, true_and, Datum.IsSubnormal]
    rw [← hfv, abs_signed]
    simp only [ne_eq, signed_eq_zero_iff]
    have hq : 0 ≤ ((unpackMantissa b).toNat : ℚ) / ((2 ^ fmt.mantissaBitsWithoutImplicit : ℕ) : ℚ) *
        2 ^ emin fmt := by positivity
    rw [abs_of_nonneg hq]
    have hpow : (0 : ℚ) < 2 ^ emin fmt := two_zpow_pos _
    constructor
    · intro hT
      have hT' : (0 : ℚ) < (unpackMantissa b).toNat := by exact_mod_cast Nat.pos_of_ne_zero hT
      refine ⟨by positivity, ?_⟩
      have : ((unpackMantissa b).toNat : ℚ) / ((2 ^ fmt.mantissaBitsWithoutImplicit : ℕ) : ℚ) < 1 :=
        (div_lt_one h2t).mpr hTq
      nlinarith
    · rintro ⟨hne, -⟩ hT
      apply hne
      simp [hT]
  · simp only [hE, false_and, false_iff]
    by_cases he : unpackExponent b = -1#_
    · by_cases hT : unpackMantissa b = 0#_
      · rw [datum_of_isInfinite (by simp [isInfinite, he, hT])]
        exact id
      · rw [datum_of_isNaN (by simp [isNaN, he, hT])]
        exact id
    · obtain ⟨v, hv, hfv⟩ := datum_of_finite he
      rw [hv]
      rintro ⟨-, hsmall⟩
      rw [exponent_eq_allOnes_iff] at he
      simp only [Silmaril.Numeric.Ieee754.finiteValue, beq_iff_eq, he, hE, ↓reduceIte,
        Option.some.injEq] at hfv
      rw [← hfv, abs_signed] at hsmall
      have hq : (0 : ℚ) ≤ ((unpackMantissa b).toNat : ℚ) /
          ((2 ^ fmt.mantissaBitsWithoutImplicit : ℕ) : ℚ) := by positivity
      have hlow : (2 : ℚ) ^ emin fmt ≤
          (2 : ℚ) ^ (((unpackExponent b).toNat : ℤ) - (fmt.exponentBias : ℤ)) := by
        apply zpow_le_zpow_right₀ (by norm_num)
        unfold emin emax
        omega
      have hpos : (0 : ℚ) < (2 : ℚ) ^ (((unpackExponent b).toNat : ℤ) - (fmt.exponentBias : ℤ)) :=
        two_zpow_pos _
      rw [abs_of_nonneg (by positivity)] at hsmall
      nlinarith

/-- Bit-level subnormal flushing is the specification's denormals-are-zero hook. -/
theorem datum_flushSubnormal (b : Bits fmt) :
    (flushSubnormal b).datum = FlagSpec.flushInput fmt b.datum := by
  unfold flushSubnormal
  split
  next h =>
    have hs := (isSubnormal_iff b).mp h
    have hE : unpackExponent b = 0#_ := by
      simp only [isSubnormal, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    have he : unpackExponent b ≠ -1#_ := by
      rw [hE]
      exact fun h' => allOnes_exponent_ne_zero fmt h'.symm
    obtain ⟨v, hv, -⟩ := datum_of_finite he
    rw [hv] at hs ⊢
    rw [flushInput_of_subnormal fmt hs, datum_eq]
    have hsign : Bits.signBit (fmt := fmt) (packedZero fmt (sign b)) = b.signBit := by
      simp [signBit, packedZero, sign,
        Silmaril.Numeric.Ieee754.Conformance.unpackSign_packComponents]
    rw [hsign]
    have h0 (n : ℕ) : (0 : BitVec n).toNat = 0 := rfl
    simp only [packedZero, unpackExponent_packComponents, unpackMantissa_packComponents, h0]
    unfold Datum.ofDecoded
    rw [finiteValue_zeroExponent]
    simp [Silmaril.Numeric.Ieee754.signed]
  next h =>
    rw [flushInput_of_not_subnormal]
    rw [← isSubnormal_iff]
    simpa using h

/-! ## The decoder's value is the classified value -/

/-- The finite value of `datum`, if any. -/
def finiteValue? : Datum → Option ℚ
  | .finite _ value => some value
  | _ => none

/-- The exact value of the core decoder is the finite value of `datum`; NaNs and
infinities have none. -/
theorem value?_value (b : Bits fmt) :
    Silmaril.Numeric.Ieee754.Conformance.value? b.value = finiteValue? b.datum := by
  by_cases he : unpackExponent b = -1#_
  · have hv : b.value = .notANumber ∨ ∃ s, b.value = .infinity s := by
      unfold value UnpackedFloat.unpack
      simp only [he, ↓reduceIte]
      split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
    have hd : finiteValue? b.datum = none := by
      by_cases hm : unpackMantissa b = 0#_
      · rw [datum_of_isInfinite (by simp [isInfinite, he, hm])]
        rfl
      · rw [datum_of_isNaN (by simp [isNaN, he, hm])]
        rfl
    rw [hd]
    rcases hv with hv | ⟨s, hv⟩ <;> rw [hv] <;> rfl
  · obtain ⟨v, hv, hfv⟩ := datum_of_finite he
    rw [hv, value, Silmaril.Numeric.Ieee754.Conformance.value?_unpack, decode_eq, hfv]
    rfl

/-- The executable float-to-integer rounding (`Rounding.toInt?`) of the decoded
value is `FlagSpec.roundInt` of the classified value, and fails exactly for NaNs
and infinities. -/
theorem toInt?_value (mode : RoundingMode) (b : Bits fmt) :
    Silmaril.Numeric.Ieee754.Rounding.toInt? mode b.value =
      (finiteValue? b.datum).map (roundInt mode) := by
  rw [← value?_value]
  generalize b.value = u
  cases u with
  | notANumber => rfl
  | infinity s => rfl
  | zero s =>
    simp [Silmaril.Numeric.Ieee754.Rounding.toInt?, Silmaril.Numeric.Ieee754.Conformance.value?]
  | finite sign n e hn =>
    obtain ⟨rounded, hr, hm⟩ :=
      Silmaril.Numeric.Ieee754.Conformance.toInt?_finite_correct mode sign n e hn
    rw [hr]
    have hq : (0 : ℚ) ≤ (n : ℚ) * 2 ^ e := by positivity
    have := roundInt_of_mantissaRounds mode sign hq hm
    simp only [Silmaril.Numeric.Ieee754.Conformance.value?, Option.map_some, Option.some.injEq]
    rw [← this]
    congr 1
    cases sign <;> simp [Silmaril.Numeric.Ieee754.Conformance.dyadic, Sign.apply]

end Bits

end Silmaril.Numeric.Float
