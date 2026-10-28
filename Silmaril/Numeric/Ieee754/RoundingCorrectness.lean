module

public import Silmaril.Numeric.Ieee754.Exact
public import Silmaril.Numeric.Ieee754.Residual
public import Silmaril.Numeric.Ieee754.Normalization
public import Silmaril.Numeric.Ieee754.PackingCorrectness

/-!
# Mathematical correctness of the unbounded rounding stages

The certificates in this module combine exact significand rounding, residual
soundness, and value-preserving carry normalization. They describe rounding on
an exponent grid; the bounded interchange encoding and its overflow policy
remain separate from these theorems. IEEE 754-2019 §§4.3, 5.4.1, 7.4:
<https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section
namespace Silmaril.Numeric.Ieee754.Conformance
open Float.Model Float.Model.UnpackedFloat

/-- Numerical effect of the complete two-shift rounding stage: its carry
normalization changes the representation, but not the rounded value. -/
theorem roundWithAccuracy_value (format : Format) (mode : RoundingMode)
    (sign : Sign) (n : Nat) (exponent : Int) (accuracy : Accuracy) :
    let shifted := shiftToTargetExponent format n exponent accuracy
    let rounded := Rounding.roundMantissa mode sign shifted.1.mantissa shifted.1.accuracy
    value? (Rounding.roundWithAccuracy format mode sign n exponent accuracy) =
      some (dyadic (sign.apply rounded) shifted.2) := by
  let shifted := shiftToTargetExponent format n exponent accuracy
  let rounded := Rounding.roundMantissa mode sign shifted.1.mantissa shifted.1.accuracy
  let final := shiftToTargetExponent format rounded shifted.2 .exact
  have hm : rounded ≤ 2 ^ format.mantissaBits :=
    roundedShift_mantissa_le format mode sign n exponent accuracy
  have he : format.minExponent ≤ shifted.2 :=
    shiftToTargetExponent_exponent_ge format n exponent accuracy
  have hv : (final.1.mantissa : ℚ) * (2 : ℚ) ^ final.2 =
      (rounded : ℚ) * (2 : ℚ) ^ shifted.2 := carryShift_value format rounded shifted.2 hm he
  have hdy : dyadic (sign.apply final.1.mantissa) final.2 =
      dyadic (sign.apply rounded) shifted.2 := by
    cases sign with
    | positive => simpa [dyadic, Sign.apply] using hv
    | negative => simpa [dyadic, Sign.apply] using congrArg Neg.neg hv
  change value? (if h : final.1.mantissa = 0 then .zero sign else
    .finite sign final.1.mantissa final.2 (Nat.pos_of_ne_zero h)) =
      some (dyadic (sign.apply rounded) shifted.2)
  split
  next hz =>
    rw [← hdy]
    cases sign <;> simp [value?, dyadic, Sign.apply, hz]
  next _ => exact congrArg some hdy

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The result is a correctly rounded value on the selected exponent grid.
This specification does not mention residual bits, shifts, or rounding code. -/
def RoundsOnGrid (mode : RoundingMode) (sign : Sign) (magnitude : K)
    (exponent : Int) (result : UnpackedFloat) : Prop :=
  ∃ n : Nat, MantissaRounds mode sign (magnitude / (2 : K) ^ exponent) n ∧
    value? result = some (dyadic (sign.apply n) exponent)

/-- End-to-end rounding-stage certificate, including the exact carry step.
The input may already contain a nonzero division residual. -/
theorem roundWithAccuracy_correct (format : Format) (mode : RoundingMode)
    (sign : Sign) (n : Nat) (exponent : Int) (accuracy : Accuracy) (q : K)
    (sound : AccuracySound n accuracy q) :
    RoundsOnGrid mode sign (q * (2 : K) ^ exponent)
      (shiftToTargetExponent format n exponent accuracy).2
      (Rounding.roundWithAccuracy format mode sign n exponent accuracy) := by
  let target := format.targetExponent (totalExponent n exponent)
  let amount := (target - exponent).toNat
  let shifted := shiftToTargetExponent format n exponent accuracy
  refine ⟨Rounding.roundMantissa mode sign shifted.1.mantissa shifted.1.accuracy, ?_,
    roundWithAccuracy_value format mode sign n exponent accuracy⟩
  have hc := shiftToExponent_round_correct mode sign n exponent target accuracy q sound
  have hscale : q * (2 : K) ^ exponent / (2 : K) ^ shifted.2 = q / (2 : K) ^ amount := by
    change q * (2 : K) ^ exponent / (2 : K) ^ (exponent + (amount : Int)) = _
    rw [zpow_add₀ (by norm_num : (2 : K) ≠ 0), zpow_natCast]
    field_simp
  change MantissaRounds mode sign (q * (2 : K) ^ exponent / (2 : K) ^ shifted.2) _
  rw [hscale]
  exact hc

/-- Every finite dyadic input is rounded correctly on the grid selected by its
leading bit and the minimum subnormal exponent. This includes the initial exact
left alignment and the final exact carry normalization. -/
theorem roundUnpacked_finite_correct (format : Format) (mode : RoundingMode)
    (sign : Sign) (n : Nat) (exponent : Int) (hn : 0 < n) :
    RoundsOnGrid mode sign ((n : ℚ) * (2 : ℚ) ^ exponent)
      (format.targetExponent (totalExponent n exponent))
      (Rounding.roundUnpacked format mode (.finite sign n exponent hn)) := by
  let target := format.targetExponent (totalExponent n exponent)
  let aligned := decreaseExponent n exponent target
  have hready := decreaseExponent_ready format n exponent (Nat.ne_of_gt hn)
  have htotal := decreaseExponent_totalExponent n exponent target (Nat.ne_of_gt hn)
  have hgrid : (shiftToTargetExponent format aligned.1 aligned.2 .exact).2 = target := by
    rw [shiftToTargetExponent_exponent_eq format aligned.1 aligned.2 .exact hready]
    rw [htotal]
  have hvalue : (aligned.1 : ℚ) * (2 : ℚ) ^ aligned.2 = (n : ℚ) * (2 : ℚ) ^ exponent := by
    simpa only [dyadic, Sign.apply, Int.cast_natCast] using
      decreaseExponent_value .positive n exponent target
  have hc := roundWithAccuracy_correct format mode sign aligned.1 aligned.2 .exact
    (aligned.1 : ℚ) rfl
  rw [hgrid, hvalue] at hc
  exact hc

/-- Exact signed zero remains exact on the minimum exponent grid. -/
theorem roundUnpacked_zero_correct (format : Format) (mode : RoundingMode) (sign : Sign) :
    RoundsOnGrid mode sign (0 : ℚ) format.minExponent
      (Rounding.roundUnpacked format mode (.zero sign)) := by
  refine ⟨0, ?_, ?_⟩
  · simpa using (exact_mantissaRounds (K := ℚ) mode sign 0)
  · cases sign <;> simp [Rounding.roundUnpacked, value?, dyadic, Sign.apply]

/-- Division's exact quotient is rounded correctly on the core's final grid,
including all quotient residuals, for every rounding direction and sign. -/
theorem divCore_rounding_correct (format : Format) (mode : RoundingMode) (sign : Sign)
    (n d : Nat) (en ed : Int) (hd : 0 < d) :
    let core := divCore format n en d ed
    RoundsOnGrid mode sign ((n : K) * (2 : K) ^ en / ((d : K) * (2 : K) ^ ed))
      (shiftToTargetExponent format core.1 core.2.1 core.2.2).2
      (Rounding.roundWithAccuracy format mode sign core.1 core.2.1 core.2.2) := by
  let core := divCore format n en d ed
  have hc := roundWithAccuracy_correct format mode sign core.1 core.2.1 core.2.2 _
    (divCore_accuracySound (K := K) format n d en ed hd)
  simpa only [core, div_mul_cancel₀ _ (zpow_ne_zero _ (by norm_num : (2 : K) ≠ 0))] using hc

/-- Square root is rounded from its exact real magnitude, not a rational
approximation. The proof covers irrational square roots as well as exact ones. -/
theorem sqrtCore_rounding_correct (format : Format) (mode : RoundingMode)
    (n : Nat) (exponent : Int) :
    let core := sqrtCore format n exponent
    RoundsOnGrid mode .positive (Real.sqrt ((n : ℝ) * (2 : ℝ) ^ exponent))
      (shiftToTargetExponent format core.1 core.2.1 core.2.2).2
      (Rounding.roundWithAccuracy format mode .positive core.1 core.2.1 core.2.2) := by
  let core := sqrtCore format n exponent
  have hc := roundWithAccuracy_correct format mode .positive core.1 core.2.1 core.2.2 _
    (sqrtCore_accuracySound format n exponent)
  simpa only [core, div_mul_cancel₀ _ (zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))] using hc

/-- Correct rounding on the mathematically selected exponent grid survives the
complete encoder/decoder path when the rounded finite exponent is in range.
Both gradual underflow and carries are covered; overflow has its separate
`unpack_packNormalized_overflow` theorem. -/
theorem packRounded_finite_correct (format : Format) (mode : RoundingMode)
    (sign : Sign) (n : Nat) (exponent : Int) (hn : 0 < n)
    (inRange : NoExponentOverflow format
      (Rounding.roundUnpacked format mode (.finite sign n exponent hn))) :
    RoundsOnGrid mode sign ((n : ℚ) * (2 : ℚ) ^ exponent)
      (format.targetExponent (totalExponent n exponent))
      (UnpackedFloat.unpack format
        (Rounding.packRounded format mode (.finite sign n exponent hn))) := by
  rw [unpack_packRounded format mode _ inRange]
  exact roundUnpacked_finite_correct format mode sign n exponent hn

end Silmaril.Numeric.Ieee754.Conformance
