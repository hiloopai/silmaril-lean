module

public import Silmaril.Numeric.Ieee754.MantissaCorrectness

/-!
# Exactness of the carry normalization stage

After significand rounding, the possible carry is normalized by a second
shift. The proofs below establish that this stage discards no nonzero bits:
the rounded significand is at most `2^precision`, and a right shift is needed
only when it equals exactly that power of two.

This verifies the carry stage of `Rounding.roundWithAccuracy`, separately from
the first shift's residual soundness and the final format overflow policy.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Conformance

open Float.Model Float.Model.UnpackedFloat

/-- Shifting the extended representation divides its integer part by a power
of two; residual bits cannot flow back into the integer significand. -/
theorem extendedShift_mantissa (extended : ExtendedMantissa) (amount : Nat) :
    (extended >>> amount).mantissa = extended.mantissa / 2 ^ amount := by
  change (amount.repeat ExtendedMantissa.shiftRightOne extended).mantissa = _
  induction amount with
  | zero => simp [Nat.repeat]
  | succ amount ih =>
    simp [Nat.repeat, ExtendedMantissa.shiftRightOne, ih, Nat.div_div_eq_div_mul, pow_succ]

/-- The first shift always fits the retained integer significand into the
destination precision, regardless of the initial residual classification. -/
theorem shiftToTargetExponent_mantissa_lt (format : Format) (mantissa : Nat)
    (exponent : Int) (accuracy : Accuracy) :
    (shiftToTargetExponent format mantissa exponent accuracy).1.mantissa <
      2 ^ format.mantissaBits := by
  let target := format.targetExponent (totalExponent mantissa exponent)
  let amount := (target - exponent).toNat
  have htarget : (mantissa.log2 : Int) + 1 + exponent - format.mantissaBits ≤ target :=
    le_max_left _ _
  have hamount := Int.self_le_toNat (target - exponent)
  have hbits : mantissa.log2 + 1 ≤ format.mantissaBits + amount := by
    dsimp [amount]
    omega
  have hpow : 2 ^ (mantissa.log2 + 1) ≤ 2 ^ (format.mantissaBits + amount) :=
    Nat.pow_le_pow_right (by decide) hbits
  have hbound : mantissa < 2 ^ format.mantissaBits * 2 ^ amount := by
    rw [← pow_add]
    exact lt_of_lt_of_le (Nat.lt_log2_self) hpow
  change (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy >>> amount).mantissa < _
  rw [extendedShift_mantissa]
  have hm : (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy).mantissa = mantissa :=
    by cases accuracy with
      | exact => rfl
      | inexact order => cases order <;> rfl
  rw [hm]
  exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr hbound

/-- The first shift never leaves the result exponent below the minimum
subnormal exponent of the destination. -/
theorem shiftToTargetExponent_exponent_ge (format : Format) (mantissa : Nat)
    (exponent : Int) (accuracy : Accuracy) :
    format.minExponent ≤ (shiftToTargetExponent format mantissa exponent accuracy).2 := by
  have htarget : format.minExponent ≤
      format.targetExponent (totalExponent mantissa exponent) := le_max_right _ _
  have h := Int.self_le_toNat
    (format.targetExponent (totalExponent mantissa exponent) - exponent)
  change format.minExponent ≤ exponent +
    (format.targetExponent (totalExponent mantissa exponent) - exponent).toNat
  omega

/-- A significand that already fits the precision does not require a carry shift. -/
theorem shiftToTargetExponent_noCarry (format : Format) (mantissa : Nat) (exponent : Int)
    (hm : mantissa < 2 ^ format.mantissaBits) (he : format.minExponent ≤ exponent) :
    shiftToTargetExponent format mantissa exponent .exact =
      (ExtendedMantissa.ofMantissaAndAccuracy mantissa .exact, exponent) := by
  have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
  have hlog : mantissa.log2 < format.mantissaBits := by
    by_cases hz : mantissa = 0
    · simpa [hz] using hp
    · exact (Nat.log2_lt hz).mpr hm
  have ht : format.targetExponent (totalExponent mantissa exponent) ≤ exponent := by
    unfold Format.targetExponent totalExponent
    omega
  have hshift : (format.targetExponent (totalExponent mantissa exponent) - exponent).toNat = 0 :=
    Int.toNat_of_nonpos (by omega)
  simp only [shiftToTargetExponent, shiftToExponent, hshift]
  change (Nat.repeat ExtendedMantissa.shiftRightOne 0 _, exponent + (0 : Int)) = (_, exponent)
  simp [Nat.repeat]

/-- A carry occurs only at the exact power of two. The one discarded bit is zero. -/
theorem shiftToTargetExponent_carry (format : Format) (exponent : Int)
    (he : format.minExponent ≤ exponent) :
    shiftToTargetExponent format (2 ^ format.mantissaBits) exponent .exact =
      (ExtendedMantissa.ofMantissaAndAccuracy (2 ^ (format.mantissaBits - 1)) .exact,
        exponent + 1) := by
  have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
  have hpow := Nat.two_pow_pred_add_two_pow_pred hp
  have hdiv : 2 ^ format.mantissaBits / 2 = 2 ^ (format.mantissaBits - 1) := by omega
  have hmod : 2 ^ format.mantissaBits % 2 = 0 := by omega
  have ht : format.targetExponent (totalExponent (2 ^ format.mantissaBits) exponent) =
      exponent + 1 := by
    unfold Format.targetExponent totalExponent
    rw [Nat.log2_two_pow]
    omega
  simp only [shiftToTargetExponent, ht, shiftToExponent,
    show (exponent + 1 - exponent).toNat = 1 by omega]
  change (ExtendedMantissa.shiftRightOne ⟨2 ^ format.mantissaBits, false, false⟩,
    exponent + 1) = _
  simp [ExtendedMantissa.shiftRightOne, ExtendedMantissa.ofMantissaAndAccuracy, hdiv, hmod]

/-- Under the carry-stage bounds, the second shift retains an exact residual. -/
theorem carryShift_exact (format : Format) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≤ 2 ^ format.mantissaBits) (he : format.minExponent ≤ exponent) :
    (shiftToTargetExponent format mantissa exponent .exact).1.accuracy = .exact := by
  rcases lt_or_eq_of_le hm with hlt | heq
  · rw [shiftToTargetExponent_noCarry format mantissa exponent hlt he]
    rfl
  · rw [heq, shiftToTargetExponent_carry format exponent he]
    rfl

/-- The carry stage preserves the numerical value in any ordered field. -/
theorem carryShift_value {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (format : Format) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≤ 2 ^ format.mantissaBits) (he : format.minExponent ≤ exponent) :
    ((shiftToTargetExponent format mantissa exponent .exact).1.mantissa : K) *
        (2 : K) ^ (shiftToTargetExponent format mantissa exponent .exact).2 =
      (mantissa : K) * (2 : K) ^ exponent := by
  rcases lt_or_eq_of_le hm with hlt | heq
  · rw [shiftToTargetExponent_noCarry format mantissa exponent hlt he]
    rfl
  · rw [heq, shiftToTargetExponent_carry format exponent he]
    simp only [ExtendedMantissa.ofMantissaAndAccuracy, Nat.cast_pow, Nat.cast_ofNat]
    rw [zpow_add₀ (by norm_num : (2 : K) ≠ 0)]
    simp only [zpow_one]
    have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
    have hpower : (2 : K) ^ (format.mantissaBits - 1) * 2 = 2 ^ format.mantissaBits := by
      rw [← pow_succ, Nat.sub_add_cancel hp]
    calc
      (2 : K) ^ (format.mantissaBits - 1) * (2 ^ exponent * 2) =
          (2 ^ (format.mantissaBits - 1) * 2) * 2 ^ exponent := by rw [mul_comm (2 ^ exponent) 2, ← mul_assoc]
      _ = 2 ^ format.mantissaBits * 2 ^ exponent := by rw [hpower]

/-- The value produced by significand rounding is bounded by the sole possible
carry, `2^precision`, for every rounding direction and sign. -/
theorem roundedShift_mantissa_le (format : Format) (mode : RoundingMode) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (accuracy : Accuracy) :
    Rounding.roundMantissa mode sign
        (shiftToTargetExponent format mantissa exponent accuracy).1.mantissa
        (shiftToTargetExponent format mantissa exponent accuracy).1.accuracy ≤
      2 ^ format.mantissaBits := by
  have hlt := shiftToTargetExponent_mantissa_lt format mantissa exponent accuracy
  rcases roundMantissa_bracket mode sign
    (shiftToTargetExponent format mantissa exponent accuracy).1.mantissa
    (shiftToTargetExponent format mantissa exponent accuracy).1.accuracy with heq | heq <;> omega

/-- The actual second shift in `roundWithAccuracy` is exact, with no hypotheses
on the input significand, initial exponent, residual class, sign, or mode. -/
theorem roundWithAccuracy_carry_exact (format : Format) (mode : RoundingMode) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (accuracy : Accuracy) :
    let shifted := shiftToTargetExponent format mantissa exponent accuracy
    let rounded := Rounding.roundMantissa mode sign shifted.1.mantissa shifted.1.accuracy
    (shiftToTargetExponent format rounded shifted.2 .exact).1.accuracy = .exact := by
  apply carryShift_exact
  · exact roundedShift_mantissa_le format mode sign mantissa exponent accuracy
  · exact shiftToTargetExponent_exponent_ge format mantissa exponent accuracy

/-- Numerical preservation for the actual carry stage, without preconditions
on the first shift's input. -/
theorem roundWithAccuracy_carry_value
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (format : Format) (mode : RoundingMode) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (accuracy : Accuracy) :
    let shifted := shiftToTargetExponent format mantissa exponent accuracy
    let rounded := Rounding.roundMantissa mode sign shifted.1.mantissa shifted.1.accuracy
    let carried := shiftToTargetExponent format rounded shifted.2 .exact
    (carried.1.mantissa : K) * (2 : K) ^ carried.2 =
      (rounded : K) * (2 : K) ^ shifted.2 := by
  apply carryShift_value
  · exact roundedShift_mantissa_le format mode sign mantissa exponent accuracy
  · exact shiftToTargetExponent_exponent_ge format mantissa exponent accuracy

/-- With the documented input precondition, the first shift reaches precisely
the exponent selected from the input's magnitude. -/
theorem shiftToTargetExponent_exponent_eq (format : Format) (mantissa : Nat)
    (exponent : Int) (accuracy : Accuracy)
    (he : exponent ≤ format.targetExponent (totalExponent mantissa exponent)) :
    (shiftToTargetExponent format mantissa exponent accuracy).2 =
      format.targetExponent (totalExponent mantissa exponent) := by
  change exponent + (format.targetExponent (totalExponent mantissa exponent) - exponent).toNat = _
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- Away from the subnormal exponent, the first shift retains the leading
implicit bit. Its significand therefore has exactly the destination precision. -/
theorem shiftToTargetExponent_mantissa_ge (format : Format) (mantissa : Nat)
    (exponent : Int) (accuracy : Accuracy)
    (he : exponent ≤ format.targetExponent (totalExponent mantissa exponent))
    (hnormal : format.minExponent < format.targetExponent (totalExponent mantissa exponent)) :
    2 ^ (format.mantissaBits - 1) ≤
      (shiftToTargetExponent format mantissa exponent accuracy).1.mantissa := by
  let target := format.targetExponent (totalExponent mantissa exponent)
  let amount := (target - exponent).toNat
  have ht : target = (mantissa.log2 : Int) + 1 + exponent - format.mantissaBits := by
    dsimp [target, Format.targetExponent, totalExponent] at *
    omega
  have hp : 2 ≤ format.mantissaBits := by
    have := format.hm
    simp only [Format.mantissaBits]
    omega
  have hbits : format.mantissaBits ≤ mantissa.log2 + 1 := by
    change exponent ≤ target at he
    rw [ht] at he
    omega
  have hnonzero : mantissa ≠ 0 := by
    intro hz
    simp only [hz, Nat.log2_zero] at hbits
    omega
  have hamount : format.mantissaBits - 1 + amount = mantissa.log2 := by
    dsimp [amount]
    rw [ht]
    omega
  change _ ≤ (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy >>> amount).mantissa
  rw [extendedShift_mantissa]
  have hm : (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy).mantissa = mantissa := by
    cases accuracy with
    | exact => rfl
    | inexact order => cases order <;> rfl
  rw [hm, Nat.le_div_iff_mul_le (Nat.pow_pos (by decide)), ← pow_add, hamount]
  exact Nat.log2_self_le hnonzero

/-- Numerical bounds characterize a canonical exponent, including subnormals.
At the minimum exponent the leading bit may be absent; at larger exponents it
must be present. -/
theorem targetExponent_eq_of_bounds (format : Format) (mantissa : Nat) (exponent : Int)
    (he : format.minExponent ≤ exponent) (hu : mantissa < 2 ^ format.mantissaBits)
    (hl : exponent = format.minExponent ∨ 2 ^ (format.mantissaBits - 1) ≤ mantissa) :
    format.targetExponent (totalExponent mantissa exponent) = exponent := by
  have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
  have hlog : mantissa.log2 < format.mantissaBits := by
    by_cases hz : mantissa = 0
    · simpa [hz] using hp
    · exact (Nat.log2_lt hz).mpr hu
  rcases hl with hmin | hl
  · unfold Format.targetExponent totalExponent
    omega
  · have hnonzero : mantissa ≠ 0 := by
      have hpow : 0 < 2 ^ (format.mantissaBits - 1) := Nat.pow_pos (by decide)
      omega
    have hlogeq : mantissa.log2 = format.mantissaBits - 1 := by
      apply (Nat.log2_eq_iff hnonzero).mpr
      exact ⟨hl, by simpa [Nat.sub_add_cancel hp] using hu⟩
    unfold Format.targetExponent totalExponent
    rw [hlogeq]
    omega

/-- Canonical precision bounds survive the exact carry normalization. -/
theorem carryShift_normalized (format : Format) (mantissa : Nat) (exponent : Int)
    (he : format.minExponent ≤ exponent) (hu : mantissa ≤ 2 ^ format.mantissaBits)
    (hl : exponent = format.minExponent ∨ 2 ^ (format.mantissaBits - 1) ≤ mantissa) :
    let carried := shiftToTargetExponent format mantissa exponent .exact
    format.targetExponent (totalExponent carried.1.mantissa carried.2) = carried.2 := by
  rcases lt_or_eq_of_le hu with hlt | heq
  · rw [shiftToTargetExponent_noCarry format mantissa exponent hlt he]
    exact targetExponent_eq_of_bounds format mantissa exponent he hlt hl
  · rw [heq, shiftToTargetExponent_carry format exponent he]
    apply targetExponent_eq_of_bounds
    · omega
    · have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
      exact Nat.pow_lt_pow_right (by decide) (by omega)
    · exact Or.inr (Nat.le_refl _)

/-- Canonical exponent equality at the actual carry-stage output, assuming
that the input exponent was low enough for the first shift. -/
theorem roundWithAccuracy_carry_normalized (format : Format) (mode : RoundingMode) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (accuracy : Accuracy)
    (he : exponent ≤ format.targetExponent (totalExponent mantissa exponent)) :
    let shifted := shiftToTargetExponent format mantissa exponent accuracy
    let rounded := Rounding.roundMantissa mode sign shifted.1.mantissa shifted.1.accuracy
    let carried := shiftToTargetExponent format rounded shifted.2 .exact
    format.targetExponent (totalExponent carried.1.mantissa carried.2) = carried.2 := by
  apply carryShift_normalized
  · exact shiftToTargetExponent_exponent_ge format mantissa exponent accuracy
  · exact roundedShift_mantissa_le format mode sign mantissa exponent accuracy
  · rw [shiftToTargetExponent_exponent_eq format mantissa exponent accuracy he]
    by_cases hmin : format.targetExponent (totalExponent mantissa exponent) = format.minExponent
    · exact Or.inl hmin
    · right
      have hnormal : format.minExponent < format.targetExponent (totalExponent mantissa exponent) := by
        have : format.minExponent ≤ format.targetExponent (totalExponent mantissa exponent) :=
          le_max_right _ _
        omega
      have hbound := shiftToTargetExponent_mantissa_ge format mantissa exponent accuracy he hnormal
      rcases roundMantissa_bracket mode sign
        (shiftToTargetExponent format mantissa exponent accuracy).1.mantissa
        (shiftToTargetExponent format mantissa exponent accuracy).1.accuracy with heq | heq <;> omega

/-- Shifting a nonzero integer significand left increases its leading-bit
position by exactly the shift amount. -/
theorem log2_shiftLeft (mantissa amount : Nat) (hm : mantissa ≠ 0) :
    (mantissa <<< amount).log2 = mantissa.log2 + amount := by
  rw [Nat.shiftLeft_eq]
  have hp : 0 < 2 ^ amount := Nat.pow_pos (by decide)
  apply (Nat.log2_eq_iff (Nat.ne_of_gt (Nat.mul_pos (Nat.pos_of_ne_zero hm) hp))).mpr
  constructor
  · rw [pow_add]
    exact Nat.mul_le_mul_right _ (Nat.log2_self_le hm)
  · rw [show mantissa.log2 + amount + 1 = (mantissa.log2 + 1) + amount by omega, pow_add]
    exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self hp

/-- Exact exponent alignment preserves the leading-bit position of a finite
nonzero value, not only its numerical denotation. -/
theorem decreaseExponent_totalExponent (mantissa : Nat) (exponent target : Int)
    (hm : mantissa ≠ 0) :
    totalExponent (decreaseExponent mantissa exponent target).1
        (decreaseExponent mantissa exponent target).2 =
      totalExponent mantissa exponent := by
  simp only [decreaseExponent, totalExponent, log2_shiftLeft _ _ hm, Nat.cast_add]
  omega

/-- The preprocessing used by `roundUnpacked` establishes exactly the exponent
precondition required by `roundWithAccuracy`. -/
theorem decreaseExponent_ready (format : Format) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0) :
    let aligned := decreaseExponent mantissa exponent
      (format.targetExponent (totalExponent mantissa exponent))
    aligned.2 ≤ format.targetExponent (totalExponent aligned.1 aligned.2) := by
  dsimp only
  rw [decreaseExponent_totalExponent mantissa exponent _ hm]
  change exponent - (exponent - format.targetExponent (totalExponent mantissa exponent)).toNat ≤ _
  have := Int.self_le_toNat (exponent - format.targetExponent (totalExponent mantissa exponent))
  omega

/-- The canonical exponent invariant required by `UnpackedFloat.pack`.
This allows exponents above the format range: overflow is handled by packing. -/
def ExponentNormalized (format : Format) : UnpackedFloat → Prop
  | .finite _ mantissa exponent _ =>
    format.targetExponent (totalExponent mantissa exponent) = exponent
  | _ => True

/-- A positive significand with a canonical exponent satisfies the numerical
precision bounds used by the normal/subnormal encoding branches. -/
theorem ExponentNormalized.finite_bounds (format : Format) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (hm : 0 < mantissa)
    (normalized : ExponentNormalized format (.finite sign mantissa exponent hm)) :
    format.minExponent ≤ exponent ∧ mantissa < 2 ^ format.mantissaBits ∧
      (exponent = format.minExponent ∨ 2 ^ (format.mantissaBits - 1) ≤ mantissa) := by
  have hnorm : max ((mantissa.log2 : Int) + 1 + exponent - format.mantissaBits)
      format.minExponent = exponent := normalized
  have hbits : mantissa.log2 < format.mantissaBits := by omega
  refine ⟨by omega, (Nat.log2_lt (Nat.ne_of_gt hm)).mp hbits, ?_⟩
  by_cases he : exponent = format.minExponent
  · exact Or.inl he
  · right
    apply (Nat.le_log2 (Nat.ne_of_gt hm)).mp
    omega

/-- Given its documented input precondition, `roundWithAccuracy` returns a
canonical exponent suitable for packing. -/
theorem roundWithAccuracy_normalized (format : Format) (mode : RoundingMode) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (accuracy : Accuracy)
    (he : exponent ≤ format.targetExponent (totalExponent mantissa exponent)) :
    ExponentNormalized format (Rounding.roundWithAccuracy format mode sign mantissa exponent accuracy) := by
  have hnorm := roundWithAccuracy_carry_normalized format mode sign mantissa exponent accuracy he
  unfold Rounding.roundWithAccuracy
  generalize hs : shiftToTargetExponent format mantissa exponent accuracy = shifted at *
  rcases shifted with ⟨extended, nextExponent⟩
  dsimp only at *
  generalize hc : shiftToTargetExponent format
    (Rounding.roundMantissa mode sign extended.mantissa extended.accuracy)
    nextExponent .exact = carried at *
  rcases carried with ⟨finalExtended, finalExponent⟩
  dsimp only at *
  split
  · trivial
  · exact hnorm

/-- Exact alignment followed by rounding always produces a canonical exponent,
for every input class and every rounding direction. -/
theorem roundUnpacked_normalized (format : Format) (mode : RoundingMode) (value : UnpackedFloat) :
    ExponentNormalized format (Rounding.roundUnpacked format mode value) := by
  cases value with
  | notANumber | infinity _ | zero _ => trivial
  | finite sign mantissa exponent hm =>
    apply roundWithAccuracy_normalized
    exact decreaseExponent_ready format mantissa exponent (Nat.ne_of_gt hm)

end Silmaril.Numeric.Ieee754.Conformance
