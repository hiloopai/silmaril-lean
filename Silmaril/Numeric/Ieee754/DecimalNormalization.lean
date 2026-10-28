module

public import Silmaril.Numeric.Ieee754.DecimalProperties
import Mathlib.Tactic.NormNum

/-! # Decimal normalization and significant digits

The formatter's existing fuel bound removes every trailing decimal zero.
Normalization preserves the rational value and leaves positive coefficients
with a nonzero final digit. The coefficient bound includes the adjacent-decade
case `10^p`, which becomes shorter after its first trimming step.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

/-- The same normalization used by the formatter's layout function. -/
def Number.normalize (number : Number) : Number :=
  trim (toString number.coefficient).length number

/-- A positive decimal coefficient without redundant trailing zeros. -/
def Number.Normalized (number : Number) : Prop :=
  0 < number.coefficient ∧ number.coefficient % 10 ≠ 0

/-- Significant digits after removing redundant trailing zeros. -/
def Number.significantDigits (number : Number) : Nat :=
  (toString number.normalize.coefficient).length

theorem trim_coefficient_le (fuel : Nat) (number : Number) :
    (trim fuel number).coefficient ≤ number.coefficient := by
  induction fuel generalizing number with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [trim]
    split
    · exact (ih _).trans (Nat.div_le_self _ _)
    · exact le_rfl

theorem trim_positive (fuel : Nat) (number : Number) (positive : 0 < number.coefficient) :
    0 < (trim fuel number).coefficient := by
  induction fuel generalizing number with
  | zero => exact positive
  | succ fuel ih =>
    simp only [trim]
    split
    next condition =>
      have divisible : number.coefficient % 10 = 0 := by
        have both : number.coefficient ≠ 0 ∧ number.coefficient % 10 = 0 := by simpa using condition
        exact both.2
      apply ih
      dsimp only
      omega
    next _ => exact positive

/-- Fewer than `10^fuel` ensures that the fuel cannot run out before a positive
coefficient reaches its last nonzero decimal digit. -/
theorem trim_normalized (fuel : Nat) (number : Number) (positive : 0 < number.coefficient)
    (bound : number.coefficient < 10 ^ fuel) : (trim fuel number).Normalized := by
  induction fuel generalizing number with
  | zero => simp only [pow_zero] at bound; omega
  | succ fuel ih =>
    simp only [trim]
    split
    next condition =>
      have divisible : number.coefficient % 10 = 0 := by
        have both : number.coefficient ≠ 0 ∧ number.coefficient % 10 = 0 := by simpa using condition
        exact both.2
      apply ih
      · dsimp only; omega
      · dsimp only
        rw [pow_succ] at bound
        omega
    next condition =>
      refine ⟨positive, ?_⟩
      have failed : ¬ (number.coefficient ≠ 0 ∧ number.coefficient % 10 = 0) := by simpa using condition
      exact fun divisible => failed ⟨by omega, divisible⟩

@[simp] theorem Number.normalize_value (number : Number) : number.normalize.value = number.value :=
  trim_value _ _

theorem Number.normalize_positive (number : Number) (positive : 0 < number.coefficient) :
    0 < number.normalize.coefficient := trim_positive _ _ positive

theorem Number.normalize_normalized (number : Number) (positive : 0 < number.coefficient) :
    number.normalize.Normalized := by
  apply trim_normalized _ _ positive
  exact (Nat.length_repr_le_iff Nat.length_repr_pos).mp (Nat.le_refl _)

theorem trim_of_normalized (fuel : Nat) (number : Number) (normalized : number.Normalized) :
    trim fuel number = number := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [trim, normalized.2]

@[simp] theorem Number.normalize_of_normalized (number : Number) (normalized : number.Normalized) :
    number.normalize = number := trim_of_normalized _ _ normalized

@[simp] theorem Number.normalize_idempotent (number : Number) (positive : 0 < number.coefficient) :
    number.normalize.normalize = number.normalize :=
  number.normalize.normalize_of_normalized (number.normalize_normalized positive)

/-- Trimming a positive-fuel coefficient bounded by `10^p` makes that bound
strict. This handles the extra digit at the next decade's boundary. -/
theorem trim_coefficient_lt_power (fuel : Nat) (fuelPositive : 0 < fuel) (number : Number)
    (digits : Nat) (digitsPositive : 0 < digits) (bound : number.coefficient ≤ 10 ^ digits) :
    (trim fuel number).coefficient < 10 ^ digits := by
  by_cases strict : number.coefficient < 10 ^ digits
  · exact (trim_coefficient_le fuel number).trans_lt strict
  · have equal : number.coefficient = 10 ^ digits := by omega
    have coefficientPositive : 0 < number.coefficient := by rw [equal]; positivity
    have divisible : number.coefficient % 10 = 0 := by
      rw [equal]
      obtain ⟨digits, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : digits ≠ 0)
      simp [pow_succ]
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    simp only [trim]
    have condition : (number.coefficient != 0 && number.coefficient % 10 == 0) = true := by
      simp [ne_of_gt coefficientPositive, divisible]
    rw [ite_eq_left condition]
    exact (trim_coefficient_le fuel _).trans_lt
      (by simpa only [equal] using Nat.div_lt_self coefficientPositive (by decide : 1 < 10))

/-- Successful `p`-digit grid coefficients use at most `p` significant digits,
even when their untrimmed coefficient is the `(p+1)`-digit number `10^p`. -/
theorem Number.significantDigits_le (number : Number) (digits : Nat) (digitsPositive : 0 < digits)
    (bound : number.coefficient ≤ 10 ^ digits) : number.significantDigits ≤ digits := by
  apply (Nat.length_repr_le_iff digitsPositive).mpr
  exact trim_coefficient_lt_power _ Nat.length_repr_pos number digits digitsPositive bound

end Silmaril.Numeric.Ieee754.Decimal
