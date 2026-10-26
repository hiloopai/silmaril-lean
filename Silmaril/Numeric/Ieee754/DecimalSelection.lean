module

public import Silmaril.Numeric.Ieee754.DecimalShortest
import Mathlib.Tactic.Linarith

/-! # Nearest-value preference in decimal candidate selection -/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

/-- The implementation expressed using the shared adjacent-grid definitions. -/
theorem candidate_formula (interval : Interval) (value : ℚ) (digits : Nat) :
    candidate interval value digits =
      let a := lowerNeighbor value digits
      let b := upperNeighbor value digits
      if (a.coefficient != 0 && interval.accepts a.value) && interval.accepts b.value then
        if value - a.value < b.value - value then some a
        else if b.value - value < value - a.value then some b
        else if a.coefficient % 2 == 0 then some a else some b
      else if a.coefficient != 0 && interval.accepts a.value then some a
      else if interval.accepts b.value then some b else none := by
  rfl

/-- Among accepted tested neighbors, the candidate chooses minimum distance
and the even coefficient for a genuine equal-distance tie. -/
theorem candidate_neighbor_preference (interval : Interval) (value : ℚ) (positive : 0 < value)
    (digits : Nat) {result : Number} (selected : candidate interval value digits = some result)
    (number : Number) (neighbor : number = lowerNeighbor value digits ∨ number = upperNeighbor value digits)
    (numberPositive : 0 < number.coefficient) (accepted : interval.accepts number.value = true) :
    |value - result.value| ≤ |value - number.value| ∧
      (|value - result.value| = |value - number.value| → result.coefficient % 2 = 0 ∨ result = number) := by
  let a := lowerNeighbor value digits
  let b := upperNeighbor value digits
  have aBelow : a.value ≤ value := (neighbor_brackets value positive.le digits).1
  have bAbove : value ≤ b.value := (neighbor_brackets value positive.le digits).2.le
  have aAbs : |value - a.value| = value - a.value := abs_of_nonneg (sub_nonneg.mpr aBelow)
  have bAbs : |value - b.value| = b.value - value := by
    rw [abs_of_nonpos (sub_nonpos.mpr bAbove)]
    ring
  have bCoefficient : b.coefficient = a.coefficient + 1 := rfl
  rw [candidate_formula] at selected
  change (if (a.coefficient != 0 && interval.accepts a.value) && interval.accepts b.value then
      if value - a.value < b.value - value then some a
      else if b.value - value < value - a.value then some b
      else if a.coefficient % 2 == 0 then some a else some b
    else if a.coefficient != 0 && interval.accepts a.value then some a
    else if interval.accepts b.value then some b else none) = some result at selected
  change number = a ∨ number = b at neighbor
  rcases neighbor with rfl | rfl <;>
    split_ifs at selected <;>
    simp_all only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, Option.some.injEq, reduceCtorEq]
  all_goals subst result
  all_goals try simp_all
  all_goals first | omega | (intro equal; linarith) | constructor <;> first | linarith | (intro equal; first | omega | linarith)

/-- The selected decimal minimizes distance over every accepted positive
coefficient on its grid, rather than just the two explicitly tested points. -/
theorem candidate_nearest_on_grid (interval : Interval) (value : ℚ) (positive : 0 < value)
    (center : interval.accepts value = true) (digits : Nat) {result : Number}
    (selected : candidate interval value digits = some result) (coefficient : Nat)
    (coefficientPositive : 0 < coefficient)
    (accepted : interval.accepts ((coefficient : ℚ) * power (decade value - (digits : Int) + 1)) = true) :
    |value - result.value| ≤ |value - (coefficient : ℚ) * power (decade value - (digits : Int) + 1)| := by
  let a := lowerNeighbor value digits
  let b := upperNeighbor value digits
  let delta := power (decade value - (digits : Int) + 1)
  have deltaPositive : 0 < delta := power_positive _
  have aValue : a.value = (a.coefficient : ℚ) * delta := by
    simp only [a, delta, lowerNeighbor, Number.value]
  have bValue : b.value = ((a.coefficient : ℚ) + 1) * delta := by
    simp only [a, b, delta, upperNeighbor, lowerNeighbor, Number.value, Nat.cast_add, Nat.cast_one]
  have aBelow : a.value ≤ value := (neighbor_brackets value positive.le digits).1
  have bAbove : value ≤ b.value := (neighbor_brackets value positive.le digits).2.le
  by_cases below : coefficient ≤ a.coefficient
  · have pointBelow : (coefficient : ℚ) * delta ≤ a.value := by
      rw [aValue]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast below) deltaPositive.le
    have aAccepted := interval.accepts_between _ value a.value accepted center pointBelow aBelow
    have preferred := (candidate_neighbor_preference interval value positive digits selected a
      (Or.inl rfl) (by omega) aAccepted).1
    apply preferred.trans
    rw [abs_of_nonneg (sub_nonneg.mpr aBelow),
      abs_of_nonneg (sub_nonneg.mpr (pointBelow.trans aBelow))]
    linarith
  · have pointAbove : b.value ≤ (coefficient : ℚ) * delta := by
      rw [bValue]
      apply mul_le_mul_of_nonneg_right _ deltaPositive.le
      have ordered : a.coefficient + 1 ≤ coefficient := by omega
      exact_mod_cast ordered
    have bAccepted := interval.accepts_between value _ b.value center accepted bAbove pointAbove
    have preferred := (candidate_neighbor_preference interval value positive digits selected b
      (Or.inr rfl) (by simp only [b, upperNeighbor]; omega) bAccepted).1
    apply preferred.trans
    rw [abs_of_nonpos (sub_nonpos.mpr bAbove),
      abs_of_nonpos (sub_nonpos.mpr (bAbove.trans pointAbove))]
    linarith

/-- A decimal whose exponent is at least the grid exponent is a positive
integer coefficient on that grid. -/
theorem Number.exists_grid_coefficient (number : Number) (positive : 0 < number.coefficient)
    (exponent : Int) (ordered : exponent ≤ number.exponent) :
    ∃ coefficient : Nat, 0 < coefficient ∧ (coefficient : ℚ) * power exponent = number.value := by
  let shift := (number.exponent - exponent).toNat
  have shiftEq : exponent + (shift : Int) = number.exponent := by
    dsimp only [shift]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr ordered)]
    omega
  refine ⟨number.coefficient * 10 ^ shift, Nat.mul_pos positive (Nat.pow_pos (by decide)), ?_⟩
  simp only [Number.value, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have exponentPower : power number.exponent = power exponent * power (shift : Int) :=
    (congrArg power shiftEq.symm).trans (power_add exponent shift)
  rw [exponentPower]
  simp only [power, zpow_natCast]
  ring

/-- The candidate is nearest among all accepted decimals with at most its
search precision, including shorter representations across a decade boundary. -/
theorem candidate_nearest_number (interval : Interval) (value : ℚ) (positive : 0 < value)
    (center : interval.accepts value = true) (digits : Nat) (digitsPositive : 0 < digits)
    {result : Number} (selected : candidate interval value digits = some result)
    (number : Number) (numberPositive : 0 < number.coefficient)
    (lengthBound : (toString number.coefficient).length ≤ digits)
    (accepted : interval.accepts number.value = true) :
    |value - result.value| ≤ |value - number.value| := by
  let exponent := decade value - (digits : Int) + 1
  by_cases higher : exponent ≤ number.exponent
  · obtain ⟨coefficient, coefficientPositive, onGrid⟩ :=
      number.exists_grid_coefficient numberPositive exponent higher
    have gridAccepted : interval.accepts ((coefficient : ℚ) * power exponent) = true := by
      rw [onGrid]; exact accepted
    have preferred := candidate_nearest_on_grid interval value positive center digits selected
      coefficient coefficientPositive gridAccepted
    change |value - result.value| ≤ |value - (coefficient : ℚ) * power exponent| at preferred
    rwa [onGrid] at preferred
  · have coefficientBound : (number.coefficient : ℚ) < power digits := by
      have bound : number.coefficient < 10 ^ digits :=
        (Nat.length_repr_le_iff digitsPositive).mp lengthBound
      simpa only [power, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using
        (show (number.coefficient : ℚ) < (10 ^ digits : Nat) by exact_mod_cast bound)
    have lowerExponent : number.exponent ≤ exponent - 1 := by omega
    have numberBelow : number.value < power (decade value) := by
      have less := mul_lt_mul_of_pos_right coefficientBound (power_positive number.exponent)
      have ordered := mul_le_mul_of_nonneg_left (power_mono lowerExponent) (power_positive digits).le
      have identity : power digits * power (exponent - 1) = power (decade value) := by
        rw [← power_add]
        congr 1
        dsimp only [exponent]
        omega
      change number.value < power digits * power number.exponent at less
      exact less.trans_le (by rw [← identity]; exact ordered)
    have boundaryBelow := (decade_bounds value positive).1
    have boundaryAccepted := interval.accepts_between number.value value (power (decade value))
      accepted center numberBelow.le boundaryBelow
    let boundary : Number := ⟨1, decade value⟩
    have boundaryValue : boundary.value = power (decade value) := by
      simp only [boundary, Number.value, Nat.cast_one, one_mul]
    obtain ⟨coefficient, coefficientPositive, onGrid⟩ :=
      boundary.exists_grid_coefficient (by change 0 < 1; decide) exponent (by dsimp only [boundary, exponent]; omega)
    have gridAccepted : interval.accepts ((coefficient : ℚ) * power exponent) = true := by
      rw [onGrid, boundaryValue]; exact boundaryAccepted
    have preferred := candidate_nearest_on_grid interval value positive center digits selected
      coefficient coefficientPositive gridAccepted
    change |value - result.value| ≤ |value - (coefficient : ℚ) * power exponent| at preferred
    rw [onGrid, boundaryValue] at preferred
    apply preferred.trans
    rw [abs_of_nonneg (sub_nonneg.mpr boundaryBelow),
      abs_of_nonneg (sub_nonneg.mpr (numberBelow.le.trans boundaryBelow))]
    linarith

/-- Among all accepted shortest decimal representations, the formatter chooses
a nearest rational value. Competitors may include redundant trailing zeros. -/
theorem shortest_nearest_minimal (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) (number : Number)
    (numberPositive : 0 < number.coefficient)
    (lengthBound : number.significantDigits ≤ (shortest bits).significantDigits)
    (accepted : (roundingInterval bits).accepts number.value = true) :
    |rational bits - (shortest bits).value| ≤ |rational bits - number.value| := by
  obtain ⟨digits, lower, _, chosen, equal, _⟩ := shortest_global_minimum bits positive finite
  have preferred := candidate_nearest_number (roundingInterval bits) (rational bits)
    (rational_pos_of_positive_finite bits positive finite) (rational_accepted bits positive finite)
    digits lower chosen number.normalize (number.normalize_positive numberPositive)
    (by rw [equal] at lengthBound; exact lengthBound)
    (by rw [number.normalize_value]; exact accepted)
  rwa [number.normalize_value] at preferred

end Silmaril.Numeric.Ieee754.Decimal
