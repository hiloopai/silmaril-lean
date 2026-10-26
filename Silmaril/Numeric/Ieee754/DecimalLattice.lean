module

public import Silmaril.Numeric.Ieee754.DecimalBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Completeness of the adjacent decimal lattice search

Convexity connects the two tested neighboring coefficients to every accepted
point on the same decimal grid. A shorter representation in a lower decade
forces a one-digit candidate, so no same-decade assumption is needed.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

theorem power_add (left right : Int) : power (left + right) = power left * power right :=
  zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0) left right

theorem power_mono {left right : Int} (ordered : left ≤ right) : power left ≤ power right :=
  zpow_le_zpow_right₀ (by norm_num) ordered

theorem grid_power (value : ℚ) (digits : Nat) :
    power (decade value - (digits : Int) + 1) * (10 : ℚ) ^ digits = power (decade value + 1) := by
  rw [← zpow_natCast (10 : ℚ) digits]
  change power (decade value - (digits : Int) + 1) * power digits = _
  rw [← power_add]
  congr 1
  omega

/-- The interval predicate is convex, with either strict or inclusive ends. -/
theorem Interval.accepts_between (interval : Interval) (left right value : ℚ)
    (leftAccepted : interval.accepts left = true) (rightAccepted : interval.accepts right = true)
    (lower : left ≤ value) (upper : value ≤ right) : interval.accepts value = true := by
  cases ends : interval.includeEnds <;>
    simp only [Interval.accepts, ends, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at *
  · exact ⟨lt_of_lt_of_le leftAccepted.1 lower, lt_of_le_of_lt upper rightAccepted.2⟩
  · exact ⟨leftAccepted.1.trans lower, upper.trans rightAccepted.2⟩

/-- Any accepted positive grid coefficient yields an accepted tested neighbor
because the exact input itself belongs to the interval. -/
theorem candidate_complete_on_grid (interval : Interval) (value : ℚ) (positive : 0 < value)
    (center : interval.accepts value = true) (digits coefficient : Nat)
    (coefficientPositive : 0 < coefficient)
    (accepted : interval.accepts ((coefficient : ℚ) * power (decade value - (digits : Int) + 1)) = true) :
    ∃ number, candidate interval value digits = some number := by
  let a := lowerNeighbor value digits
  let b := upperNeighbor value digits
  let delta := power (decade value - (digits : Int) + 1)
  have deltaPositive : 0 < delta := power_positive _
  have aValue : a.value = (a.coefficient : ℚ) * delta := by
    simp only [a, delta, lowerNeighbor, Number.value]
  have bValue : b.value = ((a.coefficient : ℚ) + 1) * delta := by
    simp only [a, b, delta, upperNeighbor, lowerNeighbor, Number.value, Nat.cast_add, Nat.cast_one]
  obtain ⟨aBelow, bAbove⟩ := neighbor_brackets value positive.le digits
  change a.value ≤ value at aBelow
  change value < b.value at bAbove
  by_cases below : (coefficient : ℚ) * delta ≤ value
  · have coefficientLess : (coefficient : ℚ) < a.coefficient + 1 := by
      apply (mul_lt_mul_iff_left₀ deltaPositive).mp
      rw [← bValue]
      exact below.trans_lt bAbove
    have coefficientLe : coefficient ≤ a.coefficient := by
      have strict : coefficient < a.coefficient + 1 := by exact_mod_cast coefficientLess
      omega
    have pointBelow : (coefficient : ℚ) * delta ≤ a.value := by
      rw [aValue]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast coefficientLe) deltaPositive.le
    apply candidate_exists_of_lower interval value digits (by omega : 0 < a.coefficient)
    exact interval.accepts_between _ value a.value accepted center pointBelow aBelow
  · have coefficientLess : (a.coefficient : ℚ) < coefficient := by
      apply (mul_lt_mul_iff_left₀ deltaPositive).mp
      rw [← aValue]
      exact aBelow.trans_lt (lt_of_not_ge below)
    have coefficientLe : a.coefficient + 1 ≤ coefficient := by exact_mod_cast coefficientLess
    have pointAbove : b.value ≤ (coefficient : ℚ) * delta := by
      rw [bValue]
      apply mul_le_mul_of_nonneg_right _ deltaPositive.le
      exact_mod_cast coefficientLe
    apply candidate_exists_of_upper interval value digits
    exact interval.accepts_between value _ b.value center accepted bAbove.le pointAbove

/-- Successful candidates are exactly one of the two tested adjacent points. -/
theorem candidate_neighbor (interval : Interval) (value : ℚ) (digits : Nat) {number : Number}
    (selected : candidate interval value digits = some number) :
    number = lowerNeighbor value digits ∨ number = upperNeighbor value digits := by
  unfold candidate upperNeighbor lowerNeighbor at *
  dsimp only at *
  split_ifs at selected <;> simp_all

/-- At precision `p`, a selected coefficient is at most `10^p`. Equality is
the adjacent-decade boundary and will normalize to fewer significant digits. -/
theorem candidate_coefficient_bound (interval : Interval) (value : ℚ) (positive : 0 < value)
    (digits : Nat) {number : Number} (selected : candidate interval value digits = some number) :
    number.coefficient ≤ 10 ^ digits := by
  let a := lowerNeighbor value digits
  let delta := power (decade value - (digits : Int) + 1)
  have deltaPositive : 0 < delta := power_positive _
  have aValue : a.value = (a.coefficient : ℚ) * delta := by
    simp only [a, delta, lowerNeighbor, Number.value]
  have bound : value < ((10 ^ digits : Nat) : ℚ) * delta := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [mul_comm, grid_power]
    exact (decade_bounds value positive).2
  have aBelow := (neighbor_brackets value positive.le digits).1
  have aLess : (a.coefficient : ℚ) < (10 ^ digits : Nat) := by
    apply (mul_lt_mul_iff_left₀ deltaPositive).mp
    rw [← aValue]
    exact aBelow.trans_lt bound
  have aNat : a.coefficient < 10 ^ digits := by exact_mod_cast aLess
  rcases candidate_neighbor interval value digits selected with rfl | rfl
  · exact aNat.le
  · change a.coefficient + 1 ≤ 10 ^ digits
    omega

/-- Every accepted positive decimal with `p` coefficient digits forces a
successful search at some precision at most `p`. Lower-decade crossings force
precision one, while all remaining cases lie on the ordinary `p`-digit grid. -/
theorem candidate_complete_for_number (interval : Interval) (value : ℚ) (positive : 0 < value)
    (center : interval.accepts value = true) (number : Number) (nonzero : 0 < number.coefficient)
    (accepted : interval.accepts number.value = true) :
    ∃ digits, 1 ≤ digits ∧ digits ≤ (toString number.coefficient).length ∧
      ∃ result, candidate interval value digits = some result := by
  let digits := (toString number.coefficient).length
  let exponent := decade value - (digits : Int) + 1
  have digitsPositive : 1 ≤ digits := Nat.length_repr_pos
  by_cases higher : exponent ≤ number.exponent
  · let shift := (number.exponent - exponent).toNat
    have shiftEq : exponent + (shift : Int) = number.exponent := by
      dsimp only [shift]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr higher)]
      omega
    have onGrid : ((number.coefficient * 10 ^ shift : Nat) : ℚ) * power exponent = number.value := by
      simp only [Number.value, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      have exponentPower : power number.exponent = power exponent * power (shift : Int) :=
        (congrArg power shiftEq.symm).trans (power_add exponent shift)
      rw [exponentPower]
      simp only [power, zpow_natCast]
      ring
    refine ⟨digits, digitsPositive, le_rfl, ?_⟩
    apply candidate_complete_on_grid interval value positive center digits (number.coefficient * 10 ^ shift)
      (Nat.mul_pos nonzero (Nat.pow_pos (by decide)))
    change interval.accepts (((number.coefficient * 10 ^ shift : Nat) : ℚ) * power exponent) = true
    rw [onGrid]
    exact accepted
  · have coefficientBound := (repr_power_bounds number.coefficient nonzero).2
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
    have boundaryAccepted := interval.accepts_between number.value value (power (decade value)) accepted center
      numberBelow.le (decade_bounds value positive).1
    refine ⟨1, le_rfl, digitsPositive, ?_⟩
    apply candidate_complete_on_grid interval value positive center 1 1 (by decide)
    simpa only [Nat.cast_one, sub_add_cancel, one_mul] using boundaryAccepted

end Silmaril.Numeric.Ieee754.Decimal
