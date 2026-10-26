module

public import Silmaril.Numeric.Ieee754.DecimalProperties
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Decimal magnitude and lattice bounds

Arithmetic properties of the decimal search that do not depend on the binary64
encoding. Bounds for actual adjacent encodings remain a separate obligation.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

theorem power_sub (a b : Int) : power (a - b) = power a / power b := by
  exact zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0) a b

theorem repr_power_bounds (n : Nat) (positive : 0 < n) :
    power ((toString n).length - 1) ≤ (n : ℚ) ∧ (n : ℚ) < power (toString n).length := by
  change power ((n.repr.length : Int) - 1) ≤ (n : ℚ) ∧ (n : ℚ) < power n.repr.length
  have lengthPositive : 0 < n.repr.length := Nat.length_repr_pos
  have upper : n < 10 ^ n.repr.length :=
    (Nat.length_repr_le_iff lengthPositive).mp (Nat.le_refl _)
  have lower : 10 ^ (n.repr.length - 1) ≤ n := by
    by_cases one : n.repr.length = 1
    · norm_num [one]
      omega
    · by_contra tooSmall
      have small := (Nat.length_repr_le_iff (by omega : 0 < n.repr.length - 1)).mpr
        (Nat.lt_of_not_ge tooSmall)
      omega
  have exponent : (n.repr.length : Int) - 1 = ((n.repr.length - 1 : Nat) : Int) := by omega
  rw [exponent]
  simp only [power, zpow_natCast]
  constructor <;> exact_mod_cast (by assumption)

/-- The decimal-length estimate is at most one decade away; the final exact
comparison therefore computes the floor base-ten exponent for every positive
rational, including fractions with very large denominators. -/
theorem decade_bounds (value : ℚ) (positive : 0 < value) :
    power (decade value) ≤ value ∧ value < power (decade value + 1) := by
  let numerator := value.num.natAbs
  let denominator := value.den
  let a : Int := (toString numerator).length
  let b : Int := (toString denominator).length
  have numeratorPositive : 0 < numerator := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr positive))
  have denominatorPositive : 0 < denominator := value.pos
  have denPos : (0 : ℚ) < denominator := by exact_mod_cast denominatorPositive
  have numValue : (numerator : ℚ) = value.num := by
    change (((value.num.natAbs : Nat) : Int) : ℚ) = (value.num : ℚ)
    rw [Int.natAbs_of_nonneg (Rat.num_pos.mpr positive).le]
  have ratio : (numerator : ℚ) / denominator = value := by
    rw [numValue]
    exact Rat.num_div_den value
  obtain ⟨nl, nu⟩ := repr_power_bounds numerator numeratorPositive
  obtain ⟨dl, du⟩ := repr_power_bounds denominator denominatorPositive
  have low : power (a - 1) / power b < value := by
    rw [← ratio]
    exact lt_of_lt_of_le (div_lt_div_of_pos_left (power_positive _) denPos du)
      (div_le_div_of_nonneg_right nl denPos.le)
  have high : value < power a / power (b - 1) := by
    rw [← ratio]
    exact lt_of_lt_of_le (div_lt_div_of_pos_right nu denPos)
      (div_le_div_of_nonneg_left (le_of_lt (power_positive _)) (power_positive _) dl)
  have low' : power (a - b - 1) < value := by
    have exponents : a - b - 1 = (a - 1) - b := by omega
    simpa [exponents, power_sub] using low
  have high' : value < power (a - b + 1) := by
    have exponents : a - b + 1 = a - (b - 1) := by omega
    simpa [exponents, power_sub] using high
  change power (if value < power (a - b) then a - b - 1 else a - b) ≤ value ∧
    value < power ((if value < power (a - b) then a - b - 1 else a - b) + 1)
  by_cases below : value < power (a - b)
  · simp only [below, ↓reduceIte]
    exact ⟨low'.le, by simpa using below⟩
  · simp only [below, ↓reduceIte]
    exact ⟨le_of_not_gt below, high'⟩

/-- The implementation's natural quotient is precisely the floor of a
nonnegative rational, despite its intermediate signed numerator. -/
theorem natural_quotient_floor (q : ℚ) (nonnegative : 0 ≤ q) :
    (q.num.toNat / q.den : Nat) = Int.floor q := by
  rw [Rat.floor_def']
  have num : (q.num.toNat : Int) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr nonnegative)
  rw [Int.natCast_ediv, num]

/-- The two coefficients considered by the algorithm bracket the scaled
positive input, with a strict bound on the upper adjacent lattice point. -/
theorem quotient_brackets (q : ℚ) (nonnegative : 0 ≤ q) :
    (q.num.toNat / q.den : Nat) ≤ q ∧ q < (q.num.toNat / q.den : Nat) + 1 := by
  have castFloor : ((q.num.toNat / q.den : Nat) : ℚ) = (Int.floor q : ℚ) := by
    exact congrArg (fun n : Int => (n : ℚ)) (natural_quotient_floor q nonnegative)
  rw [castFloor]
  exact ⟨Int.floor_le q, Int.lt_floor_add_one q⟩

def lowerNeighbor (value : ℚ) (digits : Nat) : Number :=
  let exponent := decade value - (digits : Int) + 1
  let scaled := value / power exponent
  ⟨scaled.num.toNat / scaled.den, exponent⟩

def upperNeighbor (value : ℚ) (digits : Nat) : Number :=
  ⟨(lowerNeighbor value digits).coefficient + 1, (lowerNeighbor value digits).exponent⟩

theorem candidate_none_iff (interval : Interval) (value : ℚ) (digits : Nat) :
    candidate interval value digits = none ↔
      ((lowerNeighbor value digits).coefficient = 0 ∨
        interval.accepts (lowerNeighbor value digits).value = false) ∧
      interval.accepts (upperNeighbor value digits).value = false := by
  unfold candidate upperNeighbor lowerNeighbor
  dsimp only
  generalize decade value - (digits : Int) + 1 = exponent
  generalize (value / power exponent).num.toNat / (value / power exponent).den = lower
  split_ifs <;> simp_all
  all_goals
    by_cases zero : lower = 0
    · exact Or.inl zero
    · exact Or.inr (by solve_by_elim)

theorem candidate_exists_of_lower (interval : Interval) (value : ℚ) (digits : Nat)
    (positive : 0 < (lowerNeighbor value digits).coefficient)
    (accepted : interval.accepts (lowerNeighbor value digits).value = true) :
    ∃ number, candidate interval value digits = some number := by
  cases selected : candidate interval value digits with
  | some number => exact ⟨number, rfl⟩
  | none =>
    have rejected := ((candidate_none_iff interval value digits).mp selected).1
    rcases rejected with zero | rejected
    · omega
    · simp [accepted] at rejected

theorem candidate_exists_of_upper (interval : Interval) (value : ℚ) (digits : Nat)
    (accepted : interval.accepts (upperNeighbor value digits).value = true) :
    ∃ number, candidate interval value digits = some number := by
  cases selected : candidate interval value digits with
  | some number => exact ⟨number, rfl⟩
  | none =>
    have rejected := ((candidate_none_iff interval value digits).mp selected).2
    simp [accepted] at rejected

/-- Multiplying the floor bounds by a positive decimal spacing produces
adjacent decimal numbers on either side of the exact input. -/
theorem neighbor_brackets (value : ℚ) (nonnegative : 0 ≤ value) (digits : Nat) :
    (lowerNeighbor value digits).value ≤ value ∧ value < (upperNeighbor value digits).value := by
  let exponent := decade value - (digits : Int) + 1
  have spacing : 0 < power exponent := power_positive exponent
  obtain ⟨lower, upper⟩ := quotient_brackets (value / power exponent)
    (div_nonneg nonnegative spacing.le)
  constructor
  · exact (le_div_iff₀ spacing).mp lower
  · simpa only [upperNeighbor, lowerNeighbor, Number.value, Nat.cast_add, Nat.cast_one] using
      (div_lt_iff₀ spacing).mp upper

theorem neighbor_gap (value : ℚ) (digits : Nat) :
    (upperNeighbor value digits).value - (lowerNeighbor value digits).value =
      power (decade value - (digits : Int) + 1) := by
  simp only [upperNeighbor, lowerNeighbor, Number.value, Nat.cast_add, Nat.cast_one]
  ring

theorem Interval.accepts_of_strict (interval : Interval) (value : ℚ)
    (lower : interval.lower < value) (upper : value < interval.upper) :
    interval.accepts value = true := by
  cases h : interval.includeEnds <;> simp [Interval.accepts, h, lower, upper, lower.le, upper.le]

/-- Seventeen digits suffice for every positive rational whose interval
contains a relative open ball of radius `value / 2^54`. The remaining binary64
obligation is to establish this radius for the actual neighboring encodings. -/
theorem seventeen_digits_of_relative_interval (interval : Interval) (value : ℚ)
    (positive : 0 < value)
    (lower : interval.lower ≤ value - value / 2 ^ 54)
    (upper : value + value / 2 ^ 54 ≤ interval.upper) :
    ∃ number, candidate interval value 17 = some number := by
  let a := lowerNeighbor value 17
  let b := upperNeighbor value 17
  let delta := power (decade value - (17 : Int) + 1)
  have deltaPos : 0 < delta := power_positive _
  have scaledPower : delta * 10 ^ 16 = power (decade value) := by
    change power (decade value - (17 : Int) + 1) * (10 : ℚ) ^ (16 : Nat) = _
    rw [← zpow_natCast (10 : ℚ) 16]
    change (10 : ℚ) ^ (decade value - 17 + 1) * 10 ^ (16 : Int) = _
    rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    have exponent : decade value - 17 + 1 + (16 : Int) = decade value := by omega
    rw [exponent]
    rfl
  have gridBound : delta * 10 ^ 16 ≤ value := by
    rw [scaledPower]
    exact (decade_bounds value positive).1
  have narrow : delta / 2 < value / 2 ^ 54 := by
    norm_num at gridBound ⊢
    linarith
  have gridBelow : delta ≤ value := by
    norm_num at gridBound
    linarith
  obtain ⟨aBelow, bAbove⟩ := neighbor_brackets value positive.le 17
  have gap : b.value - a.value = delta := neighbor_gap value 17
  have aPositive : 0 < a.coefficient := by
    by_contra nonpositive
    have zero : a.coefficient = 0 := by omega
    have aZero : a.value = 0 := by simp [Number.value, zero]
    have bound : b.value = delta := by linarith
    linarith
  by_cases nearer : value - a.value ≤ delta / 2
  · apply candidate_exists_of_lower interval value 17 aPositive
    apply Interval.accepts_of_strict
    · linarith
    · linarith
  · apply candidate_exists_of_upper interval value 17
    apply Interval.accepts_of_strict
    · linarith
    · linarith

theorem firstCandidate_seventeen_exists (interval : Interval) (value : ℚ)
    (positive : 0 < value)
    (lower : interval.lower ≤ value - value / 2 ^ 54)
    (upper : value + value / 2 ^ 54 ≤ interval.upper) :
    ∃ number, firstCandidate interval value (List.range' 1 17) = some number := by
  obtain ⟨number, chosen⟩ := seventeen_digits_of_relative_interval interval value positive lower upper
  cases selected : firstCandidate interval value (List.range' 1 17) with
  | some result => exact ⟨result, rfl⟩
  | none =>
    have rejected := (firstCandidate_none_iff interval value (List.range' 1 17)).mp selected 17
      (by simp [List.mem_range']; exact ⟨16, by omega, by omega⟩)
    simp [chosen] at rejected

/-- The arithmetic link from adjacent binary values to the sufficient
relative interval bound. At maximum finite the following value is extrapolated
from the preceding spacing, exactly as in `roundingInterval`. -/
theorem roundingInterval_relative_of_gaps (bits : UInt64)
    (lowerGap : rational bits / 2 ^ 53 ≤ rational bits - rational (bits - 1))
    (upperGap : bits ≠ 0x7fefffffffffffff →
      rational bits / 2 ^ 53 ≤ rational (bits + 1) - rational bits) :
    (roundingInterval bits).lower ≤ rational bits - rational bits / 2 ^ 54 ∧
      rational bits + rational bits / 2 ^ 54 ≤ (roundingInterval bits).upper := by
  constructor
  · change (rational (bits - 1) + rational bits) / 2 ≤ rational bits - rational bits / 2 ^ 54
    norm_num at lowerGap ⊢
    linarith
  · by_cases maximum : bits = 0x7fefffffffffffff
    · simp only [roundingInterval, maximum, beq_self_eq_true, ↓reduceIte]
      rw [maximum] at lowerGap
      norm_num at lowerGap ⊢
      linarith
    · have upper := upperGap maximum
      have different : (bits == 0x7fefffffffffffff) = false := by simpa using maximum
      simp only [roundingInterval, different, Bool.false_eq_true, ↓reduceIte]
      norm_num at upper ⊢
      linarith

/-- Conditional search completeness for the actual formatter interval. The
two explicitly stated gap inequalities isolate the remaining encoding proof. -/
theorem shortest_search_success_of_gaps (bits : UInt64) (positive : 0 < rational bits)
    (lowerGap : rational bits / 2 ^ 53 ≤ rational bits - rational (bits - 1))
    (upperGap : bits ≠ 0x7fefffffffffffff →
      rational bits / 2 ^ 53 ≤ rational (bits + 1) - rational bits) :
    ∃ number, firstCandidate (roundingInterval bits) (rational bits) (List.range' 1 17) = some number := by
  obtain ⟨lower, upper⟩ := roundingInterval_relative_of_gaps bits lowerGap upperGap
  exact firstCandidate_seventeen_exists (roundingInterval bits) (rational bits) positive lower upper

theorem shortest_accepts_of_gaps (bits : UInt64) (positive : 0 < rational bits)
    (lowerGap : rational bits / 2 ^ 53 ≤ rational bits - rational (bits - 1))
    (upperGap : bits ≠ 0x7fefffffffffffff →
      rational bits / 2 ^ 53 ≤ rational (bits + 1) - rational bits) :
    (roundingInterval bits).accepts (shortest bits).value = true := by
  obtain ⟨number, selected⟩ := shortest_search_success_of_gaps bits positive lowerGap upperGap
  simpa [shortest, selected] using firstCandidate_accepts (roundingInterval bits)
    (rational bits) (List.range' 1 17) selected

end Silmaril.Numeric.Ieee754.Decimal
