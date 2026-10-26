module

public import Silmaril.Numeric.Ieee754.Decimal
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-! # Correctness properties of exact decimal selection

These results concern the mathematical values of decimal candidates, their
selection order, and exact fallback. Relating the bit-neighbor interval to
binary64 RNE and proving that 17 digits always suffice are separate obligations.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

theorem power_positive (exponent : Int) : 0 < power exponent := by
  unfold power
  exact zpow_pos (by norm_num) _

theorem power_ne_zero (exponent : Int) : power exponent ≠ 0 :=
  ne_of_gt (power_positive exponent)

theorem Interval.accepts_iff (interval : Interval) (value : ℚ) :
    interval.accepts value = true ↔
      if interval.includeEnds then interval.lower ≤ value ∧ value ≤ interval.upper
      else interval.lower < value ∧ value < interval.upper := by
  cases h : interval.includeEnds <;> simp [Interval.accepts, h]

/-- Every successful candidate has passed the supplied interval predicate. -/
theorem candidate_accepts (interval : Interval) (value : ℚ) (digits : Nat)
    {number : Number} (selected : candidate interval value digits = some number) :
    interval.accepts number.value = true := by
  unfold candidate at selected
  dsimp only at selected
  split_ifs at selected <;> simp_all

/-- Zero coefficients are explicitly excluded from successful candidates. -/
theorem candidate_positive (interval : Interval) (value : ℚ) (digits : Nat)
    {number : Number} (selected : candidate interval value digits = some number) :
    0 < number.coefficient := by
  unfold candidate at selected
  dsimp only at selected
  generalize hexponent : decade value - (digits : Int) + 1 = exponent at selected
  generalize hlower : (value / power exponent).num.toNat / (value / power exponent).den = lower
    at selected
  split_ifs at selected <;>
    simp_all only [Bool.and_eq_true_iff, bne_iff_ne, Option.some.injEq, reduceCtorEq]
  all_goals subst number
  all_goals dsimp only
  all_goals omega

/-- Searching an empty precision list cannot produce a candidate. -/
@[simp] theorem firstCandidate_nil (interval : Interval) (value : ℚ) :
    firstCandidate interval value [] = none := rfl

theorem firstCandidate_none_iff (interval : Interval) (value : ℚ) (precisions : List Nat) :
    firstCandidate interval value precisions = none ↔
      ∀ digits ∈ precisions, candidate interval value digits = none := by
  induction precisions with
  | nil => simp
  | cons digits rest ih =>
    cases hc : candidate interval value digits with
    | none => simpa [firstCandidate, hc] using ih
    | some number => simp [firstCandidate, hc]

/-- A successful search selects an actual member of the precision list. -/
theorem firstCandidate_selected (interval : Interval) (value : ℚ) (precisions : List Nat)
    {number : Number} (selected : firstCandidate interval value precisions = some number) :
    ∃ digits ∈ precisions, candidate interval value digits = some number := by
  induction precisions with
  | nil => simp at selected
  | cons digits rest ih =>
    cases hc : candidate interval value digits with
    | none =>
      obtain ⟨d, member, chosen⟩ := ih (by simpa [firstCandidate, hc] using selected)
      exact ⟨d, by simp [member], chosen⟩
    | some result =>
      have equal : result = number := by simpa [firstCandidate, hc] using selected
      exact ⟨digits, by simp, equal ▸ hc⟩

theorem firstCandidate_accepts (interval : Interval) (value : ℚ) (precisions : List Nat)
    {number : Number} (selected : firstCandidate interval value precisions = some number) :
    interval.accepts number.value = true := by
  obtain ⟨digits, _, chosen⟩ := firstCandidate_selected interval value precisions selected
  exact candidate_accepts interval value digits chosen

theorem firstCandidate_positive (interval : Interval) (value : ℚ) (precisions : List Nat)
    {number : Number} (selected : firstCandidate interval value precisions = some number) :
    0 < number.coefficient := by
  obtain ⟨digits, _, chosen⟩ := firstCandidate_selected interval value precisions selected
  exact candidate_positive interval value digits chosen

/-- Every precision preceding the selected one failed. This formulation also
handles custom precision schedules, without assuming that they are sorted. -/
theorem firstCandidate_first (interval : Interval) (value : ℚ) (precisions : List Nat)
    {number : Number} (selected : firstCandidate interval value precisions = some number) :
    ∃ before digits after, precisions = before ++ digits :: after ∧
      (∀ d ∈ before, candidate interval value d = none) ∧
      candidate interval value digits = some number := by
  induction precisions with
  | nil => simp at selected
  | cons digits rest ih =>
    cases hc : candidate interval value digits with
    | none =>
      obtain ⟨before, d, after, decomposition, previous, chosen⟩ :=
        ih (by simpa [firstCandidate, hc] using selected)
      refine ⟨digits :: before, d, after, by simp [decomposition], ?_, chosen⟩
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hc
      · exact previous k hk
    | some result =>
      have equal : result = number := by simpa [firstCandidate, hc] using selected
      exact ⟨[], digits, rest, rfl, by simp, equal ▸ hc⟩

/-- With an increasing consecutive schedule, the selected precision is the
least one in the search range whose adjacent-lattice test succeeds. -/
theorem firstCandidate_precision_minimal (interval : Interval) (value : ℚ)
    (start count : Nat) {number : Number}
    (selected : firstCandidate interval value (List.range' start count) = some number) :
    ∃ digits, start ≤ digits ∧ digits < start + count ∧
      candidate interval value digits = some number ∧
      ∀ earlier, start ≤ earlier → earlier < digits → candidate interval value earlier = none := by
  induction count generalizing start with
  | zero => simp at selected
  | succ count ih =>
    rw [List.range'_succ] at selected
    cases hc : candidate interval value start with
    | none =>
      obtain ⟨digits, lower, upper, chosen, minimal⟩ :=
        ih (start + 1) (by simpa [firstCandidate, hc] using selected)
      refine ⟨digits, by omega, by omega, chosen, ?_⟩
      intro earlier lower' upper'
      by_cases first : earlier = start
      · simpa [first] using hc
      · exact minimal earlier (by omega) upper'
    | some result =>
      have equal : result = number := by simpa [firstCandidate, hc] using selected
      exact ⟨start, Nat.le_refl _, by omega, equal ▸ hc, fun _ _ impossible => by omega⟩

/-- Exact conversion of an unsigned dyadic to a decimal, including negative
binary exponents. This is pure integer/rational arithmetic. -/
theorem dyadic_decimal_value (mantissa : Nat) (exponent : Int) :
    (if exponent < 0 then
      Number.mk (mantissa * 5 ^ (-exponent).toNat) exponent
    else Number.mk (mantissa * 2 ^ exponent.toNat) 0).value =
      (mantissa : ℚ) * (2 : ℚ) ^ exponent := by
  cases exponent with
  | ofNat n =>
    have nonnegative : ¬ ((n : Int) < 0) := not_lt.mpr (Int.natCast_nonneg n)
    simp [nonnegative, Number.value, power]
  | negSucc n =>
    simp only [Int.negSucc_lt_zero, ↓reduceIte, Int.neg_negSucc, Int.toNat_natCast,
      Number.value, power, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [Int.negSucc_eq]
    have exponent_cast : (n : Int) + 1 = ((n + 1 : Nat) : Int) := by omega
    rw [exponent_cast]
    simp only [zpow_neg, zpow_natCast]
    have ten : (10 : ℚ) = 2 * 5 := by norm_num
    rw [ten, mul_pow, mul_inv_rev]
    field_simp

/-- The fallback is the exact magnitude, independently of the finite search
bound. The public formatter supplies positive, finite, nonzero encodings. -/
theorem exact_value (bits : UInt64) : (exact bits).value = |rational bits| := by
  unfold exact rational
  cases h : (F64.ofBits bits).model.unpack with
  | zero sign => simp [Number.value, Conformance.value?]
  | infinity sign => simp [Number.value, Conformance.value?]
  | notANumber => simp [Number.value, Conformance.value?]
  | finite sign mantissa exponent positive =>
    rw [dyadic_decimal_value]
    simp only [Conformance.value?, Option.getD_some, Conformance.dyadic]
    have nonnegative : (0 : ℚ) ≤ (mantissa : ℚ) * 2 ^ exponent :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos (by norm_num) exponent))
    cases sign <;> simp [Float.Model.UnpackedFloat.Sign.apply, abs_of_nonneg nonnegative]

theorem trim_step_value (number : Number) (divisible : number.coefficient % 10 = 0) :
    (Number.mk (number.coefficient / 10) (number.exponent + 1)).value = number.value := by
  have product : number.coefficient / 10 * 10 = number.coefficient :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero divisible)
  have castProduct : (number.coefficient / 10 : Nat) * (10 : ℚ) = number.coefficient := by
    exact_mod_cast product
  simp only [Number.value, power, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one]
  calc
    (number.coefficient / 10 : Nat) * ((10 : ℚ) ^ number.exponent * 10) =
        ((number.coefficient / 10 : Nat) * (10 : ℚ)) * 10 ^ number.exponent := by ring
    _ = _ := by rw [castProduct]

/-- Trimming preserves the exact rational value for every fuel amount. -/
theorem trim_value (fuel : Nat) (number : Number) : (trim fuel number).value = number.value := by
  induction fuel generalizing number with
  | zero => rfl
  | succ fuel ih =>
    simp only [trim]
    split
    next condition =>
      have divisible : number.coefficient % 10 = 0 := by
        have both : number.coefficient ≠ 0 ∧ number.coefficient % 10 = 0 := by simpa using condition
        exact both.2
      rw [ih, trim_step_value number divisible]
    next _ => rfl

/-- Regardless of the search bound, the result either passed the interval
test or is the exact value fallback. -/
theorem shortest_accepted_or_exact (bits : UInt64) :
    (roundingInterval bits).accepts (shortest bits).value = true ∨
      (shortest bits).value = |rational bits| := by
  cases selected : firstCandidate (roundingInterval bits) (rational bits) (List.range' 1 17) with
  | none => exact Or.inr (by simpa [shortest, selected] using exact_value bits)
  | some number =>
    exact Or.inl (by simpa [shortest, selected] using (firstCandidate_accepts
      (roundingInterval bits) (rational bits) (List.range' 1 17) selected))

end Silmaril.Numeric.Ieee754.Decimal
