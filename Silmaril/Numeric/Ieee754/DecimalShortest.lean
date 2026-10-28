module

public import Silmaril.Numeric.Ieee754.DecimalLattice
public import Silmaril.Numeric.Ieee754.DecimalNormalization
public import Silmaril.Numeric.Ieee754.DecimalRounding

/-! # Global shortestness of the binary64 decimal formatter

Minimality ranges over every accepted positive decimal representation, after
removing trailing zeros. In particular it does not assume that a competing
representation lies in the input's decimal decade or on the selected grid.
The selected search precision equals the output's significant-digit count.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

/-- A successful increasing search attains the minimum number of significant
digits among every accepted positive decimal. Convexity, rather than a
same-decade restriction on competitors, connects them to searched candidates. -/
theorem firstCandidate_global_minimum (interval : Interval) (value : ℚ) (positive : 0 < value)
    (center : interval.accepts value = true) (count : Nat) {result : Number}
    (selected : firstCandidate interval value (List.range' 1 count) = some result) :
    ∃ digits, 1 ≤ digits ∧ digits < 1 + count ∧
      candidate interval value digits = some result ∧
      result.significantDigits = digits ∧
      ∀ number : Number, 0 < number.coefficient → interval.accepts number.value = true →
        digits ≤ number.significantDigits := by
  obtain ⟨digits, lower, upper, chosen, minimal⟩ :=
    firstCandidate_precision_minimal interval value 1 count selected
  have global : ∀ number : Number, 0 < number.coefficient → interval.accepts number.value = true →
      digits ≤ number.significantDigits := by
    intro number numberPositive accepted
    have normalizedAccepted : interval.accepts number.normalize.value = true := by
      rw [number.normalize_value]
      exact accepted
    obtain ⟨precision, precisionPositive, precisionBound, output, found⟩ :=
      candidate_complete_for_number interval value positive center number.normalize
        (number.normalize_positive numberPositive) normalizedAccepted
    have earlier : digits ≤ precision := by
      by_contra failed
      have missing := minimal precision precisionPositive (by omega)
      rw [found] at missing
      contradiction
    exact earlier.trans precisionBound
  have bound : result.significantDigits ≤ digits :=
    result.significantDigits_le digits lower
      (candidate_coefficient_bound interval value positive digits chosen)
  have reverse := global result (candidate_positive interval value digits chosen)
    (candidate_accepts interval value digits chosen)
  exact ⟨digits, lower, upper, chosen, Nat.le_antisymm bound reverse, global⟩

/-- Global significant-digit minimality, in a convenient comparison form. -/
theorem firstCandidate_significantDigits_minimal (interval : Interval) (value : ℚ)
    (positive : 0 < value) (center : interval.accepts value = true) (count : Nat) {result : Number}
    (selected : firstCandidate interval value (List.range' 1 count) = some result)
    (number : Number) (numberPositive : 0 < number.coefficient)
    (accepted : interval.accepts number.value = true) :
    result.significantDigits ≤ number.significantDigits := by
  obtain ⟨_, _, _, _, equal, minimal⟩ :=
    firstCandidate_global_minimum interval value positive center count selected
  rw [equal]
  exact minimal number numberPositive accepted

/-- The binary64 search result is positive, so its layout normalization is
well-defined as a positive coefficient with no trailing decimal zeros. -/
theorem shortest_positive (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) : 0 < (shortest bits).coefficient := by
  obtain ⟨number, selected⟩ := shortest_search_success_of_positive_finite bits positive finite
  simpa only [shortest, selected, Option.getD_some] using
    firstCandidate_positive (roundingInterval bits) (rational bits) (List.range' 1 17) selected

/-- The formatter's selected precision is exactly its significant-digit
count, and is globally minimal among all accepted positive decimal numbers. -/
theorem shortest_global_minimum (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    ∃ digits, 1 ≤ digits ∧ digits ≤ 17 ∧
      candidate (roundingInterval bits) (rational bits) digits = some (shortest bits) ∧
      (shortest bits).significantDigits = digits ∧
      ∀ number : Number, 0 < number.coefficient →
        (roundingInterval bits).accepts number.value = true → digits ≤ number.significantDigits := by
  obtain ⟨number, selected⟩ := shortest_search_success_of_positive_finite bits positive finite
  obtain ⟨digits, lower, upper, chosen, equal, minimal⟩ :=
    firstCandidate_global_minimum (roundingInterval bits) (rational bits)
      (rational_pos_of_positive_finite bits positive finite) (rational_accepted bits positive finite) 17 selected
  have result : shortest bits = number := by simp only [shortest, selected, Option.getD_some]
  exact ⟨digits, lower, by omega, result ▸ chosen, result ▸ equal, minimal⟩

/-- No accepted decimal has fewer significant digits than the formatter's
trimmed result. Competitors may have arbitrary exponents and trailing zeros. -/
theorem shortest_significantDigits_minimal (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) (number : Number)
    (numberPositive : 0 < number.coefficient)
    (accepted : (roundingInterval bits).accepts number.value = true) :
    (shortest bits).significantDigits ≤ number.significantDigits := by
  obtain ⟨_, _, _, _, equal, minimal⟩ := shortest_global_minimum bits positive finite
  rw [equal]
  exact minimal number numberPositive accepted

/-- The actual normalized output has a minimum-length coefficient among all
accepted normalized decimal representations of this positive finite float. -/
theorem shortest_normalized_minimal (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) (number : Number) (normalized : number.Normalized)
    (accepted : (roundingInterval bits).accepts number.value = true) :
    (toString (shortest bits).normalize.coefficient).length ≤ (toString number.coefficient).length := by
  have minimal := shortest_significantDigits_minimal bits positive finite number normalized.1 accepted
  simpa only [Number.significantDigits, number.normalize_of_normalized normalized] using minimal

/-- The minimum-length normalized decimal is positive, has no trailing zeros,
and rounds back through the proved rational ties-to-even converter. -/
theorem shortest_normalized_roundtrips (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    (shortest bits).normalize.Normalized ∧
      RationalRounding.roundPositive (shortest bits).normalize.value = bits := by
  refine ⟨(shortest bits).normalize_normalized (shortest_positive bits positive finite), ?_⟩
  rw [Number.normalize_value]
  exact shortest_roundtrips bits positive finite

end Silmaril.Numeric.Ieee754.Decimal
