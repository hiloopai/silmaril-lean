module

public import Silmaril.Numeric.Ieee754.DecimalEncodingBounds
public import Silmaril.Numeric.Ieee754.RationalRounding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Decimal intervals round back to their binary64 encoding

The bridge targets the executable exact-rational converter. Its independently
proved nearest-even specification includes parity and the overflow threshold.
Positive finite encodings, all boundary binades, and the zero neighbor are
covered. Signed text layout and global decimal shortestness remain separate.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

open RationalRounding

/-- Preserve non-strict bounds and record that accepted endpoints require the
interval's explicit endpoint-inclusion bit. -/
theorem Interval.accepted_bounds (interval : Interval) (query : ℚ)
    (accepted : interval.accepts query = true) :
    interval.lower ≤ query ∧ query ≤ interval.upper ∧
      (query = interval.lower → interval.includeEnds = true) ∧
      (query = interval.upper → interval.includeEnds = true) := by
  cases ends : interval.includeEnds with
  | false =>
    simp only [Interval.accepts, ends, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at accepted
    exact ⟨accepted.1.le, accepted.2.le, fun equal => False.elim (by rw [equal] at accepted; exact lt_irrefl _ accepted.1),
      fun equal => False.elim (by rw [equal] at accepted; exact lt_irrefl _ accepted.2)⟩
  | true =>
    simp only [Interval.accepts, ends, ↓reduceIte, decide_eq_true_eq] at accepted
    exact ⟨accepted.1, accepted.2, fun _ => rfl, fun _ => rfl⟩

theorem roundingInterval_lower_magnitude (bits : UInt64)
    (positive : 0 < bits.toNat) (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    (roundingInterval bits).lower =
      (magnitude (bits.toNat - 1) + magnitude bits.toNat) / 2 := by
  have previous := predecessor_toNat bits positive
  have previousFinite : (bits - 1).toNat ≤ 0x7fefffffffffffff := by rw [previous]; omega
  change (rational (bits - 1) + rational bits) / 2 = _
  rw [rational_eq_binaryMagnitude (bits - 1) previousFinite, rational_eq_binaryMagnitude bits finite, previous]
  rfl

/-- The formatter's extrapolated maximum-finite neighbor is exactly the
virtual overflow magnitude used by nearest-even conversion. -/
theorem following_magnitude (bits : UInt64) (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    (if bits == 0x7fefffffffffffff then rational bits + (rational bits - rational (bits - 1))
      else rational (bits + 1)) = magnitude (bits.toNat + 1) := by
  by_cases maximum : bits = 0x7fefffffffffffff
  · subst bits
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [rational_eq_binaryMagnitude 0x7fefffffffffffff (by decide),
      rational_eq_binaryMagnitude (0x7fefffffffffffff - 1) (by decide)]
    change BinaryMagnitude.value 52 1023 0x7fefffffffffffff +
      (BinaryMagnitude.value 52 1023 0x7fefffffffffffff -
        BinaryMagnitude.value 52 1023 0x7feffffffffffffe) =
      BinaryMagnitude.value 52 1023 0x7ff0000000000000
    have next := BinaryMagnitude.value_succ 52 1023 0x7fefffffffffffff
    have previous := BinaryMagnitude.value_succ 52 1023 0x7feffffffffffffe
    norm_num only [BinaryMagnitude.radix] at next previous
    linarith
  · have different : bits.toNat ≠ 0x7fefffffffffffff := by
      intro equal
      exact maximum (UInt64.toNat_inj.mp equal)
    have next := successor_toNat bits finite
    have nextFinite : (bits + 1).toNat ≤ 0x7fefffffffffffff := by rw [next]; omega
    simp only [beq_eq_false_iff_ne.mpr maximum, Bool.false_eq_true, ↓reduceIte]
    rw [rational_eq_binaryMagnitude (bits + 1) nextFinite, next]
    rfl

theorem roundingInterval_upper_magnitude (bits : UInt64) (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    (roundingInterval bits).upper = (magnitude bits.toNat + magnitude (bits.toNat + 1)) / 2 := by
  change (rational bits + (if bits == 0x7fefffffffffffff then
    rational bits + (rational bits - rational (bits - 1)) else rational (bits + 1))) / 2 = _
  rw [following_magnitude bits finite, rational_eq_binaryMagnitude bits finite]
  rfl

/-- Acceptance gives the two exact midpoint inequalities and the requisite
even low bit at either equality boundary. -/
theorem accepted_midpoints (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) (query : ℚ)
    (accepted : (roundingInterval bits).accepts query = true) :
    magnitude (bits.toNat - 1) + magnitude bits.toNat ≤ 2 * query ∧
      2 * query ≤ magnitude bits.toNat + magnitude (bits.toNat + 1) ∧
      (2 * query = magnitude (bits.toNat - 1) + magnitude bits.toNat → bits.toNat % 2 = 0) ∧
      (2 * query = magnitude bits.toNat + magnitude (bits.toNat + 1) → bits.toNat % 2 = 0) := by
  obtain ⟨lower, upper, lowerEnd, upperEnd⟩ := (roundingInterval bits).accepted_bounds query accepted
  have lo := roundingInterval_lower_magnitude bits positive finite
  have hi := roundingInterval_upper_magnitude bits finite
  refine ⟨by rw [lo] at lower; linarith, by rw [hi] at upper; linarith, ?_, ?_⟩
  · intro tie
    have ends := lowerEnd (by rw [lo]; linarith)
    simpa only [roundingInterval, beq_iff_eq] using ends
  · intro tie
    have ends := upperEnd (by rw [hi]; linarith)
    simpa only [roundingInterval, beq_iff_eq] using ends

theorem accepted_positive_below_overflow (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) (query : ℚ)
    (accepted : (roundingInterval bits).accepts query = true) :
    0 < query ∧ query < overflowThreshold := by
  obtain ⟨lower, upper, _, upperEven⟩ := accepted_midpoints bits positive finite query accepted
  have valuePositive : 0 < magnitude bits.toNat := BinaryMagnitude.value_pos 52 1023 _ positive
  have previousNonnegative : 0 ≤ magnitude (bits.toNat - 1) := BinaryMagnitude.value_nonneg 52 1023 _
  refine ⟨by linarith, ?_⟩
  have bounded : bits.toNat ≤ limit - 1 := finite
  by_cases maximum : bits.toNat = limit - 1
  · have next : bits.toNat + 1 = limit := by rw [maximum]; decide
    have odd : bits.toNat % 2 ≠ 0 := by rw [maximum]; decide
    have strict : 2 * query < magnitude bits.toNat + magnitude (bits.toNat + 1) := by
      by_contra nonstrict
      exact odd (upperEven (by linarith))
    rw [next, maximum] at strict
    unfold overflowThreshold
    linarith
  · have below : bits.toNat < limit - 1 := by omega
    have less := magnitude_strictMono below
    have following := magnitude_strictMono.monotone (by omega : bits.toNat + 1 ≤ limit)
    unfold overflowThreshold
    linarith

/-- Every accepted positive decimal rational rounds to the original actual
binary64 bits, including both midpoint parity cases and the overflow boundary. -/
theorem accepted_roundtrips (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) (query : ℚ)
    (accepted : (roundingInterval bits).accepts query = true) :
    roundPositive query = bits := by
  obtain ⟨queryPositive, below⟩ := accepted_positive_below_overflow bits positive finite query accepted
  obtain ⟨lower, upper, lowerEven, upperEven⟩ := accepted_midpoints bits positive finite query accepted
  have index := roundIndex_of_midpoints query queryPositive.le below bits.toNat positive lower upper lowerEven upperEven
  apply UInt64.toNat_inj.mp
  rw [roundPositive_toNat, index]

/-- The proven complete 17-digit search returns a decimal that converts back
to the exact source binary64 encoding. -/
theorem shortest_roundtrips (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) : roundPositive (shortest bits).value = bits :=
  accepted_roundtrips bits positive finite _ (shortest_accepts_of_positive_finite bits positive finite)

/-- Every positive finite binary64 magnitude is strictly inside its own
rounding interval, including the two unequal spacings at a binade boundary. -/
theorem rational_accepted (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) :
    (roundingInterval bits).accepts (rational bits) = true := by
  apply Interval.accepts_of_strict
  · rw [roundingInterval_lower_magnitude bits positive finite, rational_eq_binaryMagnitude bits finite]
    have gap := magnitude_strictMono (show bits.toNat - 1 < bits.toNat by omega)
    change (magnitude (bits.toNat - 1) + magnitude bits.toNat) / 2 < magnitude bits.toNat
    linarith
  · rw [roundingInterval_upper_magnitude bits finite, rational_eq_binaryMagnitude bits finite]
    have gap := magnitude_strictMono (Nat.lt_succ_self bits.toNat)
    change magnitude bits.toNat < (magnitude bits.toNat + magnitude (bits.toNat + 1)) / 2
    linarith

/-- Exact represented magnitudes are fixed by the rational converter. The
rational here is the actual Lean binary64 model decoder, not an alternative
nearest-distance representative. -/
theorem rational_roundtrips (bits : UInt64) (positive : 0 < bits.toNat)
    (finite : bits.toNat ≤ 0x7fefffffffffffff) : roundPositive (rational bits) = bits :=
  accepted_roundtrips bits positive finite _ (rational_accepted bits positive finite)

end Silmaril.Numeric.Ieee754.Decimal

namespace Silmaril.Numeric.Ieee754.RationalRounding

/-- Independent nearest-even correctness stated over every finite positive
binary64 encoding, with equality of actual interchange bits on tied values. -/
theorem roundPositive_nearestFinite (query : ℚ) (nonnegative : 0 ≤ query)
    (below : query < overflowThreshold) :
    (roundPositive query).toNat ≤ 0x7fefffffffffffff ∧
      (∀ candidate : UInt64, candidate.toNat ≤ 0x7fefffffffffffff →
        |query - Decimal.rational (roundPositive query)| ≤ |query - Decimal.rational candidate|) ∧
      (∀ candidate : UInt64, candidate.toNat ≤ 0x7fefffffffffffff →
        |query - Decimal.rational (roundPositive query)| = |query - Decimal.rational candidate| →
          (roundPositive query).toNat % 2 = 0 ∨ candidate = roundPositive query) := by
  obtain ⟨bounded, nearest, ties⟩ := roundIndex_nearestEven query nonnegative below
  have finite : (roundPositive query).toNat ≤ 0x7fefffffffffffff := by
    rw [roundPositive_toNat]
    unfold limit at bounded
    omega
  refine ⟨finite, ?_, ?_⟩
  · intro candidate candidateFinite
    rw [Decimal.rational_eq_binaryMagnitude _ finite, Decimal.rational_eq_binaryMagnitude _ candidateFinite,
      roundPositive_toNat]
    exact nearest candidate.toNat
  · intro candidate candidateFinite equal
    rw [Decimal.rational_eq_binaryMagnitude _ finite, Decimal.rational_eq_binaryMagnitude _ candidateFinite,
      roundPositive_toNat] at equal
    rcases ties candidate.toNat equal with even | same
    · exact Or.inl (by simpa only [roundPositive_toNat] using even)
    · right
      apply UInt64.toNat_inj.mp
      rw [roundPositive_toNat]
      exact same

/-- The even virtual overflow endpoint encodes positive infinity exactly. -/
theorem roundPositive_overflow_iff (query : ℚ) (nonnegative : 0 ≤ query) :
    roundPositive query = 0x7ff0000000000000 ↔ overflowThreshold ≤ query := by
  rw [← UInt64.toNat_inj, roundPositive_toNat]
  exact roundIndex_overflow_iff query nonnegative

end Silmaril.Numeric.Ieee754.RationalRounding
