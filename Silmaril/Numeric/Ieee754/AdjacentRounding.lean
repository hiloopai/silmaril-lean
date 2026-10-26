module

public import Silmaril.Numeric.Ieee754.Bisection
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

/-! # Nearest-even selection in a strictly ordered magnitude sequence

The specification minimizes distance against every candidate and requires
even index parity for genuine ties. It is independent of decimal intervals.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.AdjacentRounding

/-- Nearest magnitude, with even low-bit tie preference. -/
def NearestEven (value : Nat → ℚ) (query : ℚ) (result : Nat) : Prop :=
  (∀ candidate, |query - value result| ≤ |query - value candidate|) ∧
    ∀ candidate, |query - value result| = |query - value candidate| →
      result % 2 = 0 ∨ candidate = result

/-- Compare the exact midpoint, choosing the even endpoint on a tie. -/
def choose (value : Nat → ℚ) (query : ℚ) (lower : Nat) : Nat :=
  if 2 * query < value lower + value (lower + 1) then lower
  else if value lower + value (lower + 1) < 2 * query then lower + 1
  else if lower % 2 = 0 then lower else lower + 1

theorem choose_endpoints (value : Nat → ℚ) (query : ℚ) (lower : Nat) :
    choose value query lower = lower ∨ choose value query lower = lower + 1 := by
  unfold choose
  split_ifs <;> simp

theorem lower_nearest (value : Nat → ℚ) (increasing : StrictMono value) (query : ℚ) (lower : Nat)
    (left : value lower ≤ query) (midpoint : 2 * query ≤ value lower + value (lower + 1)) :
    ∀ candidate, |query - value lower| ≤ |query - value candidate| := by
  intro candidate
  rw [abs_of_nonneg (sub_nonneg.mpr left)]
  by_cases before : candidate ≤ lower
  · have below := increasing.monotone before
    rw [abs_of_nonneg (by linarith : 0 ≤ query - value candidate)]
    linarith
  · have above := increasing.monotone (by omega : lower + 1 ≤ candidate)
    have gap := increasing (Nat.lt_succ_self lower)
    rw [abs_of_nonpos (by linarith : query - value candidate ≤ 0)]
    linarith

theorem upper_nearest (value : Nat → ℚ) (increasing : StrictMono value) (query : ℚ) (lower : Nat)
    (midpoint : value lower + value (lower + 1) ≤ 2 * query) (right : query ≤ value (lower + 1)) :
    ∀ candidate, |query - value (lower + 1)| ≤ |query - value candidate| := by
  intro candidate
  rw [abs_of_nonpos (sub_nonpos.mpr right)]
  by_cases before : candidate ≤ lower
  · have below := increasing.monotone before
    have gap := increasing (Nat.lt_succ_self lower)
    rw [abs_of_nonneg (by linarith : 0 ≤ query - value candidate)]
    linarith
  · have above := increasing.monotone (by omega : lower + 1 ≤ candidate)
    rw [abs_of_nonpos (by linarith : query - value candidate ≤ 0)]
    linarith

theorem lower_tie (value : Nat → ℚ) (increasing : StrictMono value) (query : ℚ) (lower candidate : Nat)
    (left : value lower ≤ query) (midpoint : 2 * query ≤ value lower + value (lower + 1))
    (tie : |query - value lower| = |query - value candidate|) :
    candidate = lower ∨ (2 * query = value lower + value (lower + 1) ∧ candidate = lower + 1) := by
  rw [abs_of_nonneg (sub_nonneg.mpr left)] at tie
  by_cases before : candidate ≤ lower
  · have below := increasing.monotone before
    rw [abs_of_nonneg (by linarith : 0 ≤ query - value candidate)] at tie
    exact Or.inl (increasing.injective (by linarith))
  · have above := increasing.monotone (by omega : lower + 1 ≤ candidate)
    have gap := increasing (Nat.lt_succ_self lower)
    rw [abs_of_nonpos (by linarith : query - value candidate ≤ 0)] at tie
    exact Or.inr ⟨by linarith, increasing.injective (by linarith)⟩

theorem upper_tie (value : Nat → ℚ) (increasing : StrictMono value) (query : ℚ) (lower candidate : Nat)
    (midpoint : value lower + value (lower + 1) ≤ 2 * query) (right : query ≤ value (lower + 1))
    (tie : |query - value (lower + 1)| = |query - value candidate|) :
    candidate = lower + 1 ∨ (2 * query = value lower + value (lower + 1) ∧ candidate = lower) := by
  rw [abs_of_nonpos (sub_nonpos.mpr right)] at tie
  by_cases before : candidate ≤ lower
  · have below := increasing.monotone before
    have gap := increasing (Nat.lt_succ_self lower)
    rw [abs_of_nonneg (by linarith : 0 ≤ query - value candidate)] at tie
    exact Or.inr ⟨by linarith, increasing.injective (by linarith)⟩
  · have above := increasing.monotone (by omega : lower + 1 ≤ candidate)
    rw [abs_of_nonpos (by linarith : query - value candidate ≤ 0)] at tie
    exact Or.inl (increasing.injective (by linarith))

/-- Selection implements the independent global nearest-even specification. -/
theorem choose_correct (value : Nat → ℚ) (increasing : StrictMono value) (query : ℚ) (lower : Nat)
    (left : value lower ≤ query) (right : query ≤ value (lower + 1)) :
    NearestEven value query (choose value query lower) := by
  unfold choose
  split
  next below =>
    refine ⟨lower_nearest value increasing query lower left below.le, ?_⟩
    intro candidate tie
    rcases lower_tie value increasing query lower candidate left below.le tie with same | ⟨equal, _⟩
    · exact Or.inr same
    · linarith
  next notBelow =>
    split
    next above =>
      refine ⟨upper_nearest value increasing query lower above.le right, ?_⟩
      intro candidate tie
      rcases upper_tie value increasing query lower candidate above.le right tie with same | ⟨equal, _⟩
      · exact Or.inr same
      · linarith
    next notAbove =>
      have equal : 2 * query = value lower + value (lower + 1) := by linarith
      split
      next even =>
        exact ⟨lower_nearest value increasing query lower left equal.le, fun _ _ => Or.inl even⟩
      next odd =>
        exact ⟨upper_nearest value increasing query lower equal.ge right, fun _ _ => Or.inl (by omega)⟩

/-- A specified left endpoint is chosen exactly according to its midpoint
and parity test. -/
theorem choose_lower (value : Nat → ℚ) (query : ℚ) (lower : Nat)
    (bound : 2 * query ≤ value lower + value (lower + 1))
    (tieEven : 2 * query = value lower + value (lower + 1) → lower % 2 = 0) :
    choose value query lower = lower := by
  unfold choose
  split
  next below => rfl
  next notBelow =>
    have equal : 2 * query = value lower + value (lower + 1) := by linarith
    simp [equal, tieEven equal]

theorem choose_upper (value : Nat → ℚ) (query : ℚ) (lower : Nat)
    (bound : value lower + value (lower + 1) ≤ 2 * query)
    (tieEven : 2 * query = value lower + value (lower + 1) → (lower + 1) % 2 = 0) :
    choose value query lower = lower + 1 := by
  unfold choose
  split
  next below => linarith
  next notBelow =>
    split
    next above => rfl
    next notAbove =>
      have equal : 2 * query = value lower + value (lower + 1) := by linarith
      have odd : lower % 2 ≠ 0 := by have := tieEven equal; omega
      simp [odd]

end Silmaril.Numeric.Ieee754.AdjacentRounding
