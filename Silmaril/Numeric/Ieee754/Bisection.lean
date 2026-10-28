module

public import Mathlib.Order.Monotone.Basic

/-! # Finite bisection in an ordered sequence

The executable search halves a finite natural-index interval. Its correctness
requires endpoint bracketing, with monotonicity needed only for uniqueness.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Bisection

variable {α : Type*} [LinearOrder α]

/-- Last index at or below the query, within the supplied bracketing interval. -/
def lastLE (value : Nat → α) (query : α) (lower upper : Nat) : Nat :=
  if lower + 1 < upper then
    let middle := (lower + upper) / 2
    if value middle ≤ query then lastLE value query middle upper
    else lastLE value query lower middle
  else lower
termination_by upper - lower
decreasing_by all_goals omega

theorem lastLE_spec (value : Nat → α) (query : α) (lower upper : Nat)
    (ordered : lower < upper) (left : value lower ≤ query) (right : query < value upper) :
    lower ≤ lastLE value query lower upper ∧ lastLE value query lower upper < upper ∧
      value (lastLE value query lower upper) ≤ query ∧
      query < value (lastLE value query lower upper + 1) := by
  rw [lastLE]
  split
  next wide =>
    let middle := (lower + upper) / 2
    have middleLower : lower < middle := by dsimp only [middle]; omega
    have middleUpper : middle < upper := by dsimp only [middle]; omega
    dsimp only
    split
    next below =>
      obtain ⟨lo, hi, le, lt⟩ := lastLE_spec value query middle upper middleUpper below right
      exact ⟨middleLower.le.trans lo, hi, le, lt⟩
    next above =>
      obtain ⟨lo, hi, le, lt⟩ := lastLE_spec value query lower middle middleLower left (lt_of_not_ge above)
      exact ⟨lo, hi.trans middleUpper, le, lt⟩
  next narrow =>
    have next : lower + 1 = upper := by omega
    exact ⟨le_rfl, ordered, left, by simpa only [next] using right⟩
termination_by upper - lower
decreasing_by all_goals omega

/-- Strictly increasing sequences have only one bracket for a query. -/
theorem bracket_unique (value : Nat → α) (increasing : StrictMono value) (query : α)
    {left right : Nat} (ll : value left ≤ query) (lr : query < value (left + 1))
    (rl : value right ≤ query) (rr : query < value (right + 1)) : left = right := by
  by_contra different
  rcases lt_or_gt_of_ne different with less | greater
  · have boundary := increasing.monotone (by omega : left + 1 ≤ right)
    exact (not_lt_of_ge (boundary.trans rl)) lr
  · have boundary := increasing.monotone (by omega : right + 1 ≤ left)
    exact (not_lt_of_ge (boundary.trans ll)) rr

theorem lastLE_eq (value : Nat → α) (increasing : StrictMono value) (query : α)
    (lower upper : Nat) (ordered : lower < upper)
    (left : value lower ≤ query) (right : query < value upper)
    (expected : Nat) (el : value expected ≤ query) (er : query < value (expected + 1)) :
    lastLE value query lower upper = expected := by
  obtain ⟨_, _, ll, lr⟩ := lastLE_spec value query lower upper ordered left right
  exact bracket_unique value increasing query ll lr el er

end Silmaril.Numeric.Ieee754.Bisection
