module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.AbstractInterpretation

/-! # Exercise sheet 2, question 1 (interval abstract interpretation)

Source: `cam-optcomp-2025-exercise-sheet-2` in `references.bib`, question 1.


(a) Abstract interpretation computes with abstract values (here intervals)
standing for sets of concrete values (`Interval.γ`), using abstract operations
(`Interval.add`, `Interval.sub`). It is *safe* when the concrete result always
lies in the concretisation of the abstract result (`Interval.add_sound`,
`Interval.sub_sound`); it may be imprecise, so a property shown abstractly holds
concretely but not conversely.

(b) `gAbs_eq`: `α(g) = [3lx − hy, 3hx − ly]`; `gAbs_sound` is its safety.
(c) `gAbs_example`: `α(g) = [13, 30]`, so `g` cannot return `0`
(`g_ne_zero`).
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S2Q1

open AbstractInterpretation

/-- The concrete function `g`. -/
def g (x y : ℤ) : ℤ := (x + x) + (x - y)

/-- Its abstract interpretation over intervals. -/
def gAbs (I J : Interval) : Interval := (I.add I).add (I.sub J)

/-- (b) The interval of `g`. -/
theorem gAbs_eq (I J : Interval) : gAbs I J = ⟨3 * I.lo - J.hi, 3 * I.hi - J.lo⟩ := by
  show (⟨I.lo + I.lo + (I.lo - J.hi), I.hi + I.hi + (I.hi - J.lo)⟩ : Interval) = _
  congr 1 <;> omega

/-- (b) Safety. -/
theorem gAbs_sound {I J : Interval} {x y : ℤ} (hx : x ∈ I.γ) (hy : y ∈ J.γ) :
    g x y ∈ (gAbs I J).γ :=
  Interval.add_sound (Interval.add_sound hx hx) (Interval.sub_sound hx hy)

/-- (c) With `α(x) = [5, 10]` and `α(y) = [0, 2]`, `α(g) = [13, 30]`. -/
theorem gAbs_example : gAbs ⟨5, 10⟩ ⟨0, 2⟩ = ⟨13, 30⟩ := by
  decide

/-- (c) Hence `g` cannot return `0`. -/
theorem g_ne_zero {x y : ℤ} (hx : x ∈ (⟨5, 10⟩ : Interval).γ) (hy : y ∈ (⟨0, 2⟩ : Interval).γ) :
    g x y ≠ 0 := by
  have h := gAbs_sound hx hy
  rw [gAbs_example] at h
  have h₁ : (13 : ℤ) ≤ g x y := h.1
  omega

end Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S2Q1
