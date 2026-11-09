module

public import Silmaril.Project.Room.Defs

/-!
# Rooms as problems: the answers are the classical questions

The THM answer of `Problem R φ` is validity (`R.Entails ∅ φ`), and that of `Consequence R Γ φ`
is semantic consequence `R.Entails Γ φ`.
-/

@[expose] public section

namespace Silmaril.Project.Room

open Silmaril.Logic.Institution

universe w m₁ m₂

variable {R : Room.{w, m₁, m₂}}

/-- THM of `Consequence R Γ φ` is `Γ ⊨ φ`. -/
theorem consequence_thm_iff (Γ : Set R.Sen) (φ : R.Sen) :
    (∀ M, Consequence R Γ φ M) ↔ R.Entails Γ φ := Iff.rfl

/-- THM of `Problem R φ` is validity: `∅ ⊨ φ`. -/
theorem problem_thm_iff (φ : R.Sen) : (∀ M, Problem R φ M) ↔ R.Entails ∅ φ := by
  simp [Problem, Room.Entails]

/-- SAT of `Problem R φ` is satisfiability: some model of `φ`. -/
theorem problem_sat_iff (φ : R.Sen) : (∃ M, Problem R φ M) ↔ (R.modelsOf {φ}).Nonempty := by
  simp [Problem, Room.modelsOf, Set.Nonempty]

end Silmaril.Project.Room
