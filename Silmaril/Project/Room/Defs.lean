module

public import Silmaril.Logic.Institution.Room

/-!
# Rooms as problems

A room (silmaril's `Room`: sentences, a category of models, satisfaction `R.Sat M φ`) turns a
sentence into a **predicate over models**. Its four answers (`@[answers … thm|sat|uns|csa]` in
`Silmaril.Project`) are the classical questions about `φ`:

| answer | statement | reading |
|---|---|---|
| THM | `∀ M, R.Sat M φ` | `φ` is valid |
| SAT | `∃ M, R.Sat M φ` | `φ` is satisfiable |
| UNS | `∀ M, ¬ R.Sat M φ` | `φ` is unsatisfiable |
| CSA | `∃ M, ¬ R.Sat M φ` | `φ` has a countermodel |

"`m ⊨ φ`" for a given model is the instance `(M := m)`, and semantic consequence `Γ ⊨ φ` is the
THM answer of `Consequence R Γ φ` (`Silmaril.Project.Room.consequence_thm_iff`). So there is one
template per question shape and no extra problem kinds.
-/

@[expose] public section

namespace Silmaril.Project.Room

open Silmaril.Logic.Institution

universe w m₁ m₂

/-- `φ` in room `R`, as a predicate over models: `M ⊨ φ`. -/
def Problem (R : Room.{w, m₁, m₂}) (φ : R.Sen) (M : R.Mod) : Prop := R.Sat M φ

/-- Semantic consequence `Γ ⊨ φ`, as a predicate over models; its THM answer is
`R.Entails Γ φ`. -/
def Consequence (R : Room.{w, m₁, m₂}) (Γ : Set R.Sen) (φ : R.Sen) (M : R.Mod) : Prop :=
  (∀ ψ ∈ Γ, R.Sat M ψ) → R.Sat M φ

end Silmaril.Project.Room
