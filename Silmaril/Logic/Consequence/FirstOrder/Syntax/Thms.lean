module

public import Silmaril.Logic.Consequence.FirstOrder.Syntax.Defs
import Silmaril.Proofs.Logic.Consequence.FirstOrder.Syntax

/-!
# Unsorted first-order renaming and substitution: satisfaction

* `holds_rename`, `holds_subst`: renaming or substituting, then evaluating, is evaluating in the
  composed assignment.
* `Formula.map_inst`, `Formula.map_shift`: signature morphisms commute with them.
* `holds_shift`: an unused variable does not matter; `holds_inst`: `φ[t]` holds when `φ` holds
  with the innermost variable at the value of `t`.
-/

@[expose] public section

namespace Silmaril.Logic.Institution.Examples.UFOL

variable {Sg : Signature} (M : Structure Sg)

theorem Formula.holds_rename {k m : ℕ} (ρ : Fin k → Fin m) (φ : Formula Sg k)
    (η : Fin m → M.carrier) : (φ.rename ρ).Holds M η ↔ φ.Holds M (η ∘ ρ) :=
  Silmaril.Proofs.Logic.Consequence.FirstOrder.Syntax.holds_rename M ρ φ η

theorem Formula.holds_subst {k m : ℕ} (σ : Fin k → Term Sg m) (φ : Formula Sg k)
    (η : Fin m → M.carrier) : (φ.subst σ).Holds M η ↔ φ.Holds M fun i => (σ i).eval M η :=
  Silmaril.Proofs.Logic.Consequence.FirstOrder.Syntax.holds_subst M σ φ η

theorem Formula.holds_shift {k : ℕ} (φ : Formula Sg k) (η : Fin k → M.carrier) (x : M.carrier) :
    φ.shift.Holds M (Fin.cons x η) ↔ φ.Holds M η :=
  Silmaril.Proofs.Logic.Consequence.FirstOrder.Syntax.holds_shift M φ η x

theorem Formula.holds_inst {k : ℕ} (φ : Formula Sg (k + 1)) (t : Term Sg k)
    (η : Fin k → M.carrier) : (φ.inst t).Holds M η ↔ φ.Holds M (Fin.cons (t.eval M η) η) :=
  Silmaril.Proofs.Logic.Consequence.FirstOrder.Syntax.holds_inst M φ t η

/-- Signature morphisms commute with instantiation. -/
theorem Formula.map_inst {Sg' : Signature} (σ : Sg ⟶ Sg') {k : ℕ} (φ : Formula Sg (k + 1))
    (t : Term Sg k) : (φ.inst t).map σ = (φ.map σ).inst (t.map σ) :=
  Silmaril.Proofs.Logic.Consequence.FirstOrder.Syntax.formula_map_inst σ φ t

/-- Signature morphisms commute with shifting. -/
theorem Formula.map_shift {Sg' : Signature} (σ : Sg ⟶ Sg') {k : ℕ} (φ : Formula Sg k) :
    φ.shift.map σ = (φ.map σ).shift :=
  Silmaril.Proofs.Logic.Consequence.FirstOrder.Syntax.formula_map_shift σ φ

end Silmaril.Logic.Institution.Examples.UFOL
