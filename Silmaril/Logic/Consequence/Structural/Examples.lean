module

public import Silmaril.Logic.Consequence.Structural.Thms

/-!
# Examples: structural closures of small list-sequent relations

* A successor relation `[n] ⊢ n + 1` closed under reflexivity, cut and sublist weakening derives
  `[0, 7] ⊢ 2` (two cuts and a weakening).
* Sublist weakening plus exchange does not give contraction: the closure of `[0, 0] ⊢ 1` under
  `WeakSubperm` (`weakRules List.Subperm`) never derives `[0] ⊢ 1`, while the Tarski closure
  (weakening along `⊆`) does.
-/

@[expose] public section

namespace Silmaril.Consequence.Structural.Examples

/-- `[n] ⊢ n + 1`. -/
def succ : Rel Nat := fun Γ c => ∃ n, Γ = [n] ∧ c = n + 1

theorem succ_derives_two : Derives (jointRules List.Sublist) succ [0, 7] 2 := by
  have h1 : Derives (jointRules List.Sublist) succ [0] 1 := .base ⟨0, rfl, rfl⟩
  have h2 : Derives (jointRules List.Sublist) succ [1] 2 := .base ⟨1, rfl, rfl⟩
  have h : Derives (jointRules List.Sublist) succ ([0] ++ []) 2 := Derives.cut1 h1 h2
  exact Derives.weaken (by decide) h

/-- `[0, 0] ⊢ 1`, nothing else. -/
def twice : Rel Nat := fun Γ c => Γ = [0, 0] ∧ c = 1

/-- Derivations under sub-permutation weakening keep a sub-permutation of a base premise list. -/
theorem twice_subperm {Γ : List Nat} {c : Nat} (h : Derives (weakRules List.Subperm) twice Γ c) :
    [0, 0].Subperm Γ := by
  induction h with
  | base h => exact h.1 ▸ List.Subperm.refl _
  | refl h => exact h.elim
  | weak hw _ ih => exact ih.trans hw
  | cut _ h => exact h.elim

/-- Sub-permutation weakening (hence weakening along sublists, and exchange) does not give
contraction. -/
theorem subperm_closure_not_contraction :
    ¬ Contraction (Derives (weakRules List.Subperm) twice) := fun h =>
  absurd (twice_subperm (@h 0 [] 1 (.base ⟨rfl, rfl⟩))).length_le (by decide)

/-- The Tarski closure contracts. -/
theorem twice_tarski_contracts : Derives tarskiRules twice [0] 1 :=
  .weak (show [0, 0] ⊆ [0] by decide) (.base ⟨rfl, rfl⟩)

end Silmaril.Consequence.Structural.Examples
