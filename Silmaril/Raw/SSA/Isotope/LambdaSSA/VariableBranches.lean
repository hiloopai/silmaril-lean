module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs

/-! # Regions whose branch arguments are variables -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LambdaSSA.Region

variable {Φ : Type u}

/-- Every branch passes a variable. This stronger syntactic discipline implies
pure branch arguments independently of the primitive instruction effects. -/
inductive VariableBranches : Region Φ → Prop where
  | br {ℓ i : Nat} : VariableBranches (.br ℓ (.var i))
  | case {a : Tm Φ} {l r : Region Φ} :
      VariableBranches l → VariableBranches r → VariableBranches (.case a l r)
  | let₁ {a : Tm Φ} {r : Region Φ} : VariableBranches r → VariableBranches (.let₁ a r)
  | let₂ {a : Tm Φ} {r : Region Φ} : VariableBranches r → VariableBranches (.let₂ a r)
  | cfg {e : Region Φ} {n : Nat} {bs : Fin n → Region Φ} :
      VariableBranches e → (∀ i, VariableBranches (bs i)) → VariableBranches (.cfg e n bs)

namespace VariableBranches

theorem renameVars {r : Region Φ} (hr : VariableBranches r) (ρ : Nat → Nat) :
    VariableBranches (r.renameVars ρ) := by
  induction hr generalizing ρ with
  | br => exact .br
  | case hl hr ihl ihr => exact .case (ihl _) (ihr _)
  | let₁ hr ih => exact .let₁ (ih _)
  | let₂ hr ih => exact .let₂ (ih _)
  | cfg he hb ihe ihb => exact .cfg (ihe _) (fun i => ihb i _)

theorem renameLabels {r : Region Φ} (hr : VariableBranches r) (ρ : Nat → Nat) :
    VariableBranches (r.renameLabels ρ) := by
  induction hr generalizing ρ with
  | br => exact .br
  | case hl hr ihl ihr => exact .case (ihl _) (ihr _)
  | let₁ hr ih => exact .let₁ (ih _)
  | let₂ hr ih => exact .let₂ (ih _)
  | cfg he hb ihe ihb => exact .cfg (ihe _) (fun i => ihb i _)

end VariableBranches
end Silmaril.Isotope.LambdaSSA.Region
