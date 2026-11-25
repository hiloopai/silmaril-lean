module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies

/-! # Stability of continuation families under native substitution -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem LSubst.ValueFamily.id (Γ : VCtx τ) (L : LCtx τ) :
    LSubst.ValueFamily (Φ := Φ) Γ L L labelId :=
  fun _ _ h => .br h (.var rfl)

/-- Weaken the captures of a continuation family while keeping its payload binder. -/
theorem LSubst.ValueFamily.liftVars {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) (A : τ) :
    LSubst.ValueFamily (A :: Γ) L K (liftLSubstVars σ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.valueFamily_liftVars hσ A

/-- Preserve a prefix of local labels while replacing the outward continuations. -/
theorem LSubst.ValueFamily.append {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) (R : LCtx τ) :
    LSubst.ValueFamily Γ (R ++ L) (R ++ K) (liftLSubstN R.length σ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.valueFamily_append hσ R

/-- Replacing the exits of a value-branch region by value-branch continuations
preserves value branches. -/
theorem ValueBranches.lsubst {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {σ : Nat → Region Φ} (hσ : LSubst.ValueFamily Γ L K σ) :
    ValueBranches Γ (r.lsubst σ) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.valueBranches_lsubst hr hσ

theorem LSubst.ValueFamily.comp {Γ : VCtx τ} {L K P : LCtx τ} {σ υ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) (hυ : LSubst.ValueFamily Γ K P υ) :
    LSubst.ValueFamily Γ L P (compLSubst σ υ) :=
  fun _ A h => Proofs.SSA.Isotope.LambdaSSA.Rewrite.valueBranches_lsubst (hσ h)
    (Proofs.SSA.Isotope.LambdaSSA.Rewrite.valueFamily_liftVars hυ A)

end Silmaril.Isotope.LambdaSSA.Region
