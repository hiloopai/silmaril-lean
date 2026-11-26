module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Defs
public import Silmaril.SSA.Isotope.Bridge.CaseSSA.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InstructionMap

/-! # Primitive relabelling of branch normalization and typed Paper rewrites -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region

universe u v w

variable {Φ : Type u} {Ψ : Type v} (f : Φ → Ψ)

theorem mapInstr_bindBranchArguments (r : Region Φ) :
    r.bindBranchArguments.mapInstr f = (r.mapInstr f).bindBranchArguments :=
  mapInstr_bindBranchArguments_proof f r

theorem mapInstr_lsubst (r : Region Φ) (σ : Nat → Region Φ) :
    (r.lsubst σ).mapInstr f = (r.mapInstr f).lsubst (fun i => (σ i).mapInstr f) :=
  mapInstr_lsubst_proof f r σ

theorem mapInstr_liftLSubstVars (σ : Nat → Region Φ) :
    (fun i => (liftLSubstVars σ i).mapInstr f) = liftLSubstVars (fun i => (σ i).mapInstr f) :=
  mapInstr_liftLSubstVars_proof f σ

theorem mapInstr_returnRegion (a : Tm Φ) :
    (CfgEta.TypeCategory.returnRegion a).mapInstr f = CfgEta.TypeCategory.returnRegion (a.mapInstr f) :=
  mapInstr_returnRegion_proof f a

theorem mapInstr_iterateRegion {τ : Type w} (A : τ) (r : Region Φ) :
    (SyntacticCategory.iterateRegion A r).mapInstr f = SyntacticCategory.iterateRegion A (r.mapInstr f) :=
  mapInstr_iterateRegion_proof f A r

variable {τ : Type w} [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ]
  {f} (types : InstructionMap.PreservesTypes (τ := τ) f)
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

include types

theorem ValueBranches.mapInstr (h : ValueBranches Γ r L) :
    ValueBranches Γ (r.mapInstr f) L :=
  ValueBranches.mapInstr_proof types h

theorem Paper.Extension.Eqv.mapInstr
    {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {Target : VCtx τ → Region Ψ → Region Ψ → LCtx τ → Prop}
    (seedMap : ∀ {Γ r s L}, Seed Γ r s L → Target Γ (r.mapInstr f) (s.mapInstr f) L)
    (h : Paper.Extension.Eqv Seed Γ r s L) :
    Paper.Extension.Eqv Target Γ (r.mapInstr f) (s.mapInstr f) L :=
  Paper.Extension.Eqv.mapInstr_proof types seedMap h

end Silmaril.Isotope.LambdaSSA.Region
