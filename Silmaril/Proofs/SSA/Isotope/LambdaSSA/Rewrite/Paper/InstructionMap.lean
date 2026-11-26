module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Defs
public import Silmaril.SSA.Isotope.Bridge.CaseSSA.Thms

/-! # Relabelling the underlying typed Paper derivations -/

public section

open Silmaril
namespace Silmaril.Isotope.LambdaSSA

universe u v w

variable {Φ : Type u} {Ψ : Type v} (f : Φ → Ψ)

theorem Tm.mapInstr_consSubst (a : Tm Φ) (σ : Nat → Tm Φ) :
    (fun i => (Tm.consSubst a σ i).mapInstr f) =
      Tm.consSubst (a.mapInstr f) (fun i => (σ i).mapInstr f) := by
  funext i
  cases i <;> rfl

private theorem Tm.mapInstr_liftSubst (σ : Nat → Tm Φ) :
    (fun i => (Tm.liftSubst σ i).mapInstr f) =
      Tm.liftSubst (fun i => (σ i).mapInstr f) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact Tm.mapInstr_rename f (σ i) Nat.succ

private theorem Tm.mapInstr_liftSubstN (n : Nat) (σ : Nat → Tm Φ) :
    (fun i => (Tm.liftSubstN n σ i).mapInstr f) =
      Tm.liftSubstN n (fun i => (σ i).mapInstr f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Tm.liftSubstN, Tm.mapInstr_liftSubst, ih]

theorem Tm.mapInstr_subst (a : Tm Φ) (σ : Nat → Tm Φ) :
    (a.subst σ).mapInstr f = (a.mapInstr f).subst (fun i => (σ i).mapInstr f) := by
  induction a generalizing σ <;>
    simp_all only [Tm.subst, Tm.mapInstr, Tm.mapInstr_liftSubst, Tm.mapInstr_liftSubstN]

namespace Region

theorem mapInstr_substVars (r : Region Φ) (σ : Nat → Tm Φ) :
    (r.substVars σ).mapInstr f = (r.mapInstr f).substVars (fun i => (σ i).mapInstr f) := by
  induction r generalizing σ <;>
    simp_all only [substVars, mapInstr, Tm.mapInstr_subst, Tm.mapInstr_liftSubst, Tm.mapInstr_liftSubstN]

theorem mapInstr_liftLSubstVars_proof (σ : Nat → Region Φ) :
    (fun i => (liftLSubstVars σ i).mapInstr f) = liftLSubstVars (fun i => (σ i).mapInstr f) := by
  funext i
  exact mapInstr_renameVars f (σ i) _

private theorem mapInstr_liftLSubst (σ : Nat → Region Φ) :
    (fun i => (liftLSubst σ i).mapInstr f) = liftLSubst (fun i => (σ i).mapInstr f) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact mapInstr_renameLabels f (σ i) _

private theorem mapInstr_liftLSubstN (n : Nat) (σ : Nat → Region Φ) :
    (fun i => (liftLSubstN n σ i).mapInstr f) = liftLSubstN n (fun i => (σ i).mapInstr f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftLSubstN, mapInstr_liftLSubst, ih]

theorem mapInstr_lsubst_proof (r : Region Φ) (σ : Nat → Region Φ) :
    (r.lsubst σ).mapInstr f = (r.mapInstr f).lsubst (fun i => (σ i).mapInstr f) := by
  induction r generalizing σ <;>
    simp_all only [lsubst, mapInstr, mapInstr_substVars, Tm.mapInstr_consSubst, Tm.mapInstr,
      mapInstr_liftLSubstVars_proof, mapInstr_liftLSubstN]

theorem mapInstr_bindBranchArguments_proof (r : Region Φ) :
    r.bindBranchArguments.mapInstr f = (r.mapInstr f).bindBranchArguments := by
  induction r <;> simp_all only [bindBranchArguments, mapInstr, Tm.mapInstr]

theorem mapInstr_returnRegion_proof (a : Tm Φ) :
    (CfgEta.TypeCategory.returnRegion a).mapInstr f = CfgEta.TypeCategory.returnRegion (a.mapInstr f) := by
  induction a <;> simp_all only [CfgEta.TypeCategory.returnRegion, Region.mapInstr, Tm.mapInstr, mapInstr_lsubst_proof]

theorem mapInstr_iterateRegion_proof {τ : Type w} (A : τ) (r : Region Φ) :
    (SyntacticCategory.iterateRegion A r).mapInstr f = SyntacticCategory.iterateRegion A (r.mapInstr f) := by
  simp only [SyntacticCategory.iterateRegion, feedbackRegion, cfgEntryContinuations, mapInstr,
    mapInstr_renameVars, SyntacticCategory.iterationBody, mapInstr_lsubst_proof]
  rfl

end Region

variable {τ : Type w} [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ]
  {Γ : VCtx τ} {L K : LCtx τ} {A : τ} {a : Tm Φ} {r s : Region Φ}

omit [HasTy Φ τ] [HasTy Ψ τ] in
theorem Tm.BranchValue.mapInstr (h : Tm.BranchValue Γ a A) :
    Tm.BranchValue Γ (a.mapInstr f) A := by
  induction h with
  | var hi => exact .var hi
  | unit => exact .unit
  | pair _ _ h₁ h₂ => exact .pair h₁ h₂
  | inl _ h => exact .inl h
  | inr _ h => exact .inr h

namespace Region

variable {f} (types : InstructionMap.PreservesTypes (τ := τ) f)
include types

theorem ValueBranches.mapInstr_proof (h : ValueBranches Γ r L) :
    ValueBranches Γ (r.mapInstr f) L := by
  induction h with
  | br hℓ ha => exact .br hℓ (ha.mapInstr f)
  | let₁ ha _ ih => exact .let₁ (ha.mapInstr f types) ih
  | let₂ ha _ ih => exact .let₂ (ha.mapInstr f types) ih
  | case ha _ _ ih₁ ih₂ => exact .case (ha.mapInstr f types) ih₁ ih₂
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb

theorem LSubst.HasType.mapInstr {σ : Nat → Region Φ} (h : LSubst.HasType Γ L K σ) :
    LSubst.HasType Γ L K (fun i => (σ i).mapInstr f) :=
  fun {_ _} hi => (h hi).mapInstr f types

end Region
end Silmaril.Isotope.LambdaSSA

namespace Silmaril.Isotope.LambdaSSA.Region

universe u v w

variable {τ : Type w} [TypeFormers τ] {Φ : Type u} {Ψ : Type v} [HasTy Φ τ] [HasTy Ψ τ]
  {f : Φ → Ψ} (types : InstructionMap.PreservesTypes (τ := τ) f)
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

include types

theorem CfgEquiv.mapInstr (h : CfgEquiv Γ r s L) : CfgEquiv Γ (r.mapInstr f) (s.mapInstr f) L := by
  induction h with
  | refl hr => exact .refl (hr.mapInstr f types)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ (ha.mapInstr f types) ih
  | let₂ ha _ ih => exact .let₂ (ha.mapInstr f types) ih
  | case ha _ _ ih₁ ih₂ => exact .case (ha.mapInstr f types) ih₁ ih₂
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | cfgZero he bs => exact .cfgZero (he.mapInstr f types) (fun i => (bs i).mapInstr f)
  | cfgBrExit R hℓ ha hb => exact .cfgBrExit R hℓ (ha.mapInstr f) (fun i => (hb i).mapInstr f types)
  | cfgBrLocal R i ha hb => exact .cfgBrLocal R i (ha.mapInstr f) (fun j => (hb j).mapInstr f types)

theorem RewriteEquiv.mapInstr (h : RewriteEquiv Γ r s L) :
    RewriteEquiv Γ (r.mapInstr f) (s.mapInstr f) L := by
  induction h with
  | entry h => exact .entry (h.mapInstr types)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ (ha.mapInstr f types) ih
  | let₂ ha _ ih => exact .let₂ (ha.mapInstr f types) ih
  | case ha _ _ ih₁ ih₂ => exact .case (ha.mapInstr f types) ih₁ ih₂
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | letBr ha hb hℓ =>
    simpa only [Region.mapInstr, Tm.mapInstr_subst, Tm.mapInstr_consSubst, Tm.mapInstr] using
      RewriteEquiv.letBr (ha.mapInstr f) (hb.mapInstr f) hℓ
  | caseInl ha hl hr => exact .caseInl (ha.mapInstr f types) (hl.mapInstr f types) (hr.mapInstr f types)
  | caseInr hb hl hr => exact .caseInr (hb.mapInstr f types) (hl.mapInstr f types) (hr.mapInstr f types)

omit [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ] types in
private theorem mapInstr_caseCfg (a : Tm Φ) (r s : Region Φ) :
    (Region.caseCfg a r s).mapInstr f = Region.caseCfg (a.mapInstr f) (r.mapInstr f) (s.mapInstr f) := by
  simp only [Region.caseCfg, Region.mapInstr, Tm.mapInstr, mapInstr_renameLabels, Region.cfg.injEq,
    true_and]
  apply heq_of_eq
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem SubstitutionEquiv.mapInstr (h : SubstitutionEquiv Γ r s L) :
    SubstitutionEquiv Γ (r.mapInstr f) (s.mapInstr f) L := by
  induction h with
  | base h => exact .base (h.mapInstr types)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ (ha.mapInstr f types) ih
  | let₂ ha _ ih => exact .let₂ (ha.mapInstr f types) ih
  | case ha _ _ ih₁ ih₂ => exact .case (ha.mapInstr f types) ih₁ ih₂
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | letValue ha hr =>
    simpa only [Region.mapInstr, mapInstr_substVars, Tm.mapInstr_consSubst, Tm.mapInstr] using
      SubstitutionEquiv.letValue (ha.mapInstr f) (hr.mapInstr f types)
  | caseValue ha hr =>
    simpa only [Region.mapInstr, mapInstr_substVars, Tm.mapInstr_consSubst, Tm.replaceNewest, Tm.mapInstr, Function.comp_apply, Tm.singleSubst] using!
      SubstitutionEquiv.caseValue (ha.mapInstr f) (hr.mapInstr f types)
  | caseCfg ha hl hr =>
    simpa only [Region.mapInstr, mapInstr_caseCfg] using
      SubstitutionEquiv.caseCfg (ha.mapInstr f types) (hl.mapInstr f types) (hr.mapInstr f types)
  | initial ha hr hs => exact .initial (ha.mapInstr f) (hr.mapInstr f types) (hs.mapInstr f types)
  | cfgOutward R hr hb =>
    simpa only [Region.mapInstr, mapInstr_renameLabels] using
      SubstitutionEquiv.cfgOutward R (hr.mapInstr f types) (fun i => (hb i).mapInstr f types)

omit [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ] types in
private theorem mapInstr_reentry (r : Region Φ) :
    (fun i => (CfgEta.reentry r i).mapInstr f) = CfgEta.reentry (r.mapInstr f) := by
  funext i
  simp only [CfgEta.reentry, cfgEntryContinuations, Region.mapInstr, Tm.mapInstr, mapInstr_renameVars]

omit [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ] types in
private theorem mapInstr_singleCfg (r s : Region Φ) :
    (CfgEta.singleCfg r s).mapInstr f = CfgEta.singleCfg (r.mapInstr f) (s.mapInstr f) := rfl

theorem CfgEta.Eqv.mapInstr (h : CfgEta.Eqv Γ r s L) : CfgEta.Eqv Γ (r.mapInstr f) (s.mapInstr f) L := by
  induction h with
  | native h => exact .native (h.mapInstr types)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ (ha.mapInstr f types) ih
  | let₂ ha _ ih => exact .let₂ (ha.mapInstr f types) ih
  | case ha _ _ ih₁ ih₂ => exact .case (ha.mapInstr f types) ih₁ ih₂
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | etaPost he hb hσ =>
    simpa only [mapInstr_lsubst_proof, mapInstr_singleCfg, mapInstr_reentry] using
      CfgEta.Eqv.etaPost (he.mapInstr_proof types) (hb.mapInstr_proof types) (hσ.mapInstr types)

omit [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ] types in
private theorem mapInstr_localMap (a : Tm Φ) :
    (fun i => (CfgEta.Uniformity.localMap a i).mapInstr f) = CfgEta.Uniformity.localMap (a.mapInstr f) := by
  funext i
  cases i <;> rfl

theorem Paper.Eqv.mapInstr (h : Paper.Eqv Γ r s L) : Paper.Eqv Γ (r.mapInstr f) (s.mapInstr f) L := by
  induction h with
  | cfgEta h => exact .cfgEta (h.mapInstr types)
  | productBeta h =>
    cases h with
    | let₂Beta ha hb hr =>
      simpa only [Region.mapInstr, Tm.mapInstr, mapInstr_substVars, Tm.mapInstr_consSubst, Tm.mapInstr] using
        Paper.Eqv.productBeta (.let₂Beta (ha.mapInstr f) (hb.mapInstr f) (hr.mapInstr f types))
  | productEta h =>
    cases h with
    | let₂Eta hi hℓ => exact .productEta (.let₂Eta hi hℓ)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ (ha.mapInstr f types) ih
  | let₂ ha _ ih => exact .let₂ (ha.mapInstr f types) ih
  | case ha _ _ ih₁ ih₂ => exact .case (ha.mapInstr f types) ih₁ ih₂
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | lsubstCongr hp _ ih =>
    simpa only [mapInstr_lsubst_proof] using Paper.Eqv.lsubstCongr (hp.mapInstr_proof types) (fun {_ _} hi => ih hi)
  | lsubstPost _ hr hs hσ ih =>
    simpa only [mapInstr_lsubst_proof] using Paper.Eqv.lsubstPost ih (hr.mapInstr_proof types) (hs.mapInstr_proof types)
      (hσ.mapInstr types)
  | substVars _ hθ ih =>
    simpa only [mapInstr_substVars] using Paper.Eqv.substVars ih (fun {_ _} hi => (hθ hi).mapInstr f)
  | renameLabels _ hρ ih =>
    simpa only [mapInstr_renameLabels] using Paper.Eqv.renameLabels ih hρ
  | collapsePost he hp hσ =>
    simpa only [mapInstr_lsubst_proof, CfgEta.Codiagonal.nested, CfgEta.Codiagonal.flattened, mapInstr_singleCfg,
      mapInstr_renameVars, mapInstr_renameLabels, Region.mapInstr, Tm.mapInstr] using
      Paper.Eqv.collapsePost (he.mapInstr_proof types) (hp.mapInstr_proof types) (hσ.mapInstr types)
  | uniform he hp hq ha _ ih =>
    simp only [mapInstr_lsubst_proof, mapInstr_liftLSubstVars_proof, mapInstr_localMap, Region.mapInstr] at ih
    simpa only [mapInstr_singleCfg, mapInstr_lsubst_proof, mapInstr_localMap] using
      Paper.Eqv.uniform (he.mapInstr_proof types) (hp.mapInstr_proof types) (hq.mapInstr f types) (ha.mapInstr f) ih

theorem Paper.Extension.Eqv.mapInstr_proof
    {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    {Target : VCtx τ → Region Ψ → Region Ψ → LCtx τ → Prop}
    (seedMap : ∀ {Γ r s L}, Seed Γ r s L → Target Γ (r.mapInstr f) (s.mapInstr f) L)
    (h : Paper.Extension.Eqv Seed Γ r s L) :
    Paper.Extension.Eqv Target Γ (r.mapInstr f) (s.mapInstr f) L := by
  induction h with
  | paper h => exact .paper (h.mapInstr types)
  | extra hr hs h => exact .extra (hr.mapInstr f types) (hs.mapInstr f types) (seedMap h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ (ha.mapInstr f types) ih
  | let₂ ha _ ih => exact .let₂ (ha.mapInstr f types) ih
  | case ha _ _ ih₁ ih₂ => exact .case (ha.mapInstr f types) ih₁ ih₂
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | lsubstCongr hp _ ih =>
    simpa only [mapInstr_lsubst_proof] using Paper.Extension.Eqv.lsubstCongr (hp.mapInstr_proof types)
      (fun {_ _} hi => ih hi)
  | lsubstPost _ hr hs hσ ih =>
    simpa only [mapInstr_lsubst_proof] using
      Paper.Extension.Eqv.lsubstPost ih (hr.mapInstr_proof types) (hs.mapInstr_proof types) (hσ.mapInstr types)
  | substVars _ hθ ih =>
    simpa only [mapInstr_substVars] using Paper.Extension.Eqv.substVars ih (fun {_ _} hi => (hθ hi).mapInstr f)
  | renameLabels _ hρ ih =>
    simpa only [mapInstr_renameLabels] using Paper.Extension.Eqv.renameLabels ih hρ

end Silmaril.Isotope.LambdaSSA.Region
