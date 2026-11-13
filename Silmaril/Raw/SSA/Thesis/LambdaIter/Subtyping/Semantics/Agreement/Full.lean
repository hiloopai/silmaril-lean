module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.Semantics.Agreement.Combinators


@[expose] public section

-- Source lakefile: autoImplicit (Lean default) on, relaxedAutoImplicit off.
set_option autoImplicit true
set_option relaxedAutoImplicit false
namespace Silmaril.Thesis.LambdaIter.Subtyping.Semantics

open Silmaril.Thesis.LambdaIter.LocallyNameless
open Silmaril.Thesis.LambdaIter.Subtyping.LocallyNameless

open _root_.CategoryTheory _root_.CategoryTheory.Limits Silmaril.Thesis.Elgot

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]

omit [DecidableEq ν] in
/-- The `Type` coproduct comparison undoes the categorical coproduct isomorphism of
`ofTypeModel` (port helper). -/
theorem ofTypeModel_coprodIso_hom_apply {A B : τ}
    (e : TypeModel.interp (TypeFormers.coprod A B : τ)) :
    (Types.binaryCoproductIso (TypeModel.interp A) (TypeModel.interp B)).hom
        (((Categorical.ofTypeModel (τ := τ)).coprodIso A B).hom e) =
      TypeModel.coprodEquiv A B e :=
  types_congr_hom (Iso.inv_hom_id (Types.binaryCoproductIso _ _)) _

/-- The abstract categorical semantics, specialized to the Kleisli category of the
monadic model, agrees pointwise with the direct monadic semantics. -/
theorem categorical_denote_eq {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    (Categorical.denoteOfType (ε := ε) (m := m) h).of
        (envToCategorical γ ρ) =
      denote (ε := ε) (m := m) h γ ρ := by
  let _ := Categorical.ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  -- port note: the thesis closed every case with one `simp` call; under the bundled
  -- `Type` morphisms of current Mathlib that normalisation no longer fires, so each case
  -- is an explicit chain of the evaluation lemmas of `Agreement/Iteration.lean` and
  -- `Agreement/Combinators.lean` and the monad laws.
  induction h with
  | fv h =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      exact congrArg (pure (f := m)) (freeLookup_toCategorical γ ρ _ h)
  | bv =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      exact congrArg (pure (f := m)) (boundVar_toCategorical γ ρ _)
  | op ha ih =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      refine (Categorical.kleisli_comp_of _ _ _).trans ?_
      exact congrArg (fun u => Bind.bind (m := m) u _) (ih ρ)
  | let₁ ha hb iha ihb =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      refine (Categorical.bind_of _ _ _).trans ?_
      refine (congrArg (fun u => Bind.bind (m := m) u _) (iha ρ)).trans ?_
      refine bind_congr fun a => ?_
      refine (Categorical.kleisli_comp_of _ _ _).trans ((pure_bind (m := m) _ _).trans ?_)
      exact ihb (ρ, a)
  | unit =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      rfl
  | pair ha hb iha ihb =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      refine (Categorical.kleisli_comp_of _ _ _).trans ?_
      refine (congrArg (fun u => Bind.bind (m := m) u _) (Categorical.pair_of _ _ _)).trans ?_
      refine (bind_assoc (m := m) _ _ _).trans ?_
      refine (congrArg (fun u => Bind.bind (m := m) u _) (iha ρ)).trans ?_
      refine bind_congr fun a => ?_
      refine (bind_assoc (m := m) _ _ _).trans ?_
      refine (congrArg (fun u => Bind.bind (m := m) u _) (ihb ρ)).trans ?_
      refine bind_congr fun b => ?_
      exact pure_bind (m := m) _ _
  | let₂ ha hc iha ihc =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      refine (Categorical.bind_of _ _ _).trans ?_
      refine (congrArg (fun u => Bind.bind (m := m) u _) (iha ρ)).trans ?_
      refine bind_congr fun ab => ?_
      refine (Categorical.kleisli_comp_of _ _ _).trans ((pure_bind (m := m) _ _).trans ?_)
      refine (Categorical.kleisli_comp_of _ _ _).trans ((pure_bind (m := m) _ _).trans ?_)
      exact ihc ((ρ, (TypeModel.tensorEquiv _ _ ab).1), (TypeModel.tensorEquiv _ _ ab).2)
  | inl ha ih =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      refine (Categorical.kleisli_comp_of _ _ _).trans ?_
      refine (congrArg (fun u => Bind.bind (m := m) u _) (ih ρ)).trans ?_
      refine bind_congr fun a => ?_
      exact congrArg (fun z => (pure ((TypeModel.coprodEquiv _ _).symm z) : m _))
        (types_congr_hom (Types.binaryCoproductIso_inl_comp_hom _ _) a)
  | inr hb ih =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      refine (Categorical.kleisli_comp_of _ _ _).trans ?_
      refine (congrArg (fun u => Bind.bind (m := m) u _) (ih ρ)).trans ?_
      refine bind_congr fun b => ?_
      exact congrArg (fun z => (pure ((TypeModel.coprodEquiv _ _).symm z) : m _))
        (types_congr_hom (Types.binaryCoproductIso_inr_comp_hom _ _) b)
  | case he hl hr ihe ihl ihr =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      refine (Categorical.caseWithContext_of _ _ _ _).trans ?_
      refine (congrArg (fun u => Bind.bind (m := m) u _)
        ((Categorical.kleisli_comp_of _ _ _).trans
          (congrArg (fun u => Bind.bind (m := m) u _) (ihe ρ)))).trans ?_
      refine (bind_assoc (m := m) _ _ _).trans ?_
      refine bind_congr fun e => ?_
      refine (pure_bind (m := m) _ _).trans ?_
      have hx := ofTypeModel_coprodIso_hom_apply (τ := τ) e
      split
      · rename_i a ha
        have h2 : TypeModel.coprodEquiv _ _ e = Sum.inl a := hx.symm.trans ha
        rw [h2]
        exact (Categorical.kleisli_comp_of _ _ _).trans
          ((pure_bind (m := m) _ _).trans (ihl (ρ, a)))
      · rename_i b hb
        have h2 : TypeModel.coprodEquiv _ _ e = Sum.inr b := hx.symm.trans hb
        rw [h2]
        exact (Categorical.kleisli_comp_of _ _ _).trans
          ((pure_bind (m := m) _ _).trans (ihr (ρ, b)))
  | abort ha ih =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      refine (Categorical.kleisli_comp_of _ _ _).trans ?_
      refine (congrArg (fun u => Bind.bind (m := m) u _) (ih ρ)).trans ?_
      refine bind_congr fun z => ?_
      exact Empty.elim (TypeModel.emptyEquiv z)
  | iter ha hb iha ihb =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      refine (Categorical.bind_of _ _ _).trans ?_
      refine (congrArg (fun u => Bind.bind (m := m) u _) (iha ρ)).trans ?_
      refine bind_congr fun a => ?_
      refine (Categorical.contextualLoop_of _ _ _).trans ?_
      refine congrArg (fun q => Silmaril.Thesis.Elgot.iter (m := m) q a) (funext fun x => ?_)
      refine (congrArg (fun u => Bind.bind (m := m) u _)
        ((Categorical.kleisli_comp_of _ _ _).trans ((pure_bind (m := m) _ _).trans
          ((Categorical.kleisli_comp_of _ _ _).trans
            (congrArg (fun u => Bind.bind (m := m) u _) (ihb (ρ, x))))))).trans ?_
      refine (bind_assoc (m := m) _ _ _).trans ?_
      refine bind_congr fun s => ?_
      refine (pure_bind (m := m) _ _).trans ?_
      exact congrArg pure (ofTypeModel_coprodIso_hom_apply s)
  | sub ha hAB ih =>
      simp only [Categorical.denoteOfType, Categorical.denote]
      refine (Categorical.kleisli_comp_of _ _ _).trans ?_
      exact congrArg (fun u => Bind.bind (m := m) u _) (ih ρ)

end Silmaril.Thesis.LambdaIter.Subtyping.Semantics
