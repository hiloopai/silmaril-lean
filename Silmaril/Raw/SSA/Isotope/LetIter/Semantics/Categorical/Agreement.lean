module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Categorical.Kleisli

/-!
# Agreement of exact categorical and monadic let-iter semantics

The categorical interpreter is independent of the monadic recursion. Its
Kleisli specialization agrees at every packed environment with direct monadic
evaluation of the visible free values and the indexed bound values.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope.Semantics
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (bind_of pair_of caseWithContext_of contextualLoop_of typeJ)

universe u v w q

variable {τ : Type u} [TypeFormers τ] (D : τ → Type v)
  [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  {m : Type v → Type v} [Monad m] [LawfulMonad m]
  [Iterate m] [LawfulElgotMonad m]
  (M : Isotope.Semantics.InstructionModel D Φ m)

/-- Every exact categorical denotation agrees with the direct monadic interpreter.
The input is a packed environment, including any anonymous and shadowed slots. -/
theorem denoteOfType_eq {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : Derivation Φ Γ β t A)
    (γ : ctxObj (ofTypeModel D) Γ) (ρ : boundObj (ofTypeModel D) β) :
    (denoteOfType D M h).of (γ, ρ) =
      Derivation.denote D M h (freeEnv D γ) (boundEnv D ρ) := by
  induction h with
  | fv _ => rfl
  | bv => rfl
  | @op n β f a ha ih =>
      simp [denoteOfType, denote, Derivation.denote,
        ofInstructionModel, ofTypeModel, joinM,
        bind_map_left]
      exact congrArg (fun x => x >>= M.eval f) (ih ρ)
  | let₁ ha hb iha ihb =>
      have hia := iha ρ
      simp only [denoteOfType, ofTypeModel] at hia
      have hib (a) := ihb (ρ, a)
      simp only [boundEnv_snoc] at hib
      simp only [denoteOfType, ofTypeModel] at hib
      simp [denoteOfType, denote, Derivation.denote,
        ofTypeModel]
      refine (bind_of (m := m) _ _ (γ, ρ)).trans ?_
      simp only [Bind.kleisliRight]
      refine congrArg₂ (fun x k => x >>= k) hia ?_
      funext a
      simp [joinM]
      exact hib a
  | unit => rfl
  | pair ha hb iha ihb =>
      have hp := pair_of (m := m) (denoteOfType D M ha) (denoteOfType D M hb) (γ, ρ)
      simp [denoteOfType, denote, Derivation.denote, ofTypeModel, joinM]
      refine (congrArg
        (fun x => Functor.map (f := m) (ProductModel.productEquiv (D := D) _ _).symm x) hp).trans ?_
      simp only [Bind.kleisliRight, map_bind, bind_pure_comp, Functor.map_map, iha ρ, ihb ρ]
      rfl
  | @let₂ n β a c A B C ha hc iha ihc =>
      have hia := iha ρ
      simp only [denoteOfType, ofTypeModel] at hia
      simp [denoteOfType, denote, Derivation.denote,
        ofTypeModel]
      refine (bind_of (m := m) _ _ (γ, ρ)).trans ?_
      simp only [Bind.kleisliRight]
      refine congrArg₂ (fun x k => x >>= k) hia ?_
      funext ab
      simp [joinM]
      change (denoteOfType D M hc).of
        (γ, ((ρ, (ProductModel.productEquiv (D := D) A B ab).1),
          (ProductModel.productEquiv (D := D) A B ab).2)) = _
      have h := ihc ((ρ, (ProductModel.productEquiv (D := D) A B ab).1),
        (ProductModel.productEquiv (D := D) A B ab).2)
      rw [boundEnv_snoc D (β := .snoc β A), boundEnv_snoc D (β := β)] at h
      exact h
  | inl ha ih =>
      have hi := ih ρ
      simp only [denoteOfType, ofTypeModel] at hi
      simp [denoteOfType, denote, Derivation.denote,
        ofTypeModel, joinM, bind_map_left]
      exact hi
  | inr hb ih =>
      have hi := ih ρ
      simp only [denoteOfType, ofTypeModel] at hi
      simp [denoteOfType, denote, Derivation.denote,
        ofTypeModel, joinM, bind_map_left]
      exact hi
  | case he hl hr ihe ihl ihr =>
      have hie := ihe ρ
      simp only [denoteOfType, ofTypeModel] at hie
      have hil (a) := ihl (ρ, a)
      simp only [boundEnv_snoc] at hil
      simp only [denoteOfType, ofTypeModel] at hil
      have hir (b) := ihr (ρ, b)
      simp only [boundEnv_snoc] at hir
      simp only [denoteOfType, ofTypeModel] at hir
      simp [denoteOfType, denote, Derivation.denote,
        ofTypeModel]
      refine (caseWithContext_of (m := m) _ _ _ (γ, ρ)).trans ?_
      simp [Bind.kleisliRight, joinM]
      refine congrArg₂ (fun x k => x >>= k) ?_ ?_
      · exact hie
      funext e
      dsimp only [Kleisli.Adjunction.toKleisli] at hil hir ⊢
      cases h : CoproductModel.coprodEquiv (D := D) _ _ e with
      | inl a =>
          exact hil a
      | inr b =>
          exact hir b
  | abort ha ih =>
      have hi := ih ρ
      simp only [denoteOfType, ofTypeModel] at hi
      simp [denoteOfType, denote, Derivation.denote,
        ofTypeModel,
        joinM, bind_map_left]
      refine congrArg₂ (fun x k => x >>= k) hi ?_
      funext z
      exact PEmpty.elim (EmptyModel.emptyEquiv (D := D) z)
  | iter ha hb iha ihb =>
      have hia := iha ρ
      simp only [denoteOfType, ofTypeModel] at hia
      have hib (a) := ihb (ρ, a)
      simp only [boundEnv_snoc] at hib
      simp only [denoteOfType, ofTypeModel] at hib
      simp [denoteOfType, denote, Derivation.denote,
        ofTypeModel]
      refine (bind_of (m := m) _ _ (γ, ρ)).trans ?_
      simp only [Bind.kleisliRight]
      refine congrArg₂ (fun x k => x >>= k) hia ?_
      funext a
      simp []
      refine (contextualLoop_of (m := m) _ (γ, ρ) a).trans ?_
      apply congrArg (fun q => Silmaril.Elgot.iter (m := m) q a)
      funext x
      dsimp only [typeJ, Kleisli.Adjunction.toKleisli, ofTypeMonad, ofTypeFunctor] at hib ⊢
      simp [Bind.kleisliRight, joinM]
      exact hib x

/-- Hidden packed slots cannot affect a computation once the visible values agree. -/
theorem denoteOfType_congr_freeEnv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : Derivation Φ Γ β t A)
    {γ₁ γ₂ : ctxObj (ofTypeModel D) Γ}
    (hγ : freeEnv D γ₁ = freeEnv D γ₂) (ρ : boundObj (ofTypeModel D) β) :
    (denoteOfType D M h).of (γ₁, ρ) = (denoteOfType D M h).of (γ₂, ρ) := by
  rw [denoteOfType_eq, denoteOfType_eq, hγ]

/-- A closed categorical program returns precisely its direct monadic computation. -/
theorem denoteOfType_closed {t : Tm Empty Φ 0} {A : τ}
    (h : Derivation Φ (.nil : Ctx Empty τ) .nil t A) :
    (denoteOfType D M h).of (PUnit.unit, PUnit.unit) =
      Derivation.denoteClosed D M h := by
  rw [denoteOfType_eq]
  have hf : freeEnv D (Γ := .nil) PUnit.unit =
      (fun x : Empty => nomatch x) := by funext x; cases x
  have hb : boundEnv D (β := .nil) PUnit.unit =
      (fun i => Fin.elim0 i) := by funext i; exact Fin.elim0 i
  exact congrArg₂ (Derivation.denote D M h) hf hb

end Silmaril.Isotope.LetIter.Semantics.Categorical
