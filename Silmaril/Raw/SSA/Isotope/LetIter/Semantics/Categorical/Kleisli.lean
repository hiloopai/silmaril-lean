module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Categorical
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Monadic
public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.Semantics.Agreement.Combinators

/-!
# Kleisli interpretation of exact categorical models

A type interpretation and arbitrary monadic primitive functions induce a
categorical model. Packed categorical environments project to the functional
environments used by the direct interpretation. No inverse is asserted for
free environments: anonymous and shadowed slots remain in the packed product,
and their interpretations need not be inhabited.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.Semantics
open Silmaril.Isotope.LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] (D : τ → Type v)
  [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]

/-- A type interpretation preserving the four type formers induces a model in `Type`. -/
@[reducible] noncomputable def ofTypeModel : TypeModel τ (Type v) where
  obj := D
  productIso A B := Equiv.toIso (ProductModel.productEquiv (D := D) A B)
  unitIso := Equiv.toIso (UnitModel.unitEquiv (D := D))
  coprodIso A B := (Equiv.toIso (CoproductModel.coprodEquiv (D := D) A B)).trans
    (Types.binaryCoproductIso _ _).symm
  emptyIsInitial := IsInitial.ofUniqueHom
    (fun X => TypeCat.ofHom fun z => PEmpty.elim (EmptyModel.emptyEquiv (D := D) z))
    (fun X f => by ext z; exact PEmpty.elim (EmptyModel.emptyEquiv (D := D) z))

variable {Φ : Type q} [HasTy Φ τ]
  {m : Type v → Type v} [Monad m] [LawfulMonad m]
  (M : Isotope.Semantics.InstructionModel D Φ m)

/-- Primitive monadic computations are the corresponding Kleisli arrows. -/
@[reducible] def ofInstructionModel : InstructionModel
    (Kleisli.Adjunction.toKleisli (ofTypeMonad m)) (ofTypeModel D) Φ where
  denote f := Kleisli.Hom.mk (TypeCat.ofHom (M.eval f))

variable {ν : Type w} [DecidableEq ν]

/-- Project a packed free environment to the values of visible names. -/
noncomputable def freeEnv {Γ : Ctx ν τ} (γ : ctxObj (ofTypeModel D) Γ) : FreeEnv D Γ :=
  fun x _ h => ctxLookup (ofTypeModel D) x h γ

/-- Project a packed bound environment to its newest-first indexed values. -/
noncomputable def boundEnv {n : Nat} {β : BoundCtx τ n}
    (ρ : boundObj (ofTypeModel D) β) : BoundEnv D β :=
  fun i => boundLookup (ofTypeModel D) i ρ

@[simp] theorem boundEnv_snoc {n : Nat} {β : BoundCtx τ n} {A : τ}
    (ρ : boundObj (ofTypeModel D) β) (a : D A) :
    boundEnv D (β := .snoc β A) (ρ, a) = (boundEnv D ρ).snoc a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem freeLookup_apply {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (γ : ctxObj (ofTypeModel D) Γ) (ρ : boundObj (ofTypeModel D) β)
    (x : ν) {A : τ} (h : Γ.lookup x = some A) :
    freeLookup (ofTypeModel D) (β := β) x h (γ, ρ) = freeEnv D γ x A h := rfl

omit [DecidableEq ν] in
@[simp] theorem boundVar_apply {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (γ : ctxObj (ofTypeModel D) Γ) (ρ : boundObj (ofTypeModel D) β) (i : Fin n) :
    boundVar (ofTypeModel D) (Γ := Γ) i (γ, ρ) = boundEnv D ρ i := rfl

variable [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]

/-- Specialize the independent categorical interpretation to the monadic model. -/
noncomputable def denoteOfType {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A) :=
  letI := ofInstructionModel D M
  denote (Kleisli.Adjunction.toKleisli (ofTypeMonad m)) (ofTypeModel D) d

end Silmaril.Isotope.LetIter.Semantics.Categorical
