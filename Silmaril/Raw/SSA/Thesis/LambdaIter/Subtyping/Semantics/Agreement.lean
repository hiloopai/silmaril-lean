module

public import Silmaril.Raw.SSA.Thesis.CategoryTheory.Monad.Elgot
public import Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.Semantics.Categorical
public import Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.Semantics.Denotation

/-!
# Agreement of categorical and monadic lambda-iter semantics

This file specializes the categorical interfaces to the set-valued model and its Kleisli
category.  The final agreement theorem is intentionally stated pointwise on the underlying
Kleisli arrow.
-/

@[expose] public section

-- Source lakefile: autoImplicit (Lean default) on, relaxedAutoImplicit off.
set_option autoImplicit true
set_option relaxedAutoImplicit false

universe u v w q r

namespace Silmaril.Thesis.LambdaIter.Subtyping.Semantics

open Silmaril.Thesis.LambdaIter.LocallyNameless
open Silmaril.Thesis.LambdaIter.Subtyping.LocallyNameless

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Silmaril.Thesis.Elgot

namespace Categorical

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable [Semantics.TypeModel.{u, v} τ]

private theorem types_coprodMap_comparison {X Y X' Y' : Type v}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    coprod.map f g ≫ (Types.binaryCoproductIso X' Y').hom =
      (Types.binaryCoproductIso X Y).hom ≫ TypeCat.ofHom (Sum.map f g) := by
  apply coprod.hom_ext
  · rw [coprod.inl_map_assoc, Types.binaryCoproductIso_inl_comp_hom,
      ← Category.assoc, Types.binaryCoproductIso_inl_comp_hom]
    rfl
  · rw [coprod.inr_map_assoc, Types.binaryCoproductIso_inr_comp_hom,
      ← Category.assoc, Types.binaryCoproductIso_inr_comp_hom]
    rfl

/-- A set-valued type model is a categorical type model in `Type`. -/
@[reducible] noncomputable def ofTypeModel : Categorical.TypeModel τ (Type v) where
  obj := Semantics.TypeModel.interp
  tensorIso A B := Equiv.toIso (Semantics.TypeModel.tensorEquiv A B)
  unitIso :=
    { hom := TypeCat.ofHom (fun _ => PUnit.unit)
      inv := TypeCat.ofHom (fun _ => Semantics.TypeModel.unitEquiv.symm ())
      hom_inv_id := by
        ext x
        exact Semantics.TypeModel.unitEquiv.injective
          (Semantics.TypeModel.unitEquiv.apply_symm_apply ())
      inv_hom_id := by ext }
  coprodIso A B := (Equiv.toIso (Semantics.TypeModel.coprodEquiv A B)).trans
    (Types.binaryCoproductIso _ _).symm
  emptyIsInitial := IsInitial.ofUniqueHom
    (fun _ => TypeCat.ofHom (fun z => Empty.elim (Semantics.TypeModel.emptyEquiv z)))
    (fun _ _ => by ext z; exact Empty.elim (Semantics.TypeModel.emptyEquiv z))
  subty d := TypeCat.ofHom (Semantics.TypeModel.coe d)

private theorem ofTypeModel_coprodIso_hom_comparison (A B : τ) :
    ((ofTypeModel (τ := τ)).coprodIso A B).hom ≫
        (Types.binaryCoproductIso
          ((ofTypeModel (τ := τ)).obj A)
          ((ofTypeModel (τ := τ)).obj B)).hom =
      (Equiv.toIso (Semantics.TypeModel.coprodEquiv A B)).hom := by
  change (((Equiv.toIso (Semantics.TypeModel.coprodEquiv A B)).trans
      (Types.binaryCoproductIso _ _).symm).hom ≫
        (Types.binaryCoproductIso _ _).hom) = _
  simp [Category.assoc]

/-- Elementwise naturality of an `Equiv`-presented coproduct comparison in `Type`. -/
private theorem types_coprodIso_naturality {X Y X' Y' S S' : Type v}
    (e : S ≃ X ⊕ Y) (e' : S' ≃ X' ⊕ Y') (c : S → S') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : ∀ s, e' (c s) = Sum.map f g (e s)) :
    TypeCat.ofHom c ≫ ((Equiv.toIso e').trans (Types.binaryCoproductIso X' Y').symm).hom =
      ((Equiv.toIso e).trans (Types.binaryCoproductIso X Y).symm).hom ≫
        coprod.map f g := by
  rw [← cancel_mono (Types.binaryCoproductIso X' Y').hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, types_coprodMap_comparison, Iso.inv_hom_id_assoc]
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  exact h s

/-- The structural laws of a set-valued type model transport to the
categorical model in `Type`. -/
noncomputable instance ofTypeModelLawful [Semantics.LawfulTypeModel.{u, v} τ] :
    Categorical.LawfulTypeModel τ (Type v) (ofTypeModel (τ := τ)) where
  subty_refl A := by
    ext x
    exact congrFun (Semantics.LawfulTypeModel.coe_refl A) x
  subty_trans f g := by
    ext x
    exact congrFun (Semantics.LawfulTypeModel.coe_trans f g) x
  subty_tensor f g := by
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    exact Semantics.LawfulTypeModel.coe_tensor f g p
  subty_coprod f g :=
    types_coprodIso_naturality _ _ _ _ _
      (Semantics.LawfulTypeModel.coe_coprod f g)
  subty_empty A := by
    ext z
    exact Empty.elim (Semantics.TypeModel.emptyEquiv z)
  subty_unit A := by
    rfl

/-- Optional proof irrelevance transports independently of the structural
laws. -/
noncomputable instance ofTypeModelSubtyProofIrrelevant
    [Semantics.SubtyProofIrrelevant.{u, v} τ] :
    Categorical.SubtyProofIrrelevant τ (Type v) (ofTypeModel (τ := τ)) where
  subty_eq f g := congrArg TypeCat.ofHom (Semantics.SubtyProofIrrelevant.coe_eq f g)

variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Semantics.InstructionModel Φ τ ε m]

/-- A monadic instruction interpretation is precisely a Kleisli instruction interpretation. -/
@[reducible] def ofInstructionModel : Categorical.InstructionModel
    (CategoryTheory.Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m))
    (ofTypeModel (τ := τ)) Φ where
  denote f := CategoryTheory.Kleisli.Hom.mk
    (TypeCat.ofHom (Semantics.InstructionModel.denote
      (Φ := Φ) (τ := τ) (ε := ε) (m := m) f))

variable {ν : Type w} [DecidableEq ν]
variable [Silmaril.Thesis.Elgot.Iterate m] [Silmaril.Thesis.Elgot.LawfulElgotMonad m]

@[simp] private theorem types_snd_apply {X Y : Type v} (p : X × Y) :
    CategoryTheory.CartesianMonoidalCategory.snd X Y p = p.2 := by rfl

@[simp] private theorem types_fst_apply {X Y : Type v} (p : X × Y) :
    CategoryTheory.CartesianMonoidalCategory.fst X Y p = p.1 := by rfl

/-- The categorical denotation specialized to a set-valued monadic model. -/
noncomputable def denoteOfType {Γ : Ctx ν τ} {n : Nat}
    {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :=
  letI := ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  Categorical.denote
    (CategoryTheory.Kleisli.Adjunction.toKleisli (CategoryTheory.ofTypeMonad m))
    (ofTypeModel (τ := τ)) h

end Categorical

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable [Semantics.TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Semantics.InstructionModel Φ τ ε m]
variable {ν : Type w} [DecidableEq ν]
variable [Silmaril.Thesis.Elgot.Iterate m] [Silmaril.Thesis.Elgot.LawfulElgotMonad m]

/-- Canonical embedding of the existing nested-pair free environment into its categorical
interpretation.  This avoids requiring the syntactic and semantic universes to coincide. -/
def ctxToCategorical : {Γ : Ctx ν τ} → CtxDen Γ →
    Categorical.ctxObj (Categorical.ofTypeModel (τ := τ)) Γ
  | .nil, _ => PUnit.unit
  | .snoc _ _ _, γ => (ctxToCategorical γ.1, γ.2)

/-- Canonical embedding of a bound environment into its categorical interpretation. -/
def boundToCategorical : {n : Nat} → {β : BoundCtx τ n} → BoundDen β →
    Categorical.boundObj (Categorical.ofTypeModel (τ := τ)) β
  | 0, .nil, _ => PUnit.unit
  | _ + 1, .snoc _ _, ρ => (boundToCategorical ρ.1, ρ.2)

/-- Canonical complete categorical environment associated to the monadic environments. -/
def envToCategorical {n : Nat} {Γ : Ctx ν τ} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    Categorical.envObj (Categorical.ofTypeModel (τ := τ)) Γ β :=
  (ctxToCategorical γ, boundToCategorical ρ)

theorem ctxLookup_toCategorical {Γ : Ctx ν τ} (γ : CtxDen Γ)
    (x : ν) {A : τ} (h : Γ.lookup x = some A) :
    Categorical.ctxLookup (Categorical.ofTypeModel (τ := τ)) x h
        (ctxToCategorical γ) = CtxDen.lookup γ x h := by
  induction Γ generalizing A with
  | nil => simp [Ctx.lookup] at h
  | snoc Γ name B ih =>
      cases name with
      | none =>
          exact ih γ.1 h
      | some y =>
          by_cases hxy : x = y
          · subst y
            have hBA : B = A := by simpa [Ctx.lookup] using h
            subst A
            simp only [Categorical.ctxLookup, CtxDen.lookup, ctxToCategorical]
            simp
            rfl
          · simp only [Categorical.ctxLookup, CtxDen.lookup, ctxToCategorical]
            simp only [dite_eq_right hxy]
            change Categorical.ctxLookup (Categorical.ofTypeModel (τ := τ)) x _
                (ctxToCategorical γ.1) = CtxDen.lookup γ.1 x _
            exact ih γ.1 (by simpa [Ctx.lookup, hxy] using h)

theorem freeLookup_toCategorical {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) (x : ν) {A : τ}
    (h : Γ.lookup x = some A) :
    Categorical.freeLookup (Categorical.ofTypeModel (τ := τ)) x h
        (envToCategorical γ ρ) = CtxDen.lookup γ x h := by
  exact ctxLookup_toCategorical γ x h

theorem boundLookup_toCategorical {n : Nat} {β : BoundCtx τ n}
    (ρ : BoundDen β) (i : Fin n) :
    Categorical.boundLookup (Categorical.ofTypeModel (τ := τ)) i
        (boundToCategorical ρ) = BoundDen.get ρ i := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih ρ.1 j

omit [DecidableEq ν] in
theorem boundVar_toCategorical {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) (i : Fin n) :
    Categorical.boundVar (Categorical.ofTypeModel (τ := τ)) i
        (envToCategorical γ ρ) = BoundDen.get ρ i := by
  exact boundLookup_toCategorical ρ i

omit [DecidableEq ν] in
theorem envSnocIso_toCategorical {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) {A : τ} (a : TyDen A) :
    (Categorical.envSnocIso (Categorical.ofTypeModel (τ := τ)) Γ β A).hom
        (envToCategorical γ ρ, a) = envToCategorical (β := .snoc β A) γ (ρ, a) := by rfl

omit [DecidableEq ν] in
theorem envPairHom_toCategorical {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    (γ : CtxDen Γ) (ρ : BoundDen β) {A B : τ} (a : TyDen A) (b : TyDen B) :
    Categorical.envPairHom (Categorical.ofTypeModel (τ := τ)) Γ β A B
        (envToCategorical γ ρ, (a, b)) =
          envToCategorical (β := .snoc (.snoc β A) B) γ ((ρ, a), b) := by rfl

end Silmaril.Thesis.LambdaIter.Subtyping.Semantics
