module

public import Silmaril.Raw.SSA.Isotope.LetIter.ProofRelevant.Semantics.Categorical
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Derivation

@[expose] public section

open Silmaril.Isotope.LetIter.LocallyNameless (Tm Pure TypedRenaming)

/-!
# Exact categorical semantics for let-iter

Exact typing data is interpreted independently in a strong Elgot Freyd category.
Primitive arrows need no effect annotations or subtype interpretations. Products
sequence effects from left to right; coproduct left exits an iteration and right
continues it.

The generic Freyd combinators currently live with the proof-relevant semantics.
Only those combinators are reused here, not its typing or instruction models.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

variable {τ : Type u₃} {V : Type u₁} {C : Type u₂} {ν : Type u₅}

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (bind pair caseWithContext contextualLoop)

/-- Interpretation of object-language types in the value category.  Type former preservation is
recorded by isomorphisms rather than forced to hold definitionally. No subtyping or effect
annotation is required. -/
class TypeModel (τ : Type u₃) [TypeFormers τ]
    (V : Type u₁) [Category.{v₁} V] [CartesianMonoidalCategory V]
    [HasFiniteCoproducts V] where
  obj : τ → V
  productIso (A B : τ) : obj (product A B) ≅ obj A ⊗ obj B
  unitIso : obj (unit : τ) ≅ 𝟙_ V
  coprodIso (A B : τ) : obj (coprod A B) ≅ obj A ⨿ obj B
  emptyIsInitial : IsInitial (obj (empty : τ))

/-- Interpretation of primitive instructions as computation morphisms. -/
class InstructionModel [TypeFormers τ]
    [Category.{v₁} V] [Category.{v₂} C] (J : Functor V C)
    [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
    (M : TypeModel τ V) (Φ : Type u₄) [HasTy Φ τ] where
  denote (f : Φ) : J.obj (M.obj (instrSrc f)) ⟶ J.obj (M.obj (instrTrg f))

section Contexts

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)

/-- Value-category interpretation of a free-variable context.  The newest slot is the right
product factor, exactly as in the existing nested-pair semantics. -/
def ctxObj : Ctx ν τ → V
  | .nil => 𝟙_ V
  | .snoc Γ _ A => ctxObj Γ ⊗ M.obj A

/-- Value-category interpretation of a length-indexed bound context. -/
def boundObj : {n : Nat} → Isotope.BoundCtx τ n → V
  | 0, .nil => 𝟙_ V
  | _ + 1, .snoc β A => boundObj β ⊗ M.obj A

/-- The complete environment object. -/
def envObj (Γ : Ctx ν τ) {n : Nat} (β : Isotope.BoundCtx τ n) : V :=
  ctxObj M Γ ⊗ boundObj M β

/-- Categorical lookup of a visible free name. -/
noncomputable def ctxLookup [DecidableEq ν] : {Γ : Ctx ν τ} →
    (x : ν) → {A : τ} → Γ.lookup x = some A → (ctxObj M Γ ⟶ (M.obj A : V))
  | .nil, _, _, h => by simp [Ctx.lookup] at h
  | .snoc Γ none B, x, A, h =>
      CartesianMonoidalCategory.fst _ _ ≫ ctxLookup x h
  | .snoc Γ (some y) B, x, A, h => by
      by_cases hxy : x = y
      · subst y
        simp [Ctx.lookup] at h
        cases h
        exact CartesianMonoidalCategory.snd _ _
      · exact CartesianMonoidalCategory.fst _ _ ≫
          ctxLookup x (by simpa [Ctx.lookup, hxy] using h)

/-- Free lookup from the complete environment discards the bound component first. -/
noncomputable def freeLookup [DecidableEq ν] {Γ : Ctx ν τ}
    {n : Nat} {β : Isotope.BoundCtx τ n}
    (x : ν) {A : τ} (h : Γ.lookup x = some A) : envObj M Γ β ⟶ (M.obj A : V) :=
  CartesianMonoidalCategory.fst _ _ ≫ ctxLookup M x h

/-- Categorical lookup of a newest-first de Bruijn index. -/
noncomputable def boundLookup : {n : Nat} → {β : Isotope.BoundCtx τ n} →
    (i : Fin n) → (boundObj M β ⟶ (M.obj (β.get i) : V))
  | _ + 1, .snoc _β _A, i => Fin.cases
      (CartesianMonoidalCategory.snd _ _)
      (fun j => CartesianMonoidalCategory.fst _ _ ≫ boundLookup j) i

/-- Bound lookup from the complete environment discards the free component first. -/
noncomputable def boundVar {Γ : Ctx ν τ}
    {n : Nat} {β : Isotope.BoundCtx τ n} (i : Fin n) :
    envObj M Γ β ⟶ (M.obj (β.get i) : V) :=
  CartesianMonoidalCategory.snd _ _ ≫ boundLookup M i

/-- Extending the bound context corresponds, up to associativity, to pairing the old complete
environment with the new value. -/
def envSnocIso (Γ : Ctx ν τ) {n : Nat} (β : Isotope.BoundCtx τ n) (A : τ) :
    envObj M Γ β ⊗ M.obj A ≅ envObj M Γ (.snoc β A) :=
  α_ (ctxObj M Γ) (boundObj M β) (M.obj A)

end Contexts

section Denotation

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type _} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Reassociate an environment extended by a pair into an environment extended by its two
components. -/
def envPairHom (Γ : Ctx ν τ) {n : Nat} (β : Isotope.BoundCtx τ n) (A B : τ) :
    envObj M Γ β ⊗ (M.obj A ⊗ M.obj B) ⟶
      envObj M Γ (.snoc (.snoc β A) B) :=
  (α_ (ctxObj M Γ) (boundObj M β) (M.obj A ⊗ M.obj B)).hom ≫
    ctxObj M Γ ◁ (α_ (boundObj M β) (M.obj A) (M.obj B)).inv

/-- Interpret exact typing data in a strong Elgot Freyd category. -/
noncomputable def denote : {Γ : Ctx ν τ} → {n : Nat} →
    {β : Isotope.BoundCtx τ n} → {t : Silmaril.Isotope.LetIter.LocallyNameless.Tm ν Φ n} → {A : τ} →
    LocallyNameless.Derivation Φ Γ β t A →
      (J.obj (envObj M Γ β) ⟶ J.obj (M.obj A))
  | _, _, _, _, _, .fv h => J.map (freeLookup M _ h)
  | _, _, _, _, _, .bv => J.map (boundVar M _)
  | _, _, _, _, _, .op ha => denote ha ≫ InstructionModel.denote _
  | Γ, _, β, _, _, .let₁ ha hb => bind J (denote ha) <|
      J.map (envSnocIso M Γ β _).hom ≫ denote hb
  | _, _, _, _, _, .unit =>
      J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv)
  | _, _, _, _, _, .pair ha hb =>
      pair J (denote ha) (denote hb) ≫ J.map (M.productIso _ _).inv
  | Γ, _, β, _, _, .let₂ ha hc => bind J (denote ha) <|
      J.map ((𝟙 _) ⊗ₘ (M.productIso _ _).hom) ≫
        J.map (envPairHom M Γ β _ _) ≫ denote hc
  | _, _, _, _, _, .inl ha =>
      denote ha ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv)
  | _, _, _, _, _, .inr hb =>
      denote hb ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv)
  | Γ, _, β, _, _, .case he hl hr =>
      caseWithContext J (denote he ≫ J.map (M.coprodIso _ _).hom)
        (J.map (envSnocIso M Γ β _).hom ≫ denote hl)
        (J.map (envSnocIso M Γ β _).hom ≫ denote hr)
  | _, _, _, _, _, .abort ha =>
      denote ha ≫ J.map (M.emptyIsInitial.to (M.obj _))
  | Γ, _, β, _, _, .iter ha hb => bind J (denote ha) <|
      contextualLoop J
        (J.map (envSnocIso M Γ β _).hom ≫ denote hb ≫
          J.map (M.coprodIso _ _).hom)

end Denotation

end Silmaril.Isotope.LetIter.Semantics.Categorical

