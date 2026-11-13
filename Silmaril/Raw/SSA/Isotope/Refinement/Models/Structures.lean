module

public import Silmaril.Raw.SSA.Isotope.Refinement.Effects
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Coproducts
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Ordered categorical structure for the written refinement calculus

The structures here are on actual categories: terms denote morphisms, composition
is sequential execution, and refinement is the order on each hom set. They reuse
the premonoidal and Elgot interfaces without imposing cartesian structure on
linear or relevant values. Effect membership is a wide-subcategory predicate;
it is deliberately not assumed closed under refinement.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory PremonoidalCategory

variable (C : Type u) [Category.{v} C] [∀ X Y : C, PartialOrder (X ⟶ Y)]

/-- Poset enrichment is monotonicity of composition in both arguments. -/
class OrderedCategory : Prop where
  comp_mono {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z} :
    f ≤ f' → g ≤ g' → f ≫ g ≤ f' ≫ g'

/-- Each of the two tensor actions is enriched separately. -/
class OrderedPremonoidal [PremonoidalCategory C] : Prop extends OrderedCategory C where
  whiskerLeft_mono (X : C) {Y Z : C} {f g : Y ⟶ Z} : f ≤ g → X ◁ f ≤ X ◁ g
  whiskerRight_mono {X Y : C} {f g : X ⟶ Y} (Z : C) : f ≤ g → f ▷ Z ≤ g ▷ Z

variable {C}

/-- Sequential tensor is monotone, without requiring the interchange equation. -/
theorem leftTensor_mono [PremonoidalCategory C] [OrderedPremonoidal C]
    {A B D E : C} {f f' : A ⟶ B} {g g' : D ⟶ E} (hf : f ≤ f') (hg : g ≤ g') :
    f ⋉ g ≤ f' ⋉ g' :=
  OrderedCategory.comp_mono (OrderedPremonoidal.whiskerRight_mono D hf)
    (OrderedPremonoidal.whiskerLeft_mono B hg)

/-- A functor between locally ordered categories is enriched when its hom maps are monotone. -/
def EnrichedFunctor {D : Type w} [Category.{v} D] [∀ X Y : D, PartialOrder (X ⟶ Y)]
    (F : C ⥤ D) : Prop := ∀ {A B : C} {f g : A ⟶ B}, f ≤ g → F.map f ≤ F.map g

variable (C) [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
variable (ε : Type w) [EffectSystem ε]

/-- Wide effect subcategories, their tensor actions, and directed commutation. -/
structure EffectfulCategory where
  effect : ε → MorphismProperty C
  mono {e e' : ε} (h : e ≤ e') {A B : C} {f : A ⟶ B} : effect e f → effect e' f
  top {A B : C} (f : A ⟶ B) : effect ⊤ f
  id (e : ε) (A : C) : effect e (𝟙 A)
  comp {e : ε} {A B D : C} {f : A ⟶ B} {g : B ⟶ D} :
    effect e f → effect e g → effect e (f ≫ g)
  whiskerLeft {e : ε} (A : C) {B D : C} {f : B ⟶ D} : effect e f → effect e (A ◁ f)
  whiskerRight {e : ε} {A B : C} {f : A ⟶ B} (D : C) : effect e f → effect e (f ▷ D)
  associator (A B D : C) : effect ⊥ (α_ A B D).hom
  associator_inv (A B D : C) : effect ⊥ (α_ A B D).inv
  leftUnitor (A : C) : effect ⊥ (λ_ A).hom
  leftUnitor_inv (A : C) : effect ⊥ (λ_ A).inv
  rightUnitor (A : C) : effect ⊥ (ρ_ A).hom
  rightUnitor_inv (A : C) : effect ⊥ (ρ_ A).inv
  braiding (A B : C) : effect ⊥ (BraidedPremonoidalCategory.braiding A B).hom
  exchange (p : Polarity) {e η : ε} {A B D E : C} {f : A ⟶ B} {g : D ⟶ E} :
    EffectSystem.moves p e η → effect e f → effect η g → p.orient (· ≤ ·) (f ⋉ g) (f ⋊ g)

namespace EffectfulCategory

variable {ε C} (M : EffectfulCategory C ε)

instance multiplicative (e : ε) : (M.effect e).IsMultiplicative where
  id_mem := M.id e
  comp_mem _ _ := M.comp

/-- The category consisting of all objects and the morphisms of one effect. -/
abbrev Subcategory (e : ε) := WideSubcategory (M.effect e)

/-- Pure computations commute with every computation in either tensor position. -/
theorem pure_central {A B : C} {f : A ⟶ B} (hf : M.effect ⊥ f) :
    PremonoidalCategory.IsCentral f := by
  constructor
  · intro D E g
    exact le_antisymm
      (M.exchange .positive (EffectSystem.pure_moves .positive ⊤) hf (M.top g))
      (M.exchange .negative (EffectSystem.pure_moves .negative ⊤) hf (M.top g))
  · intro D E g
    exact le_antisymm
      (M.exchange .positive (EffectSystem.moves_pure .positive ⊤) (M.top g) hf)
      (M.exchange .negative (EffectSystem.moves_pure .negative ⊤) (M.top g) hf)

end EffectfulCategory

/-- Enriched chosen coproducts with pure injections and effect-preserving copairing. -/
structure CaseCategory (M : EffectfulCategory C ε) (S : ChosenCoproducts C) : Prop where
  inl (A B : C) : M.effect ⊥ (S.inl A B)
  inr (A B : C) : M.effect ⊥ (S.inr A B)
  initial (A : C) : M.effect ⊥ (S.abort A)
  desc {e : ε} {A B D : C} {f : A ⟶ D} {g : B ⟶ D} :
    M.effect e f → M.effect e g → M.effect e (S.desc f g)
  desc_mono {A B D : C} {f f' : A ⟶ D} {g g' : B ⟶ D} :
    f ≤ f' → g ≤ g' → S.desc f g ≤ S.desc f' g'
  distributor_isIso (A B D : C) : IsIso (S.distributor A B D)
  distributor_inv (A B D : C) : letI := distributor_isIso A B D
    M.effect ⊥ (inv (S.distributor A B D))

/-- Conway equations on the designated coproducts. The result summand is left
and the next-state summand right, as in the existing Elgot interface. -/
structure ConwayIteration (S : ChosenCoproducts C) where
  iterate {A B : C} : (A ⟶ S.sum B A) → (A ⟶ B)
  fixpoint {A B : C} (f : A ⟶ S.sum B A) :
    iterate f = f ≫ S.desc (𝟙 B) (iterate f)
  naturality {A B D : C} (f : A ⟶ S.sum B A) (g : B ⟶ D) :
    iterate f ≫ g = iterate (f ≫ S.map g (𝟙 A))
  codiagonal {A B : C} (f : A ⟶ S.sum (S.sum B A) A) :
    iterate (iterate f) = iterate (f ≫ S.desc (𝟙 (S.sum B A)) (S.inr B A))

/-- Strong Conway iteration with order, effects, and directed uniformity.
Uniformity bounds the left loop body; its right body may have arbitrary effect,
as in the written rule's unbounded `b'` and exit continuation. -/
structure IterCategory (M : EffectfulCategory C ε) (S : ChosenCoproducts C)
    (CS : CaseCategory C ε M S) (It : ConwayIteration C S) : Prop where
  monotone {A B : C} {f g : A ⟶ S.sum B A} : f ≤ g → It.iterate f ≤ It.iterate g
  effect {e : ε} {A B : C} {f : A ⟶ S.sum B A} :
    EffectSystem.iterable e → M.effect e f → M.effect e (It.iterate f)
  strength (D : C) {A B : C} (f : A ⟶ S.sum B A) :
    letI := CS.distributor_isIso D B A
    It.iterate ((D ◁ f) ≫ inv (S.distributor D B A)) = D ◁ It.iterate f
  uniformity (p : Polarity) {e η : ε} {A B D : C}
      {h : A ⟶ B} {f : B ⟶ S.sum D B} {g : A ⟶ S.sum D A} :
    EffectSystem.iterable e → EffectSystem.moves p η e →
    M.effect η h → M.effect e f →
    p.orient (· ≤ ·) (h ≫ f) (g ≫ S.map (𝟙 D) h) →
    p.orient (· ≤ ·) (h ≫ It.iterate f) (It.iterate g)

/-- Pure discard/copy maps and the three effect-sensitive naturality principles.
These are conditional on type linearity: neither map is provided for every object.
Directed copy naturality does not assert exchange of the two evaluation orders. -/
structure CopyDiscard (M : EffectfulCategory C ε) (quantity : C → Quantity) where
  discard (A : C) : Quantity.affine ≤ quantity A → (A ⟶ 𝟙_ C)
  copy (A : C) : Quantity.relevant ≤ quantity A → (A ⟶ A ⊗ A)
  discard_pure (A : C) (h : Quantity.affine ≤ quantity A) : M.effect ⊥ (discard A h)
  copy_pure (A : C) (h : Quantity.relevant ≤ quantity A) : M.effect ⊥ (copy A h)
  copy_assoc (A : C) (h : Quantity.relevant ≤ quantity A) :
    copy A h ≫ copy A h ▷ A ≫ (α_ A A A).hom = copy A h ≫ A ◁ copy A h
  copy_comm (A : C) (h : Quantity.relevant ≤ quantity A) :
    copy A h ≫ (BraidedPremonoidalCategory.braiding A A).hom = copy A h
  discard_natural (p : Polarity) {e : ε} {A B : C} (f : A ⟶ B)
      (hA : Quantity.affine ≤ quantity A) (hB : Quantity.affine ≤ quantity B) :
    EffectSystem.canDelete p e → M.effect e f →
    p.orient (· ≤ ·) (f ≫ discard B hB) (discard A hA)
  retained_elimination (p : Polarity) {e : ε} {A B : C} (f : A ⟶ B)
      (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.affine ≤ quantity B) :
    EffectSystem.canDelete p e → M.effect e f →
    p.orient (· ≤ ·) (copy A hA ≫ (f ≫ discard B hB) ▷ A) (λ_ A).inv
  copy_natural (p : Polarity) {e : ε} {A B : C} (f : A ⟶ B)
      (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.relevant ≤ quantity B) :
    EffectSystem.canCopy p e → M.effect e f →
    p.orient (· ≤ ·) (f ≫ copy B hB) (copy A hA ≫ (f ⋉ f))

end Silmaril.Isotope.Refinement.Models
