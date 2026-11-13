module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ResourceNaturality
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ControlNaturality

@[expose] public section

namespace CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [PremonoidalCategory C]

@[reassoc] theorem whiskerRight_eqToHom {A B D E : C} (f : A ⟶ B) (h : D = E) :
    f ▷ D ≫ eqToHom (congrArg (fun X => B ⊗ X) h) =
      eqToHom (congrArg (fun X => A ⊗ X) h) ≫ f ▷ E := by
  cases h
  simp

@[reassoc] theorem associator_inv_naturality_left {A B : C} (f : A ⟶ B) (D E : C) :
    f ▷ (D ⊗ E) ≫ (α_ B D E).inv = (α_ A D E).inv ≫ f ▷ D ▷ E := by
  have h := congrArg (fun g => (α_ A D E).inv ≫ g ≫ (α_ B D E).inv)
    (associator_naturality_left f D E)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] using h.symm
end CategoryTheory.PremonoidalCategory

namespace Silmaril.Isotope.Refinement.Models.SeqData

open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- A pure map in the first tensor position commutes with any computation in
the other position. This uses effect exchange, not copying exchange. -/
theorem exchange_left_pure {A B D E : τ} (f : M.Hom A B) (g : M.Hom D E)
    (hf : M.hasEffect ⊥ f) :
    M.compose (M.right f D) (M.left B g) = M.compose (M.left A g) (M.right f E) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  have h := (M.effects.pure_central hf).left g
  simpa [right, left, compose, PremonoidalCategory.leftTensor, PremonoidalCategory.rightTensor,
    Category.assoc] using congrArg (fun h => eqToHom (M.tensor_obj A D).symm ≫ h ≫ eqToHom (M.tensor_obj B E)) h

/-- The tensor comparison needed when precomposing two arbitrary computations
by structural context maps; only the second structural map needs purity. -/
theorem tensor_comp_pure {A B D E G H : τ}
    (f : M.Hom A B) (g : M.Hom D E) (a : M.Hom B G) (b : M.Hom E H)
    (hg : M.hasEffect ⊥ g) :
    M.compose (M.tensor f g) (M.tensor a b) = M.tensor (M.compose f a) (M.compose g b) := by
  unfold tensor
  rw [M.right_compose, M.left_compose]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.left B g) (M.right a E), ← M.exchange_right_pure a g hg]
  simp only [M.compose_assoc]

/-- Interchange when the first computation in the second tensor is pure. -/
theorem tensor_comp_pure_middle {A B D E G H : τ}
    (f : M.Hom A B) (g : M.Hom D E) (a : M.Hom B G) (b : M.Hom E H)
    (ha : M.hasEffect ⊥ a) :
    M.compose (M.tensor f g) (M.tensor a b) = M.tensor (M.compose f a) (M.compose g b) := by
  unfold tensor
  rw [M.right_compose, M.left_compose]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.left B g) (M.right a E), ← M.exchange_left_pure a g ha]
  simp only [M.compose_assoc]

/-- Tensoring an effectful computation after a pure environment map. -/
theorem tensor_left_pure {A B D E G : τ} (f : M.Hom A B) (g : M.Hom D E) (a : M.Hom E G)
    (hf : M.hasEffect ⊥ f) :
    M.compose (M.tensor f g) (M.left B a) =
      M.compose (M.left A (M.compose g a)) (M.right f G) := by
  unfold tensor
  rw [M.compose_assoc, ← M.left_compose, M.exchange_left_pure f _ hf]

/-- Normalized naturality of associator inverse in its environment argument. -/
theorem associatorInv_natural_left {A B : τ} (f : M.Hom A B) (D E : τ) :
    M.compose (M.right f (product D E)) (M.associatorInv B D E) =
      M.compose (M.associatorInv A D E) (M.right (M.right f D) E) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp only [compose, right, associatorInv]
  simp only [Category.assoc, PremonoidalCategory.comp_whiskerRight,
    PremonoidalCategory.eqToHom_whiskerRight, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [PremonoidalCategory.whiskerRight_eqToHom_assoc f (M.tensor_obj D E).symm]
  simp [PremonoidalCategory.associator_inv_naturality_left_assoc]

end Silmaril.Isotope.Refinement.Models.SeqData
