module

public import Silmaril.Semantics.Categories.Thms
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

/-! # Monoidal structure when all morphisms are central

This construction is used for the pure wide subcategory of an effectful
premonoidal category; it does not impose interchange on effectful morphisms.
-/

namespace CategoryTheory.PremonoidalCategory

universe u v
open scoped MonoidalCategory PremonoidalCategory
variable {C : Type u} [Category.{v} C] [PremonoidalCategory C]

@[simp] theorem whiskerLeft_eqToHom (A : C) {B D : C} (h : B = D) :
    A ◁ eqToHom h = eqToHom (congrArg (fun X => A ⊗ X) h) := by
  subst D
  simp

@[simp] theorem eqToHom_whiskerRight {A B : C} (h : A = B) (D : C) :
    eqToHom h ▷ D = eqToHom (congrArg (fun X => X ⊗ D) h) := by
  subst B
  simp

/-- A premonoidal category whose morphisms are all central is monoidal. -/
@[instance_reducible] def monoidalOfCentral (central : ∀ {A B : C} (f : A ⟶ B), IsCentral f) : MonoidalCategory C where
  __ := (inferInstance : PremonoidalCategory C).toMonoidalCategoryStruct
  tensorHom_def := PremonoidalCategory.tensorHom_def
  id_tensorHom_id A B := by simp [PremonoidalCategory.tensorHom_def, leftTensor]
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    have hc := (central g₁).1 f₂
    simp only [leftTensor, rightTensor] at hc
    simp only [PremonoidalCategory.tensorHom_def, leftTensor,
      PremonoidalCategory.comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [← Category.assoc ( _ ◁ f₂), ← hc]
    simp only [Category.assoc]
  whiskerLeft_id := PremonoidalCategory.whiskerLeft_id
  id_whiskerRight := PremonoidalCategory.id_whiskerRight
  associator_naturality f₁ f₂ f₃ := by
    simp only [PremonoidalCategory.tensorHom_def, leftTensor,
      PremonoidalCategory.comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [PremonoidalCategory.associator_naturality_right,
      PremonoidalCategory.associator_naturality_middle_assoc,
      PremonoidalCategory.associator_naturality_left_assoc]
  leftUnitor_naturality := PremonoidalCategory.leftUnitor_naturality
  rightUnitor_naturality := PremonoidalCategory.rightUnitor_naturality
  pentagon := PremonoidalCategory.pentagon
  triangle := PremonoidalCategory.triangle

end CategoryTheory.PremonoidalCategory
