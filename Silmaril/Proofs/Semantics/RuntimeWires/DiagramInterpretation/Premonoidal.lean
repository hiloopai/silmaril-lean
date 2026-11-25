module

public import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Basic

public section

namespace Silmaril.RuntimeWires.Proofs.DiagramInterpretation

open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory SameArrow

universe u v u' v'

section
variable {C : Type u'} [Category.{v'} C] [PremonoidalCategory C]

/-- The associator is natural for the sequential tensor. This proof uses
the three separate naturality squares in their execution order. -/
theorem sequential_assoc {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X' Y' Z').hom =
      (α_ X Y Z).hom ≫ (f ⊗ₘ g ⊗ₘ h) := by
  simp only [PremonoidalCategory.tensorHom_def, PremonoidalCategory.leftTensor,
    PremonoidalCategory.comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [PremonoidalCategory.associator_naturality_right,
    PremonoidalCategory.associator_naturality_middle_assoc,
    PremonoidalCategory.associator_naturality_left_assoc]

theorem sequential_id (X Y : C) : (𝟙 X ⊗ₘ 𝟙 Y) = 𝟙 (X ⊗ Y) := by
  rw [PremonoidalCategory.tensorHom_def, PremonoidalCategory.leftTensor_id]

/-- The only interchange used is for the middle two arrows. -/
theorem sequential_comp {A B D X Y Z : C} (f : A ⟶ B) (g : B ⟶ D) (h : X ⟶ Y) (k : Y ⟶ Z)
    (commute : g ⋉ h = g ⋊ h) :
    (f ⊗ₘ h) ≫ (g ⊗ₘ k) = (f ≫ g) ⊗ₘ (h ≫ k) := by
  change g ▷ X ≫ D ◁ h = B ◁ h ≫ g ▷ Y at commute
  simp only [PremonoidalCategory.tensorHom_def, PremonoidalCategory.leftTensor,
    PremonoidalCategory.comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% commute]

variable [IsStrictTensor C]

theorem premonoidal_tensor_assoc {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ₘ g) ⊗ₘ h ≈ₐ f ⊗ₘ g ⊗ₘ h :=
  of_square (IsStrictTensor.assocObj ..) (IsStrictTensor.assocObj ..)
    (by simpa only [IsStrictTensor.associator_hom] using sequential_assoc f g h)

theorem premonoidal_tensor_unit_left {X Y : C} (f : X ⟶ Y) : 𝟙 (𝟙_ C) ⊗ₘ f ≈ₐ f := by
  rw [PremonoidalCategory.tensorHom_def, PremonoidalCategory.leftTensor,
    PremonoidalCategory.id_whiskerRight, Category.id_comp]
  exact of_square (IsStrictTensor.leftObj X) (IsStrictTensor.leftObj Y)
    (by simpa only [IsStrictTensor.leftUnitor_hom] using PremonoidalCategory.leftUnitor_naturality f)

theorem premonoidal_tensor_unit_right {X Y : C} (f : X ⟶ Y) : f ⊗ₘ 𝟙 (𝟙_ C) ≈ₐ f := by
  rw [PremonoidalCategory.tensorHom_def, PremonoidalCategory.leftTensor,
    PremonoidalCategory.whiskerLeft_id, Category.comp_id]
  exact of_square (IsStrictTensor.rightObj X) (IsStrictTensor.rightObj Y)
    (by simpa only [IsStrictTensor.rightUnitor_hom] using PremonoidalCategory.rightUnitor_naturality f)

end

section
variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C]

/-- A strict chosen-pure functor carries the pure tensor to the sequential tensor. -/
theorem map_tensor (F : V ⥤ C) (h : IsStrictTensorFunctor F)
    {A B X Y : V} (f : A ⟶ B) (g : X ⟶ Y) :
    F.map (f ⊗ₘ g) ≈ₐ F.map f ⊗ₘ F.map g := by
  rw [MonoidalCategory.tensorHom_def, F.map_comp, PremonoidalCategory.tensorHom_def]
  exact (of_square (h.tensor A X) (h.tensor B X) (h.right f X)).comp
    (of_square (h.tensor B X) (h.tensor B Y) (h.left B g))

end
end Silmaril.RuntimeWires.Proofs.DiagramInterpretation
