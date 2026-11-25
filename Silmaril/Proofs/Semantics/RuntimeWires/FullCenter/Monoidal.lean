module

public import Silmaril.Semantics.RuntimeWires.FullCenter.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Premonoidal

public section

namespace Silmaril.RuntimeWires.Proofs.FullCenter

open CategoryTheory PremonoidalCategory
open scoped MonoidalCategory PremonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C] [IsStrictTensor C]

theorem monoidal_id (X Y : Center C) : (𝟙 X ⊗ₘ 𝟙 Y) = 𝟙 (X ⊗ Y) :=
  WideSubcategory.hom_ext (central C) (DiagramInterpretation.sequential_id X.obj Y.obj)

theorem monoidal_left (X : Center C) {Y Z : Center C} (f : Y ⟶ Z) :
    (𝟙 X ⊗ₘ f) = X ◁ f := by
  apply WideSubcategory.hom_ext (central C)
  change (𝟙 X.obj ⊗ₘ f.hom) = X.obj ◁ f.hom
  simp [PremonoidalCategory.tensorHom_def, leftTensor]

theorem monoidal_right {X Y : Center C} (f : X ⟶ Y) (Z : Center C) :
    (f ⊗ₘ 𝟙 Z) = f ▷ Z := by
  apply WideSubcategory.hom_ext (central C)
  change (f.hom ⊗ₘ 𝟙 Z.obj) = f.hom ▷ Z.obj
  simp [PremonoidalCategory.tensorHom_def, leftTensor]

theorem monoidal_comp {A B D X Y Z : Center C}
    (f : A ⟶ B) (h : X ⟶ Y) (g : B ⟶ D) (k : Y ⟶ Z) :
    (f ⊗ₘ h) ≫ (g ⊗ₘ k) = (f ≫ g) ⊗ₘ (h ≫ k) :=
  WideSubcategory.hom_ext (central C)
    (DiagramInterpretation.sequential_comp f.hom g.hom h.hom k.hom (g.property.1 h.hom))

theorem monoidal_assoc {X Y Z X' Y' Z' : Center C}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X' Y' Z').hom = (α_ X Y Z).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) :=
  WideSubcategory.hom_ext (central C) (DiagramInterpretation.sequential_assoc f.hom g.hom h.hom)

theorem monoidal_unitor_left {X Y : Center C} (f : X ⟶ Y) :
    (𝟙 (𝟙_ (Center C)) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  rw [monoidal_left]
  exact WideSubcategory.hom_ext (central C) (PremonoidalCategory.leftUnitor_naturality f.hom)

theorem monoidal_unitor_right {X Y : Center C} (f : X ⟶ Y) :
    (f ⊗ₘ 𝟙 (𝟙_ (Center C))) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  rw [monoidal_right]
  exact WideSubcategory.hom_ext (central C) (PremonoidalCategory.rightUnitor_naturality f.hom)

theorem monoidal_pentagon (W X Y Z : Center C) : MonoidalCategory.Pentagon W X Y Z :=
  WideSubcategory.hom_ext (central C) (PremonoidalCategory.pentagon W.obj X.obj Y.obj Z.obj)

theorem monoidal_triangle (X Y : Center C) :
    (α_ X (𝟙_ (Center C)) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y :=
  WideSubcategory.hom_ext (central C) (PremonoidalCategory.triangle X.obj Y.obj)

theorem model_objects (C : Type u) [Category.{v} C] [PremonoidalCategory C] :
    Function.Bijective (centerInclusion C).obj :=
  ⟨fun ⟨_⟩ ⟨_⟩ e => congrArg WideSubcategory.mk e, fun X => ⟨⟨X⟩, rfl⟩⟩

end Silmaril.RuntimeWires.Proofs.FullCenter
