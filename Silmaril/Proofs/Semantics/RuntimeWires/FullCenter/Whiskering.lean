module

public import Silmaril.Semantics.RuntimeWires.StrictEffectful.Thms
public import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Premonoidal

public section

namespace Silmaril.RuntimeWires.Proofs.FullCenter

open CategoryTheory PremonoidalCategory
open scoped MonoidalCategory PremonoidalCategory SameArrow

universe u v

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C] [IsStrictTensor C]

private theorem assoc_left {X Y : C} (f : X ⟶ Y) (Z W : C) :
    (f ▷ Z) ▷ W ≈ₐ f ▷ (Z ⊗ W) :=
  DiagramInterpretation.of_square (IsStrictTensor.assocObj ..) (IsStrictTensor.assocObj ..)
    (by simpa only [IsStrictTensor.associator_hom] using associator_naturality_left f Z W)

private theorem assoc_middle (X : C) {Y Z : C} (f : Y ⟶ Z) (W : C) :
    (X ◁ f) ▷ W ≈ₐ X ◁ (f ▷ W) :=
  DiagramInterpretation.of_square (IsStrictTensor.assocObj ..) (IsStrictTensor.assocObj ..)
    (by simpa only [IsStrictTensor.associator_hom] using associator_naturality_middle X f W)

private theorem assoc_right (X Y : C) {Z W : C} (f : Z ⟶ W) :
    (X ⊗ Y) ◁ f ≈ₐ X ◁ (Y ◁ f) :=
  DiagramInterpretation.of_square (IsStrictTensor.assocObj ..) (IsStrictTensor.assocObj ..)
    (by simpa only [IsStrictTensor.associator_hom] using associator_naturality_right X Y f)

theorem central_left (Z : C) {X Y : C} {f : X ⟶ Y} (hf : IsCentral f) :
    IsCentral (Z ◁ f) := by
  constructor
  · intro A B g
    apply SameArrow.eq
    calc
      _ ≈ₐ (Z ◁ (f ▷ A)) ≫ Z ◁ (Y ◁ g) :=
        (assoc_middle Z f A).comp (assoc_right Z Y g)
      _ ≈ₐ Z ◁ (f ⋉ g) := .of_eq (whiskerLeft_comp ..).symm
      _ ≈ₐ Z ◁ (f ⋊ g) := .of_eq (congrArg (Z ◁ ·) (hf.1 g))
      _ ≈ₐ (Z ◁ (X ◁ g)) ≫ Z ◁ (f ▷ B) := .of_eq (whiskerLeft_comp ..)
      _ ≈ₐ _ := ((assoc_right Z X g).comp (assoc_middle Z f B)).symm
  · intro A B g
    apply SameArrow.eq
    calc
      _ ≈ₐ (g ▷ Z) ⋉ f := ((assoc_left g Z X).symm).comp (assoc_right B Z f).symm
      _ ≈ₐ (g ▷ Z) ⋊ f := .of_eq (hf.2 (g ▷ Z))
      _ ≈ₐ _ := (assoc_right A Z f).comp (assoc_left g Z Y)

theorem central_right (Z : C) {X Y : C} {f : X ⟶ Y} (hf : IsCentral f) :
    IsCentral (f ▷ Z) := by
  constructor
  · intro A B g
    apply SameArrow.eq
    calc
      _ ≈ₐ f ⋉ (Z ◁ g) := (assoc_left f Z A).comp (assoc_right Y Z g)
      _ ≈ₐ f ⋊ (Z ◁ g) := .of_eq (hf.1 (Z ◁ g))
      _ ≈ₐ _ := (assoc_right X Z g).symm.comp (assoc_left f Z B).symm
  · intro A B g
    apply SameArrow.eq
    calc
      _ ≈ₐ ((g ▷ X) ▷ Z) ≫ ((B ◁ f) ▷ Z) :=
        (assoc_left g X Z).symm.comp (assoc_middle B f Z).symm
      _ ≈ₐ (g ⋉ f) ▷ Z := .of_eq (comp_whiskerRight ..).symm
      _ ≈ₐ (g ⋊ f) ▷ Z := .of_eq (congrArg (· ▷ Z) (hf.2 g))
      _ ≈ₐ ((A ◁ f) ▷ Z) ≫ ((g ▷ Y) ▷ Z) := .of_eq (comp_whiskerRight ..)
      _ ≈ₐ _ := (assoc_middle A f Z).comp (assoc_left g Y Z)

theorem central_tensor {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y} (hf : IsCentral f)
    (hg : IsCentral g) : IsCentral (f ⊗ₘ g) :=
  (PremonoidalCategory.tensorHom_def f g).symm ▸
    (central_right X hf).comp (central_left B hg)

end Silmaril.RuntimeWires.Proofs.FullCenter
