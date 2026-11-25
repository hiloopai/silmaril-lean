module

public import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Basic

public section

namespace Silmaril.RuntimeWires.Proofs.DiagramInterpretation

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory SameArrow
open Diagram

universe u v u' v'

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [IsStrictTensor C]

theorem monoidal_tensor_assoc {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ₘ g) ⊗ₘ h ≈ₐ f ⊗ₘ g ⊗ₘ h :=
  of_square (IsStrictTensor.assocObj ..) (IsStrictTensor.assocObj ..)
    (by simpa only [IsStrictTensor.associator_hom] using associator_naturality f g h)

theorem monoidal_tensor_unit_left {X Y : C} (f : X ⟶ Y) :
    𝟙 (𝟙_ C) ⊗ₘ f ≈ₐ f := by
  rw [id_tensorHom]
  exact of_square (IsStrictTensor.leftObj X) (IsStrictTensor.leftObj Y)
    (by simpa only [IsStrictTensor.leftUnitor_hom] using leftUnitor_naturality f)

theorem monoidal_tensor_unit_right {X Y : C} (f : X ⟶ Y) :
    f ⊗ₘ 𝟙 (𝟙_ C) ≈ₐ f := by
  rw [tensorHom_id]
  exact of_square (IsStrictTensor.rightObj X) (IsStrictTensor.rightObj Y)
    (by simpa only [IsStrictTensor.rightUnitor_hom] using rightUnitor_naturality f)

omit [IsStrictTensor C] in
theorem monoidal_map_tensor {D : Type u} [Category.{v} D] [MonoidalCategory D]
    (F : D ⥤ C) (h : IsStrictTensorFunctor F) {A B X Y : D} (f : A ⟶ B) (g : X ⟶ Y) :
    F.map (f ⊗ₘ g) ≈ₐ F.map f ⊗ₘ F.map g := by
  rw [MonoidalCategory.tensorHom_def, F.map_comp, MonoidalCategory.tensorHom_def]
  exact (of_square (h.tensor A X) (h.tensor B X) (h.right f X)).comp
    (of_square (h.tensor B X) (h.tensor B Y) (h.left B g))

variable {O : Type u} {S : Signature.{u,v} O}

theorem monoidal_descend (I : Interpretation S C) {E : Diagram.Equations S}
    (extra : ∀ {A B} {f g : Diagram S A B}, E f g → I.eval f = I.eval g)
    {A B : List O} {f g : Diagram S A B} (h : Diagram.Congruence E f g) :
    I.eval f = I.eval g := by
  induction h with
  | equation h => exact extra h
  | refl => rfl
  | symm _ h => exact h.symm
  | trans _ _ h k => exact h.trans k
  | comp _ _ h k => exact congrArg₂ CategoryStruct.comp h k
  | tensor _ _ h k => simp only [Interpretation.eval, h, k]
  | id_comp => exact Category.id_comp _
  | comp_id => exact Category.comp_id _
  | comp_assoc => exact Category.assoc _ _ _
  | tensor_id A B =>
    exact ((eval_tensor I (.id A) (.id B)).trans
      ((SameArrow.of_eq (id_tensorHom_id _ _)).trans (.id (I.append A B).symm))).eq
  | tensor_comp f g h k =>
    exact ((eval_tensor I (.comp f g) (.comp h k)).trans
      ((SameArrow.of_eq (tensorHom_comp_tensorHom (I.eval f) (I.eval h)
        (I.eval g) (I.eval k)).symm).trans
        ((eval_tensor I f h).symm.comp (eval_tensor I g k).symm))).eq
  | tensor_unit_left f =>
    exact ((eval_reindex I _ _ _).trans ((eval_tensor I (.id []) f).trans
      (((SameArrow.id I.empty).tensor (.refl _)).trans
        (monoidal_tensor_unit_left (I.eval f))))).eq
  | tensor_unit_right f =>
    exact ((eval_reindex I _ _ _).trans ((eval_tensor I f (.id [])).trans
      (((SameArrow.refl _).tensor (.id I.empty)).trans
        (monoidal_tensor_unit_right (I.eval f))))).eq
  | tensor_assoc f g h =>
    exact ((eval_reindex I _ _ _).trans ((eval_tensor I (.tensor f g) h).trans
      (((eval_tensor I f g).tensor (.refl _)).trans
        ((monoidal_tensor_assoc (I.eval f) (I.eval g) (I.eval h)).trans
          (((SameArrow.refl _).tensor (eval_tensor I g h).symm).trans
            (eval_tensor I f (.tensor g h)).symm))))).eq

omit [IsStrictTensor C] in
theorem eval_determined (I : Interpretation S C) {E : Diagram.Equations S}
    (F : Presented S E ⥤ C) (strict : IsStrictTensorFunctor F)
    (objects : ∀ X, F.obj X = I.obj X.word)
    (generators : ∀ e : S.Edge,
      F.map (Presented.ofTerm (A := ⟨S.source e⟩) (B := ⟨S.target e⟩) (.gen e)) ≈ₐ I.edge e)
    {A B : List O} (f : Diagram S A B) :
    F.map (Presented.ofTerm (A := ⟨A⟩) (B := ⟨B⟩) f) ≈ₐ I.eval f := by
  induction f with
  | id A =>
    exact (SameArrow.of_eq (F.map_id ⟨A⟩)).trans (.id (objects ⟨A⟩))
  | gen e => exact generators e
  | comp f g hf hg =>
    exact (SameArrow.of_eq (F.map_comp (Presented.ofTerm f) (Presented.ofTerm g))).trans
      (hf.comp hg)
  | tensor f g hf hg =>
    exact (monoidal_map_tensor F strict (Presented.ofTerm f) (Presented.ofTerm g)).trans
      ((hf.tensor hg).trans (eval_tensor I f g).symm)

end Silmaril.RuntimeWires.Proofs.DiagramInterpretation
