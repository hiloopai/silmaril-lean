module

public import Silmaril.Semantics.RuntimeWires.DiagramInterpretation.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Transport

public section

namespace Silmaril.RuntimeWires.Proofs.DiagramInterpretation

open CategoryTheory
open scoped MonoidalCategory SameArrow
open Diagram

universe u v u' v'

section
variable {C : Type u'} [Category.{v'} C]

theorem of_square {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y} (p : A = X) (q : B = Y)
    (h : f ≫ eqToHom q = eqToHom p ≫ g) : f ≈ₐ g := by
  subst p
  subst q
  exact SameArrow.of_eq (by simpa using h)

theorem transport_eq {A B X Y : C} (p : A = X) (q : B = Y) (f : A ⟶ B) :
    Interpretation.transport p q f ≈ₐ f := by
  subst p
  subst q
  simpa [Interpretation.transport] using SameArrow.refl f

theorem map_congr {V : Type u} [Category.{v} V] (F : V ⥤ C)
    {A B X Y : V} {f : A ⟶ B} {g : X ⟶ Y} (h : f ≈ₐ g) :
    F.map f ≈ₐ F.map g := by
  obtain ⟨rfl, rfl, h⟩ := h
  cases eq_of_heq h
  exact SameArrow.refl _

end

section
variable {C : Type u'} [Category.{v'} C] [MonoidalCategoryStruct C]
variable {O : Type u} {S : Signature.{u,v} O}

theorem eval_tensor (I : Interpretation S C) {A B D E : List O}
    (f : Diagram S A B) (g : Diagram S D E) :
    I.eval (.tensor f g) ≈ₐ I.eval f ⊗ₘ I.eval g :=
  transport_eq _ _ _

theorem eval_reindex (I : Interpretation S C) {A B D E : List O}
    (p : A = D) (q : B = E) (f : Diagram S A B) :
    I.eval (Diagram.reindex p q f) ≈ₐ I.eval f := by
  subst p
  subst q
  exact SameArrow.refl _

end

section
variable {C : Type u'} [Category.{v'} C] [MonoidalCategoryStruct C] [IsStrictTensor C]

theorem wordObject_append {O : Type u} (f : O → C) (A B : List O) :
    StrictEffectful.wordObject f (A ++ B) =
      StrictEffectful.wordObject f A ⊗ StrictEffectful.wordObject f B := by
  induction A with
  | nil => exact (IsStrictTensor.leftObj _).symm
  | cons x A ih => exact (congrArg (f x ⊗ ·) ih).trans (IsStrictTensor.assocObj _ _ _).symm

end
end Silmaril.RuntimeWires.Proofs.DiagramInterpretation
