module

public import Silmaril.Semantics.RuntimeWires.DiagramInterpretation.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Monoidal

@[expose] public section

namespace Silmaril.RuntimeWires.Diagram.Interpretation

open CategoryTheory
open scoped MonoidalCategory

universe u v u' v'

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C] [IsStrictTensor C]
variable {O : Type u} {S : Signature.{u,v} O}

/-- Word interpretation in an arbitrary strict monoidal category. -/
def ofGenerators (f : O → C)
    (edge : ∀ e : S.Edge, StrictEffectful.wordObject f (S.source e) ⟶
      StrictEffectful.wordObject f (S.target e)) : Interpretation S C where
  obj := StrictEffectful.wordObject f
  empty := rfl
  append A B := by exact Proofs.DiagramInterpretation.wordObject_append f A B
  edge := edge

/-- Evaluation descends when the extra relations are validated in the target.
Tensor interchange, associativity and units are supplied by the target. -/
theorem respectsCongruence (I : Interpretation S C) {E : Diagram.Equations S}
    (extra : ∀ {A B} {f g : Diagram S A B}, E f g → I.eval f = I.eval g)
    {A B : List O} {f g : Diagram S A B} (h : Diagram.Congruence E f g) :
    I.eval f = I.eval g :=
  Proofs.DiagramInterpretation.monoidal_descend I extra h

/-- Interpretation of a presented monoidal category. -/
def functor (I : Interpretation S C) (E : Diagram.Equations S)
    (extra : ∀ {A B} {f g : Diagram S A B}, E f g → I.eval f = I.eval g) :
    Diagram.Presented S E ⥤ C where
  obj X := I.obj X.word
  map := Quotient.lift I.eval (fun _ _ h => I.respectsCongruence extra h)
  map_id _ := rfl
  map_comp f g := Quotient.inductionOn₂ f g (fun _ _ => rfl)

@[simp] theorem functor_map_ofTerm (I : Interpretation S C) (E : Diagram.Equations S)
    (extra : ∀ {A B} {f g : Diagram S A B}, E f g → I.eval f = I.eval g)
    {A B : Diagram.Presented S E} (f : Diagram S A.word B.word) :
    (I.functor E extra).map (Diagram.Presented.ofTerm f) = I.eval f :=
  rfl

/-- An extending functor preserves both tensors, the prescribed word objects,
and the generator assignments after identifying their boundaries. -/
structure Extends (I : Interpretation S C) (E : Diagram.Equations S)
    (F : Diagram.Presented S E ⥤ C) : Prop where
  strict : IsStrictTensorFunctor F
  objects (X : Diagram.Presented S E) : F.obj X = I.obj X.word
  generators (e : S.Edge) :
    F.map (Diagram.Presented.ofTerm (A := ⟨S.source e⟩) (B := ⟨S.target e⟩) (.gen e)) ≫
        eqToHom (objects ⟨S.target e⟩) =
      eqToHom (objects ⟨S.source e⟩) ≫ I.edge e

theorem functor_extends (I : Interpretation S C) (E : Diagram.Equations S)
    (extra : ∀ {A B} {f g : Diagram S A B}, E f g → I.eval f = I.eval g) :
    I.Extends E (I.functor E extra) where
  strict :=
    { unit := I.empty
      tensor A B := I.append A.word B.word
      left X {Y Z} f := by
        refine Quotient.inductionOn f fun f => ?_
        exact ((Proofs.DiagramInterpretation.eval_tensor I (.id X.word) f).trans
          (Proofs.SameArrow.of_eq (MonoidalCategory.id_tensorHom _ _))).square
          (I.append X.word Y.word) (I.append X.word Z.word)
      right {X Y} f Z := by
        refine Quotient.inductionOn f fun f => ?_
        exact ((Proofs.DiagramInterpretation.eval_tensor I f (.id Z.word)).trans
          (Proofs.SameArrow.of_eq (MonoidalCategory.tensorHom_id _ _))).square
          (I.append X.word Z.word) (I.append Y.word Z.word) }
  objects _ := rfl
  generators _ := (Category.comp_id _).trans (Category.id_comp _).symm

/-- Algebraic universal property of a strict monoidal presentation. In particular,
taking the extra relations empty gives the pure extension in Lemma 3.13. -/
theorem uniqueExtension (I : Interpretation S C) (E : Diagram.Equations S)
    (extra : ∀ {A B} {f g : Diagram S A B}, E f g → I.eval f = I.eval g) :
    ∃! F : Diagram.Presented S E ⥤ C, I.Extends E F := by
  refine ⟨I.functor E extra, I.functor_extends E extra, ?_⟩
  intro F h
  apply Functor.hext h.objects
  intro X Y f
  refine Quotient.inductionOn f fun f => ?_
  exact (Proofs.DiagramInterpretation.eval_determined I F h.strict h.objects
    (fun e => Proofs.DiagramInterpretation.of_square _ _ (h.generators e)) f).arrow

end Silmaril.RuntimeWires.Diagram.Interpretation
