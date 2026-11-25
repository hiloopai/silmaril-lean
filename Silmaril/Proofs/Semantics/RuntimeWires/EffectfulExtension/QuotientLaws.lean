module

public import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulExtension.Maps
public import Silmaril.Proofs.Semantics.RuntimeWires.GradedInterpretation.Crossings
public import Silmaril.Proofs.Semantics.RuntimeWires.PureInclusion.Naturality
public import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Whiskering

public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulExtension

open CategoryTheory Diagram Presentation
open DiagramInterpretation
open scoped MonoidalCategory SameArrow

universe u v u' v' u₁ v₁

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

variable (F : T.Assignment G)

theorem value_count (A : List G.Obj) : runtimeCount (valueWord (G := G) A).word = 0 :=
  runtimeCount_values A

theorem small_value (A : List G.Obj) : runtimeCount (valueWord (G := G) A).word ≤ 1 :=
  (value_count (G := G) A).symm ▸ Nat.zero_le 1

theorem small_comp (X : Computations G) : runtimeCount X.boundary.word ≤ 1 :=
  Nat.le_of_eq (StrictEffectful.Assignment.computation_count X)

theorem runtime_tensor_count (X Y : Runtime G) :
    runtimeCount (X ⊗ Y).word = runtimeCount X.word + runtimeCount Y.word :=
  runtimeCount_append X.word Y.word

theorem small_tensor_right (X : Computations G) (A : List G.Obj) :
    runtimeCount (X.boundary ⊗ valueWord A).word ≤ 1 := by
  rw [runtime_tensor_count, StrictEffectful.Assignment.computation_count, value_count]

theorem small_tensor_left (A : List G.Obj) (X : Computations G) :
    runtimeCount (valueWord A ⊗ X.boundary).word ≤ 1 := by
  rw [runtime_tensor_count, value_count, StrictEffectful.Assignment.computation_count]

theorem eval_congr {A B X Y : Runtime G} {f : A ⟶ B} {g : X ⟶ Y}
    (h : f ≈ₐ g) (ha : runtimeCount A.word ≤ 1) (hx : runtimeCount X.word ≤ 1) :
    F.evaluate f ha ≈ₐ F.evaluate g hx := by
  obtain ⟨rfl, rfl, h⟩ := h
  cases eq_of_heq h
  exact SameArrow.refl _

theorem eval_tensor_rel {A B X Y : Runtime G} (f : A ⟶ B) (g : X ⟶ Y)
    (h : runtimeCount (A ⊗ X).word ≤ 1) (ha : runtimeCount A.word ≤ 1)
    (hx : runtimeCount X.word ≤ 1) :
    F.evaluate (f ⊗ₘ g) h ≈ₐ F.evaluate f ha ⊗ₘ F.evaluate g hx :=
  (SameArrow.of_eq (F.evaluate_tensor f g h ha hx)).trans (transport_eq _ _ _)

theorem eval_whisker_right {A B : Runtime G} (f : A ⟶ B) (X : Runtime G)
    (h : runtimeCount (A ⊗ X).word ≤ 1) (ha : runtimeCount A.word ≤ 1)
    (hx : runtimeCount X.word ≤ 1) :
    F.evaluate (f ▷ X) h ≈ₐ F.evaluate f ha ▷ F.boundary X.word := by
  rw [← MonoidalCategory.tensorHom_id]
  refine (eval_tensor_rel F f (𝟙 X) h ha hx).trans (.of_eq ?_)
  simp only [F.evaluate_id, PremonoidalCategory.tensorHom_def, PremonoidalCategory.leftTensor,
    PremonoidalCategory.whiskerLeft_id, Category.comp_id]

theorem eval_whisker_left (X : Runtime G) {A B : Runtime G} (f : A ⟶ B)
    (h : runtimeCount (X ⊗ A).word ≤ 1) (ha : runtimeCount A.word ≤ 1)
    (hx : runtimeCount X.word ≤ 1) :
    F.evaluate (X ◁ f) h ≈ₐ F.boundary X.word ◁ F.evaluate f ha := by
  rw [← MonoidalCategory.id_tensorHom]
  refine (eval_tensor_rel F (𝟙 X) f h hx ha).trans (.of_eq ?_)
  simp only [F.evaluate_id, PremonoidalCategory.tensorHom_def, PremonoidalCategory.leftTensor,
    PremonoidalCategory.id_whiskerRight, Category.id_comp]

/-- An isomorphism between small runtime boundaries evaluates to an isomorphism. -/
def evalIso {A B : Runtime G} (i : A ≅ B) (ha : runtimeCount A.word ≤ 1)
    (hb : runtimeCount B.word ≤ 1) : F.boundary A.word ≅ F.boundary B.word where
  hom := F.evaluate i.hom ha
  inv := F.evaluate i.inv hb
  hom_inv_id := (F.evaluate_comp i.hom i.inv ha hb).symm.trans
    ((congrArg (F.evaluate · ha) i.hom_inv_id).trans (F.evaluate_id A ha))
  inv_hom_id := (F.evaluate_comp i.inv i.hom hb ha).symm.trans
    ((congrArg (F.evaluate · hb) i.inv_hom_id).trans (F.evaluate_id B hb))

theorem eval_crossing (A : List G.Obj) (h : runtimeCount ((runtime G) ⊗ valueWord A).word ≤ 1) :
    F.evaluate (crossingWord (G := G) A).hom h ≈ₐ
      𝟙 (F.boundary ((runtime G) ⊗ valueWord A).word) :=
  (SameArrow.of_eq (congrArg (F.evaluate · h) (PureInclusion.crossingWord_slide A))).trans
    (GradedInterpretation.slideRight_id F A)

theorem eval_splitLeft (A B : Computations G) :
    F.evaluate (A.splitLeft B).hom (small_comp (A.concat B)) ≈ₐ
      𝟙 (F.boundary (A.concat B).boundary.word) := by
  let X := (runtime G) ⊗ valueWord A.word
  let Y := valueWord (G := G) B.word
  have hx : runtimeCount X.word ≤ 1 := small_comp A
  have hy : runtimeCount Y.word ≤ 1 := small_value B.word
  have hxy : runtimeCount (X ⊗ Y).word ≤ 1 := small_tensor_right A B.word
  have e := (eval_congr F (RuntimeCoherence.splitLeft_hom A B) (small_comp (A.concat B)) hxy).trans
    (eval_whisker_right F (crossingWord A.word).hom Y hxy hx hy)
  have eh := (eval_crossing F A.word hx).whiskerRight (X := F.boundary Y.word) rfl
  refine e.trans (eh.trans ((SameArrow.of_eq (PremonoidalCategory.id_whiskerRight _ _)).trans ?_))
  exact SameArrow.id e.source.symm

theorem eval_splitLeft_inv (A B : Computations G) :
    F.evaluate (A.splitLeft B).inv (small_tensor_left A.word B) ≈ₐ
      𝟙 (F.boundary (valueWord A.word ⊗ B.boundary).word) := by
  let i := evalIso F (A.splitLeft B) (small_comp (A.concat B)) (small_tensor_left A.word B)
  have e : i.hom ≈ₐ (Iso.refl (F.boundary (A.concat B).boundary.word)).hom := eval_splitLeft F A B
  exact e.inv.trans (.id e.target.symm)

end Silmaril.RuntimeWires.Proofs.EffectfulExtension
