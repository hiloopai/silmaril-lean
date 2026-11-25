module

public import Silmaril.Proofs.Semantics.RuntimeWires.GradedInterpretation.Purity

public section

namespace Silmaril.RuntimeWires.Proofs.GradedInterpretation

open CategoryTheory Diagram Presentation
open DiagramInterpretation
open scoped MonoidalCategory SameArrow

universe u v u' v' u₁ v₁

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

variable (F : T.Assignment G)

local notation "I" => F.computationInterpretation

omit [PremonoidalCategory C] [IsStrictTensor C] in
private theorem drop_left {A B D X Y : C} {f : A ⟶ B} {g : B ⟶ D} {h : X ⟶ Y}
    (p : f ≈ₐ 𝟙 A) (q : g ≈ₐ h) : f ≫ g ≈ₐ h := by
  have e := (p.trans (.id (p.target.symm.trans q.source))).comp q
  simpa only [Category.id_comp] using e

omit [PremonoidalCategory C] [IsStrictTensor C] in
private theorem drop_right {A B D X Y : C} {f : A ⟶ B} {g : B ⟶ D} {h : X ⟶ Y}
    (p : f ≈ₐ h) (q : g ≈ₐ 𝟙 B) : f ≫ g ≈ₐ h := by
  have e := p.comp (q.trans (.id p.target))
  simpa only [Category.comp_id] using e

private theorem tensor_ids {A B D E : List (Wire G.Obj)}
    {f : Diagram (signature G) A B} {g : Diagram (signature G) D E}
    (p : (I).eval f ≈ₐ 𝟙 ((I).obj A)) (q : (I).eval g ≈ₐ 𝟙 ((I).obj D)) :
    (I).eval (.tensor f g) ≈ₐ 𝟙 ((I).obj (A ++ D)) :=
  (eval_tensor I f g).trans ((p.tensor q).trans
    ((SameArrow.of_eq (sequential_id _ _)).trans (.id ((I).append A D).symm)))

/-- Moving the runtime to the right of any word interprets as an identity. -/
theorem slideRight_id (A : List G.Obj) :
    (I).eval (slideRight (G := G) A) ≈ₐ 𝟙 ((I).obj (none :: values A)) := by
  induction A with
  | nil => exact SameArrow.refl _
  | cons x A ih =>
    exact drop_right
      (tensor_ids F (SameArrow.refl (𝟙 ((I).obj [none, some x])))
        (SameArrow.refl (𝟙 ((I).obj (values A)))))
      (tensor_ids F (SameArrow.refl (𝟙 ((I).obj [some x]))) ih)

/-- Moving the runtime to the left of any word interprets as an identity. -/
theorem slideLeft_id (A : List G.Obj) :
    (I).eval (slideLeft (G := G) A) ≈ₐ 𝟙 ((I).obj (values A ++ [none])) := by
  induction A with
  | nil => exact SameArrow.refl _
  | cons x A ih =>
    exact drop_right
      (tensor_ids F (SameArrow.refl (𝟙 ((I).obj [some x]))) ih)
      (tensor_ids F (SameArrow.refl (𝟙 ((I).obj [some x, none])))
        (SameArrow.refl (𝟙 ((I).obj (values A)))))

theorem tensor_runtime_right {A B : List (Wire G.Obj)} (f : Diagram (signature G) A B) :
    (I).eval (.tensor f (.id [none])) ≈ₐ (I).eval f :=
  (eval_tensor I f (.id [none])).trans (((SameArrow.refl _).tensor
    (.id F.boundary_runtime)).trans (premonoidal_tensor_unit_right ((I).eval f)))

theorem tensor_runtime_left {A B : List (Wire G.Obj)} (f : Diagram (signature G) A B) :
    (I).eval (.tensor (.id [none]) f) ≈ₐ (I).eval f :=
  (eval_tensor I (.id [none]) f).trans (((SameArrow.id F.boundary_runtime).tensor
    (.refl _)).trans (premonoidal_tensor_unit_left ((I).eval f)))

/-- The four equations of Figure 9 hold under the erasing interpretation. -/
theorem extra_equations {A B : List (Wire G.Obj)} {f g : Diagram (signature G) A B}
    (h : Relations G f g) : (I).eval f = (I).eval g := by
  cases h with
  | cancelRight x => exact Category.id_comp _
  | cancelLeft x => exact Category.id_comp _
  | pureRight e =>
    exact ((drop_left (slideRight_id F (G.pure.source e))
      (tensor_runtime_right F (pureDiagram e))).trans
      (drop_right (tensor_runtime_left F (pureDiagram e))
        (slideRight_id F (G.pure.target e))).symm).eq
  | pureLeft e =>
    exact ((drop_left (slideLeft_id F (G.pure.source e))
      (tensor_runtime_left F (pureDiagram e))).trans
      (drop_right (tensor_runtime_right F (pureDiagram e))
        (slideLeft_id F (G.pure.target e))).symm).eq

end Silmaril.RuntimeWires.Proofs.GradedInterpretation
