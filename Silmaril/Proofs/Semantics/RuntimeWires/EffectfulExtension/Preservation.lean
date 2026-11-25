module

public import Silmaril.Semantics.RuntimeWires.EffectfulExtension.Maps
public import Silmaril.Semantics.RuntimeWires.ZeroRuntimeEquivalence.Thms
public import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulExtension.QuotientLaws

public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulExtension

open CategoryTheory Diagram Presentation
open DiagramInterpretation
open scoped MonoidalCategory SameArrow

universe u v u' v' u₁ v₁

section
variable {C : Type u'} [Category.{v'} C]

private theorem drop_left {A B D X Y : C} {f : A ⟶ B} {g : B ⟶ D} {h : X ⟶ Y}
    (p : f ≈ₐ 𝟙 A) (q : g ≈ₐ h) : f ≫ g ≈ₐ h := by
  have e := (p.trans (.id (p.target.symm.trans q.source))).comp q
  simpa only [Category.id_comp] using e

private theorem drop_right {A B D X Y : C} {f : A ⟶ B} {g : B ⟶ D} {h : X ⟶ Y}
    (p : f ≈ₐ h) (q : g ≈ₐ 𝟙 B) : f ≫ g ≈ₐ h := by
  have e := p.comp (q.trans (.id p.target))
  simpa only [Category.comp_id] using e

end

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

variable (F : T.Assignment G)

local notation "H" => F.computationExtension

theorem computation_right {X Y : Computations G} (f : X ⟶ Y) (Z : Computations G) :
    (H).map (f ▷ Z) ≫ eqToHom (F.computation_append Y Z) =
      eqToHom (F.computation_append X Z) ≫ (H).map f ▷ (H).obj Z := by
  let r : X.boundary ⟶ Y.boundary := f
  have e := eval_congr F (RuntimeCoherence.right_normal f Z)
    (small_comp (X.concat Z)) (small_tensor_right X Z.word)
  have eq := (map_computation F (X.concat Z) (Y.concat Z) (f ▷ Z)).trans
    (e.trans ((eval_whisker_right F r (valueWord Z.word) (small_tensor_right X Z.word)
      (small_comp X) (small_value Z.word)).trans
      ((map_computation F X Y f).symm.whiskerRight (F.computation_boundary Z))))
  exact eq.square (F.computation_append X Z) (F.computation_append Y Z)

theorem computation_left (X : Computations G) {Y Z : Computations G} (f : Y ⟶ Z) :
    (H).map (X ◁ f) ≫ eqToHom (F.computation_append X Z) =
      eqToHom (F.computation_append X Y) ≫ (H).obj X ◁ (H).map f := by
  let r : Y.boundary ⟶ Z.boundary := f
  let s := (X.splitLeft Y).hom
  let t := (X.splitLeft Z).inv
  let q := valueWord X.word ◁ r
  have hs := small_comp (X.concat Y)
  have hy := small_tensor_left X.word Y
  have hz := small_tensor_left X.word Z
  have e₁ := (F.evaluate_comp s (q ≫ t) hs hy).trans
    (congrArg (F.evaluate s hs ≫ ·) (F.evaluate_comp q t hy hz))
  have e₂ := eval_whisker_left F (valueWord X.word) r hy (small_comp Y) (small_value X.word)
  have e₃ := drop_left (eval_splitLeft F X Y) (drop_right e₂ (eval_splitLeft_inv F X Z))
  have eq := (map_computation F (X.concat Y) (X.concat Z) (X ◁ f)).trans
    ((SameArrow.of_eq e₁).trans
      (e₃.trans ((map_computation F Y Z f).symm.whiskerLeft (F.computation_boundary X))))
  exact eq.square (F.computation_append X Y) (F.computation_append X Z)

theorem computation_strict : IsStrictTensorFunctor (H) where
  unit := T.strict.unit
  tensor := F.computation_append
  left := computation_left F
  right := computation_right F

theorem effect_generator (e : G.effect.Edge) :
    (H).map (effectGenerator G e) = F.effect e :=
  ((map_computation F ⟨G.effect.source e⟩ ⟨G.effect.target e⟩ (effectGenerator G e)).trans
    (transport_eq (F.computation_boundary ⟨G.effect.source e⟩).symm
      (F.computation_boundary ⟨G.effect.target e⟩).symm (F.effect e))).eq

private theorem eval_zero_quotient {X Y : Pure G}
    (f : (pureValues G).obj X ⟶ (pureValues G).obj Y) :
    F.evaluate f (small_value X.word) ≈ₐ
      T.pure.map (F.valueExtension.map (eraseValueMorphism f)) := by
  refine Quotient.inductionOn f fun t => ?_
  exact (GradedInterpretation.eval_zero F t (runtimeCount_values X.word)).trans
    (DiagramInterpretation.map_congr T.pure ((eval_reindex F.valuesInterpretation
      (eraseBoundary_values X.word) (eraseBoundary_values Y.word) (erasePure t
        (runtimeCount_values X.word))).symm))

theorem pure_square : pureInclusion G ⋙ (H) = F.valueExtension ⋙ T.pure := by
  refine Functor.hext (fun X : Pure G => show F.computationObject (pureObject X) =
    T.pure.obj (StrictEffectful.wordObject F.obj X.word) from rfl) ?_
  intro X Y f
  let r := (pureValues G).map f
  have h := small_comp (pureObject X)
  have eh := (eval_zero_quotient F r).trans (.of_eq
    (congrArg (fun f => T.pure.map (F.valueExtension.map f)) (eraseValueMorphism_map f)))
  have er := (eval_whisker_left F (runtime G) r h (small_value X.word) (Nat.le_refl 1)).trans
    (eh.whiskerLeft F.boundary_runtime)
  have eu := of_square (IsStrictTensor.leftObj _) (IsStrictTensor.leftObj _)
    (by simpa only [IsStrictTensor.leftUnitor_hom] using
      PremonoidalCategory.leftUnitor_naturality (T.pure.map (F.valueExtension.map f)))
  exact ((map_computation F (pureObject X) (pureObject Y) ((pureInclusion G).map f)).trans
    (er.trans eu)).arrow

end Silmaril.RuntimeWires.Proofs.EffectfulExtension
