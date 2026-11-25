module

public import Silmaril.Proofs.Semantics.RuntimeWires.GradedInterpretation.Crossings

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

private theorem subcounts (A B : List (Wire G.Obj)) (h : runtimeCount (A ++ B) ≤ 1) :
    runtimeCount A ≤ 1 ∧ runtimeCount B ≤ 1 := by
  rw [runtimeCount_append] at h
  omega

/-- All runtime congruence rules are sound in degrees zero and one. -/
theorem computation_descend {A B : List (Wire G.Obj)} {f g : Diagram (signature G) A B}
    (h : Diagram.Congruence (Relations G) f g) (bound : runtimeCount A ≤ 1) :
    (I).eval f = (I).eval g := by
  induction h with
  | equation h => exact extra_equations F h
  | refl => rfl
  | symm _ h => exact (h bound).symm
  | trans _ _ h k => exact (h bound).trans (k bound)
  | @comp A B D f f' g g' _ _ hf hg =>
    exact congrArg₂ CategoryStruct.comp (hf bound)
      (hg (preservesRuntime f ▸ bound))
  | @tensor A B D E f f' g g' _ _ hf hg =>
    obtain ⟨a, b⟩ := subcounts A D bound
    simp only [Interpretation.eval, hf a, hg b]
  | id_comp => exact Category.id_comp _
  | comp_id => exact Category.comp_id _
  | comp_assoc => exact Category.assoc _ _ _
  | tensor_id A B =>
    exact ((eval_tensor I (.id A) (.id B)).trans
      ((SameArrow.of_eq (sequential_id _ _)).trans (.id ((I).append A B).symm))).eq
  | @tensor_comp A B D X Y Z f g h k =>
    have zero : runtimeCount A = 0 ∨ runtimeCount X = 0 := by
      rw [runtimeCount_append] at bound
      omega
    have exchange := zero.elim
      (fun z => (central_zero F g ((preservesRuntime f).symm.trans z)).1 ((I).eval h))
      (fun z => (central_zero F h z).2 ((I).eval g))
    exact ((eval_tensor I (.comp f g) (.comp h k)).trans
      ((SameArrow.of_eq (sequential_comp ((I).eval f) ((I).eval g) ((I).eval h) ((I).eval k)
        exchange).symm).trans ((eval_tensor I f h).symm.comp (eval_tensor I g k).symm))).eq
  | tensor_unit_left f =>
    exact ((eval_reindex I _ _ _).trans ((eval_tensor I (.id []) f).trans
      (((SameArrow.id (I).empty).tensor (.refl _)).trans
        (premonoidal_tensor_unit_left ((I).eval f))))).eq
  | tensor_unit_right f =>
    exact ((eval_reindex I _ _ _).trans ((eval_tensor I f (.id [])).trans
      (((SameArrow.refl _).tensor (.id (I).empty)).trans
        (premonoidal_tensor_unit_right ((I).eval f))))).eq
  | tensor_assoc f g h =>
    exact ((eval_reindex I _ _ _).trans ((eval_tensor I (.tensor f g) h).trans
      (((eval_tensor I f g).tensor (.refl _)).trans
        ((premonoidal_tensor_assoc ((I).eval f) ((I).eval g) ((I).eval h)).trans
          (((SameArrow.refl _).tensor (eval_tensor I g h).symm).trans
            (eval_tensor I f (.tensor g h)).symm))))).eq

end Silmaril.RuntimeWires.Proofs.GradedInterpretation
