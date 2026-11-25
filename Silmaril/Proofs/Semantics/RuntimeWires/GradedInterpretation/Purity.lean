module

public import Silmaril.Semantics.RuntimeWires.GradedInterpretation.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Premonoidal

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
local notation "P" => F.valuesInterpretation

/-- The interpretation in degree zero agrees with interpretation in the chosen pure category. -/
theorem eval_zero {A B : List (Wire G.Obj)} (f : Diagram (signature G) A B)
    (h : runtimeCount A = 0) :
    (I).eval f ≈ₐ T.pure.map ((P).eval (erasePure f h)) := by
  induction f with
  | id => exact SameArrow.of_eq (T.pure.map_id _).symm
  | gen e =>
    cases e with
    | pure e =>
      let obj := T.pure.obj ∘ StrictEffectful.wordObject F.obj
      exact (transport_eq (congrArg obj (eraseBoundary_values (G.pure.source e))).symm
        (congrArg obj (eraseBoundary_values (G.pure.target e))).symm (T.pure.map (F.pure e))).trans
        (DiagramInterpretation.map_congr T.pure (eval_reindex P _ _ (.gen e)).symm)
    | effect e =>
      change (runtimeCount (values (G.effect.source e))).succ = 0 at h
      exact False.elim (Nat.noConfusion h)
    | moveRight _ | moveLeft _ => exact False.elim (Nat.noConfusion h)
  | comp f g hf hg =>
    have hb := (preservesRuntime f).symm.trans h
    exact ((hf h).comp (hg hb)).trans
      (SameArrow.of_eq (T.pure.map_comp ((P).eval (erasePure f h)) ((P).eval (erasePure g hb))).symm)
  | @tensor A B D E f g hf hg =>
    have z := Nat.add_eq_zero_iff.mp ((runtimeCount_append A D).symm.trans h)
    have he := ((eval_reindex P (eraseBoundary_append A D).symm
      (eraseBoundary_append B E).symm (.tensor (erasePure f z.1) (erasePure g z.2))).trans
      (eval_tensor P (erasePure f z.1) (erasePure g z.2)))
    exact (eval_tensor I f g).trans (((hf z.1).tensor (hg z.2)).trans
      ((map_tensor T.pure T.strict ((P).eval (erasePure f z.1)) ((P).eval (erasePure g z.2))).symm.trans
        (DiagramInterpretation.map_congr T.pure he).symm))

theorem central_zero {A B : List (Wire G.Obj)} (f : Diagram (signature G) A B)
    (h : runtimeCount A = 0) : PremonoidalCategory.IsCentral ((I).eval f) := by
  have eq := (eval_zero F f h).eq
  rw [eq]
  exact T.central ((P).eval (erasePure f h))

end Silmaril.RuntimeWires.Proofs.GradedInterpretation
