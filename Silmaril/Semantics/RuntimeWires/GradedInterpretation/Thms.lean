module

public import Silmaril.Semantics.RuntimeWires.GradedInterpretation.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.GradedInterpretation.Descent

@[expose] public section

namespace Silmaril.RuntimeWires.StrictEffectful.Assignment

open CategoryTheory Diagram Presentation
open scoped MonoidalCategory

universe u v u' v' u₁ v₁

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

variable (F : T.Assignment G)

/-- Lemma 3.13, quotient descent. The runtime interpretation validates every
congruence rule on a word with at most one runtime. -/
theorem computation_respectsCongruence {A B : List (Wire G.Obj)}
    {f g : Diagram (signature G) A B} (h : Diagram.Congruence (Relations G) f g)
    (bound : runtimeCount A ≤ 1) :
    F.computationInterpretation.eval f = F.computationInterpretation.eval g :=
  Proofs.GradedInterpretation.computation_descend F h bound

/-- Evaluate an arrow of the runtime quotient at count zero or one. -/
def evaluate {A B : Runtime G} (f : A ⟶ B) (bound : runtimeCount A.word ≤ 1) :
    F.boundary A.word ⟶ F.boundary B.word :=
  Quotient.lift F.computationInterpretation.eval
    (fun _ _ h => F.computation_respectsCongruence h bound) f

theorem evaluate_id (A : Runtime G) (h : runtimeCount A.word ≤ 1) :
    F.evaluate (𝟙 A) h = 𝟙 (F.boundary A.word) := rfl

theorem evaluate_comp {A B D : Runtime G} (f : A ⟶ B) (g : B ⟶ D)
    (ha : runtimeCount A.word ≤ 1) (hb : runtimeCount B.word ≤ 1) :
    F.evaluate (f ≫ g) ha = F.evaluate f ha ≫ F.evaluate g hb :=
  Quotient.inductionOn₂ f g (fun _ _ => rfl)

theorem evaluate_eqToHom {A B : Runtime G} (p : A = B) (h : runtimeCount A.word ≤ 1) :
    F.evaluate (eqToHom p) h = eqToHom (congrArg (fun X => F.boundary X.word) p) := by
  subst p
  rfl

theorem evaluate_tensor {A B D E : Runtime G} (f : A ⟶ B) (g : D ⟶ E)
    (h : runtimeCount (A ⊗ D).word ≤ 1) (ha : runtimeCount A.word ≤ 1)
    (hd : runtimeCount D.word ≤ 1) :
    F.evaluate (f ⊗ₘ g) h =
      Interpretation.transport (F.boundary_append A.word D.word).symm
        (F.boundary_append B.word E.word).symm (F.evaluate f ha ⊗ₘ F.evaluate g hd) :=
  Quotient.inductionOn₂ f g (fun _ _ => rfl)

end Silmaril.RuntimeWires.StrictEffectful.Assignment
