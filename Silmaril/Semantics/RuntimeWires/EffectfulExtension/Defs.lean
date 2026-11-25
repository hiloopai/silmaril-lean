module

public import Silmaril.Semantics.RuntimeWires.GradedInterpretation.Thms

@[expose] public section

/-!
# Extension on pure values and computations

Lemma 3.13 (pp. 9:10–9:13) of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires

open CategoryTheory Diagram Presentation
open scoped MonoidalCategory

universe u v u' v' u₁ v₁

namespace Presentation

/-- The computation induced by an effectful generator, with the runtime on the left. -/
def effectGenerator (G : EffectfulPolygraph.{u₁,v₁}) (e : G.effect.Edge) :
    (⟨G.effect.source e⟩ : Computations G) ⟶ ⟨G.effect.target e⟩ :=
  Diagram.Presented.ofTerm (A := (⟨G.effect.source e⟩ : Computations G).boundary)
    (B := (⟨G.effect.target e⟩ : Computations G).boundary) (.gen (S := signature G) (Edge.effect e))

end Presentation

namespace StrictEffectful.Assignment

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

theorem computation_count (X : Computations G) : runtimeCount X.boundary.word = 1 :=
  congrArg Nat.succ (runtimeCount_values X.word)

variable (F : T.Assignment G)

/-- Extend the pure generators to the pure presentation. -/
def valueExtension : Pure G ⥤ V :=
  F.valuesInterpretation.functor (fun _ _ => False) False.elim

/-- The object of the computation target underlying the interpreted value word. -/
def computationObject (X : Computations G) : C :=
  T.pure.obj (wordObject F.obj X.word)

theorem computation_boundary (X : Computations G) :
    F.boundary X.boundary.word = F.computationObject X :=
  congrArg (T.pure.obj ∘ wordObject F.obj) (eraseBoundary_values X.word)

theorem computation_append (X Y : Computations G) :
    F.computationObject (X.concat Y) = F.computationObject X ⊗ F.computationObject Y :=
  (congrArg T.pure.obj (F.valuesInterpretation.append X.word Y.word)).trans (T.strict.tensor _ _)

/-- Evaluate a braid-clique morphism at its leftmost component. -/
def computationMap {X Y : Computations G} (f : X ⟶ Y) :
    F.computationObject X ⟶ F.computationObject Y :=
  Interpretation.transport (F.computation_boundary X) (F.computation_boundary Y)
    (F.evaluate (show X.boundary ⟶ Y.boundary from f) (Nat.le_of_eq (computation_count X)))

end StrictEffectful.Assignment
end Silmaril.RuntimeWires
