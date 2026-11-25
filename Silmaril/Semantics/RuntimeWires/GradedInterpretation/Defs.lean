module

public import Silmaril.Semantics.RuntimeWires.DiagramInterpretation.Thms
public import Silmaril.Semantics.RuntimeWires.ZeroRuntime.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.DiagramInterpretation.Basic

@[expose] public section

/-!
# Graded interpretation of runtime diagrams

The interpretation of Figure 12 in Lemma 3.13 (pp. 9:10–9:13) of
Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.StrictEffectful.Assignment

open CategoryTheory Diagram Presentation
open scoped MonoidalCategory

universe u v u' v' u₁ v₁

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

variable (F : T.Assignment G)

/-- Interpret the pure words in the target's chosen value category. -/
def valuesInterpretation : Interpretation G.pure V :=
  Interpretation.ofGenerators F.obj F.pure

/-- Interpret a runtime boundary by erasing the runtime and using the common target objects. -/
def boundary (A : List (Wire G.Obj)) : C :=
  T.pure.obj (wordObject F.obj (eraseBoundary A))

/-- Words without a value wire have the computation unit as their interpretation. -/
theorem boundary_runtime : F.boundary [none] = 𝟙_ C :=
  T.strict.unit

theorem boundary_append (A B : List (Wire G.Obj)) :
    F.boundary (A ++ B) = F.boundary A ⊗ F.boundary B := by
  have h : wordObject F.obj (eraseBoundary (A ++ B)) =
      wordObject F.obj (eraseBoundary A) ⊗ wordObject F.obj (eraseBoundary B) :=
    (congrArg (wordObject F.obj) (eraseBoundary_append A B)).trans
      (by exact Proofs.DiagramInterpretation.wordObject_append F.obj _ _)
  exact (congrArg T.pure.obj h).trans (T.strict.tensor _ _)

/-- Interpret the raw runtime presentation, including crossings as identities.
The quotient proof restricts this evaluation to at most one runtime wire. -/
def computationInterpretation : Interpretation (signature G) C where
  obj := F.boundary
  empty := T.strict.unit
  append := F.boundary_append
  edge
    | .pure e => Interpretation.transport
        (congrArg (T.pure.obj ∘ wordObject F.obj) (eraseBoundary_values _)).symm
        (congrArg (T.pure.obj ∘ wordObject F.obj) (eraseBoundary_values _)).symm
        (T.pure.map (F.pure e))
    | .effect e => Interpretation.transport
        (congrArg (T.pure.obj ∘ wordObject F.obj) (eraseBoundary_values _)).symm
        (congrArg (T.pure.obj ∘ wordObject F.obj) (eraseBoundary_values _)).symm (F.effect e)
    | .moveRight x => 𝟙 (T.pure.obj (wordObject F.obj [x]))
    | .moveLeft x => 𝟙 (T.pure.obj (wordObject F.obj [x]))

end Silmaril.RuntimeWires.StrictEffectful.Assignment
