module

public import Silmaril.Semantics.RuntimeWires.MonoidalAdjunction.Defs

@[expose] public section

namespace Silmaril.RuntimeWires.StrictMonoidal

open CategoryTheory Diagram StrictEffectful
open scoped MonoidalCategory

universe u v

variable {G : Polygraph.{u,max u v}} {X : StrictMonoidal.{u,v}}

def sort (x : G.Obj) : (terms G).Object := ⟨[x]⟩

theorem termsWord (A : List G.Obj) :
    wordObject id (A.map (sort (G := G))) = (⟨A⟩ : (terms G).Object) := by
  induction A with
  | nil => rfl
  | cons x A ih => exact congrArg (sort x ⊗ ·) ih

def generator (e : G.edges.Edge) :
    (⟨G.edges.source e⟩ : (terms G).Object) ⟶ ⟨G.edges.target e⟩ :=
  Presented.ofTerm (Diagram.gen (S := G.edges) e)

/-- The map from the generating polygraph into the underlying polygraph of its presentation. -/
def generatorUnit (G : Polygraph.{u,max u v}) : G ⟶ forget.obj (terms G) where
  obj := sort
  edges :=
    { edge e := ⟨(G.edges.source e).map sort, (G.edges.target e).map sort,
        Interpretation.transport (termsWord _).symm (termsWord _).symm (generator e)⟩
      source _ := rfl
      target _ := rfl }

theorem wordObject_map (f : G.Obj → X.Object) (A : List G.Obj) :
    wordObject id (A.map f) = wordObject f A :=
  StrictEffectful.Bundled.wordImage_map (G := G.allEffectful) (X := X.model) f A

theorem input (f : G ⟶ forget.obj X) (e : G.edges.Edge) :
    wordObject (id : X.Object → X.Object) (f.edges.edge e).1 =
      wordObject (show G.Obj → X.Object from f.obj) (G.edges.source e) :=
  (congrArg (wordObject (id : X.Object → X.Object)) (f.edges.source e)).trans
    (wordObject_map f.obj (G.edges.source e))

theorem output (f : G ⟶ forget.obj X) (e : G.edges.Edge) :
    wordObject (id : X.Object → X.Object) (f.edges.edge e).2.1 =
      wordObject (show G.Obj → X.Object from f.obj) (G.edges.target e) :=
  (congrArg (wordObject (id : X.Object → X.Object)) (f.edges.target e)).trans
    (wordObject_map f.obj (G.edges.target e))

/-- Interpret a map into the underlying polygraph as a monoidal word interpretation. -/
def interpretation (f : G ⟶ forget.obj X) : Interpretation G.edges X.Object :=
  Interpretation.ofGenerators (show G.Obj → X.Object from f.obj)
    (fun e => Interpretation.transport (input f e) (output f e) (f.edges.edge e).2.2)

/-- Restriction to the polygraph generators. -/
def restrict (F : terms G ⟶ X) : G ⟶ forget.obj X :=
  generatorUnit G ≫ forget.map F

end Silmaril.RuntimeWires.StrictMonoidal
