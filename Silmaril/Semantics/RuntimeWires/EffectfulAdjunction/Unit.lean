module

public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.Forget

@[expose] public section

namespace Silmaril.RuntimeWires.StrictEffectful.Bundled

open CategoryTheory Diagram Presentation
open scoped MonoidalCategory

universe u v

variable {G : EffectfulPolygraph.{u,max u v}} {X : Bundled.{u,v}}

/-- Regard a generator sort as a singleton word. -/
def sortObject (x : G.Obj) : (runtime G).Value := ⟨[x]⟩

theorem runtimeWord (A : List G.Obj) :
    wordObject id (A.map (sortObject (G := G))) = (⟨A⟩ : (runtime G).Value) := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    exact congrArg ((sortObject x) ⊗ ·) ih

/-- The pure generator of the free value presentation. -/
def pureGenerator (e : G.pure.Edge) :
    (⟨G.pure.source e⟩ : Pure G) ⟶ ⟨G.pure.target e⟩ :=
  Diagram.Presented.ofTerm (Diagram.gen (S := G.pure) e)

/-- The generator map into the underlying polygraph of the free model. -/
def generatorUnit (G : EffectfulPolygraph.{u,max u v}) : G ⟶ (runtime G).polygraph where
  obj := sortObject
  pure :=
    { edge e := ⟨(G.pure.source e).map sortObject, (G.pure.target e).map sortObject,
        Interpretation.transport (runtimeWord _).symm (runtimeWord _).symm (pureGenerator e)⟩
      source _ := rfl
      target _ := rfl }
  effect :=
    { edge e := ⟨(G.effect.source e).map sortObject, (G.effect.target e).map sortObject,
        Interpretation.transport
          (congrArg (runtime G).model.pure.obj (runtimeWord _)).symm
          (congrArg (runtime G).model.pure.obj (runtimeWord _)).symm (effectGenerator G e)⟩
      source _ := rfl
      target _ := rfl }

theorem wordImage_map (obj : G.Obj → X.Value) (A : List G.Obj) :
    wordObject id (A.map obj) = wordObject obj A := by
  induction A with
  | nil => rfl
  | cons x A ih => exact congrArg (obj x ⊗ ·) ih

/-- Read a map into the underlying polygraph as a generator assignment. -/
def assignment (f : G ⟶ X.polygraph) : X.model.Assignment G where
  obj := f.obj
  pure e := Interpretation.transport
    ((congrArg (wordObject (id : X.Value → X.Value)) (f.pure.source e)).trans (wordImage_map f.obj _))
    ((congrArg (wordObject (id : X.Value → X.Value)) (f.pure.target e)).trans (wordImage_map f.obj _))
    (f.pure.edge e).2.2
  effect e := Interpretation.transport
    ((congrArg (X.model.pure.obj ∘ wordObject id) (f.effect.source e)).trans
      (congrArg X.model.pure.obj (wordImage_map f.obj _)))
    ((congrArg (X.model.pure.obj ∘ wordObject id) (f.effect.target e)).trans
      (congrArg X.model.pure.obj (wordImage_map f.obj _)))
    (f.effect.edge e).2.2

/-- Restrict a strict effectful functor to its action on generators. -/
def restrict (H : runtime G ⟶ X) : G ⟶ X.polygraph :=
  generatorUnit G ≫ forget.map H

end Silmaril.RuntimeWires.StrictEffectful.Bundled
