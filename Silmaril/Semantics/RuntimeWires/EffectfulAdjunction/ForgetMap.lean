module

public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.Category

@[expose] public section

namespace Silmaril.RuntimeWires.StrictEffectful.Bundled

open CategoryTheory Diagram
open scoped MonoidalCategory

universe u v

theorem wordImage {X Y : Bundled.{u,v}} (H : X ⟶ Y) (A : List X.Value) :
    H.value.obj (wordObject id A) = wordObject id (A.map H.value.obj) := by
  induction A with
  | nil => exact H.valueStrict.unit
  | cons x A ih =>
    exact (H.valueStrict.tensor x (wordObject id A)).trans (congrArg (H.value.obj x ⊗ ·) ih)

theorem effectWordImage {X Y : Bundled.{u,v}} (H : X ⟶ Y) (A : List X.Value) :
    H.computation.obj (X.model.pure.obj (wordObject id A)) =
      Y.model.pure.obj (wordObject id (A.map H.value.obj)) :=
  (Functor.congr_obj H.square (wordObject id A)).trans (congrArg Y.model.pure.obj (wordImage H A))

def pureArrow {X Y : Bundled.{u,v}} (H : X ⟶ Y) (e : X.polygraph.pure.Edge) :
    (wordObject id (e.1.map H.value.obj) ⟶ wordObject id (e.2.1.map H.value.obj)) :=
  Interpretation.transport (wordImage H e.1) (wordImage H e.2.1) (H.value.map e.2.2)

def effectArrow {X Y : Bundled.{u,v}} (H : X ⟶ Y) (e : X.polygraph.effect.Edge) :
    (Y.model.pure.obj (wordObject id (e.1.map H.value.obj)) ⟶
      Y.model.pure.obj (wordObject id (e.2.1.map H.value.obj))) :=
  Interpretation.transport (effectWordImage H e.1) (effectWordImage H e.2.1)
    (H.computation.map e.2.2)

def forgetMap {X Y : Bundled.{u,v}} (H : X ⟶ Y) : X.polygraph ⟶ Y.polygraph where
  obj := H.value.obj
  pure := ⟨fun e => ⟨e.1.map H.value.obj, e.2.1.map H.value.obj, pureArrow H e⟩,
    fun _ => rfl, fun _ => rfl⟩
  effect := ⟨fun e => ⟨e.1.map H.value.obj, e.2.1.map H.value.obj, effectArrow H e⟩,
    fun _ => rfl, fun _ => rfl⟩

end Silmaril.RuntimeWires.StrictEffectful.Bundled
