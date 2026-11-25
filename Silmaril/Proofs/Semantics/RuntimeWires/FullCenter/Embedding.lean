module

public import Silmaril.Semantics.RuntimeWires.FullCenter.Category
public import Silmaril.Semantics.RuntimeWires.ChosenCenter.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.FullCenter

open CategoryTheory PremonoidalCategory
open Silmaril.RuntimeWires.FullCenter.Bundled
open scoped MonoidalCategory

universe u v

variable {X Y : Silmaril.RuntimeWires.FullCenter.Bundled.{u,v}}

theorem onCenters_strict (H : X ⟶ Y) : IsStrictTensorFunctor (onCenters H) where
  unit := congrArg WideSubcategory.mk H.strict.unit
  tensor A B := congrArg WideSubcategory.mk (H.strict.tensor A.obj B.obj)
  left A {_ _} f := by
    apply (centerInclusion Y.Object).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    exact (congrArg (fun k => _ ≫ k) (eqToHom_map (centerInclusion Y.Object) _)).trans
      ((H.strict.left A.obj f.hom).trans
        (congrArg (fun k => k ≫ _) (eqToHom_map (centerInclusion Y.Object) _).symm))
  right {_ _} f B := by
    apply (centerInclusion Y.Object).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    exact (congrArg (fun k => _ ≫ k) (eqToHom_map (centerInclusion Y.Object) _)).trans
      ((H.strict.right f.hom B.obj).trans
        (congrArg (fun k => k ≫ _) (eqToHom_map (centerInclusion Y.Object) _).symm))

private theorem center_cancel {D : Type u} [Category.{max u v} D] [PremonoidalCategory D]
    {F G : Center X.Object ⥤ Center D} (h : F ⋙ centerInclusion D = G ⋙ centerInclusion D) :
    F = G := by
  have obj (A : Center X.Object) : F.obj A = G.obj A :=
    congrArg WideSubcategory.mk (Functor.congr_obj h A)
  refine CategoryTheory.Functor.ext obj ?_
  intro A B f
  apply (centerInclusion D).map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom h f

@[expose] def liftComputation (H : X.toEffectful ⟶ Y.toEffectful) : X ⟶ Y where
  functor := H.computation
  strict := H.computationStrict
  central f hf :=
    StrictEffectful.Hom.preservesCentral_of_exhaustsCenter X.toEffectful.model H
      (fun {_ _} g hg => ⟨⟨g, hg⟩, rfl⟩) f hf

theorem lift_value_eq (H : X.toEffectful ⟶ Y.toEffectful) :
    onCenters (liftComputation H) = H.value :=
  center_cancel (F := onCenters (liftComputation H)) (G := H.value) H.square

theorem effectful_hom_eq {X Y : StrictEffectful.Bundled.{u,v}} {H K : X ⟶ Y}
    (h : H.value = K.value) (k : H.computation = K.computation) : H = K := by
  cases H
  cases K
  cases h
  cases k
  rfl

theorem premonoidal_hom_eq {H K : X ⟶ Y} (e : H.functor = K.functor) : H = K := by
  cases H
  cases K
  cases e
  rfl

end Silmaril.RuntimeWires.Proofs.FullCenter
