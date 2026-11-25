module

public import Silmaril.Semantics.RuntimeWires.FullCenter.Monoidal
public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.Category
import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulAdjunction.Category

@[expose] public section

namespace Silmaril.RuntimeWires.FullCenter

open CategoryTheory PremonoidalCategory

universe u v

/-- The objects of the strict premonoidal category in Definition 5.1. -/
structure Bundled where
  Object : Type u
  [category : Category.{max u v} Object]
  [premonoidal : PremonoidalCategory Object]
  [strict : IsStrictTensor Object]

attribute [instance] Bundled.category Bundled.premonoidal Bundled.strict

namespace Bundled

/-- A strict premonoidal functor preserving all central arrows. -/
structure Hom (X Y : Bundled.{u,v}) where
  functor : X.Object ⥤ Y.Object
  strict : IsStrictTensorFunctor functor
  central {A B : X.Object} (f : A ⟶ B) : IsCentral f → IsCentral (functor.map f)

instance : Category Bundled.{u,v} where
  Hom := Hom
  id X :=
    { functor := 𝟭 X.Object
      strict := by exact Proofs.EffectfulAdjunction.id_strict
      central _ h := h }
  comp H K :=
    { functor := H.functor ⋙ K.functor
      strict := by exact Proofs.EffectfulAdjunction.comp_strict H.strict K.strict
      central f h := K.central _ (H.central f h) }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Bundle the center inclusion as a strict effectful category. -/
def toEffectful (X : Bundled.{u,v}) : StrictEffectful.Bundled.{u,v} where
  Value := Center X.Object
  Computation := X.Object
  model := FullCenter.model X.Object

/-- A central functor restricts to the centers. -/
def onCenters {X Y : Bundled.{u,v}} (H : X ⟶ Y) : Center X.Object ⥤ Center Y.Object where
  obj Z := ⟨H.functor.obj Z.obj⟩
  map f := ⟨H.functor.map f.hom, H.central f.hom f.property⟩
  map_id _ := WideSubcategory.hom_ext (central Y.Object) (H.functor.map_id _)
  map_comp _ _ := WideSubcategory.hom_ext (central Y.Object) (H.functor.map_comp _ _)

end Bundled
end Silmaril.RuntimeWires.FullCenter
