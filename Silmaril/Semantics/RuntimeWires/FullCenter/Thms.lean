module

public import Silmaril.Semantics.RuntimeWires.FullCenter.Category
import Silmaril.Proofs.Semantics.RuntimeWires.FullCenter.Embedding

@[expose] public section

namespace Silmaril.RuntimeWires.FullCenter.Bundled

open CategoryTheory

universe u v

/-- The functor `J` in Definition 5.1 sends a strict premonoidal category to its full
center inclusion and a center-preserving functor to its induced commutative square. -/
def embedding : Bundled.{u,v} ⥤ StrictEffectful.Bundled.{u,v} where
  obj := toEffectful
  map H :=
    { value := onCenters H
      computation := H.functor
      valueStrict := by exact Proofs.FullCenter.onCenters_strict H
      computationStrict := H.strict
      square := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

instance embedding_faithful : (embedding.{u,v}).Faithful where
  map_injective h := by
    exact Proofs.FullCenter.premonoidal_hom_eq (congrArg (fun F => F.computation) h)

instance embedding_full : (embedding.{u,v}).Full where
  map_surjective := by
    intro X Y H
    exact ⟨Proofs.FullCenter.liftComputation H,
      Proofs.FullCenter.effectful_hom_eq (Proofs.FullCenter.lift_value_eq H) rfl⟩

end Silmaril.RuntimeWires.FullCenter.Bundled
