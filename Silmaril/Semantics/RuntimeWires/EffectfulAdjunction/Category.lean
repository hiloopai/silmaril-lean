module

public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulAdjunction.Category

@[expose] public section

namespace Silmaril.RuntimeWires.StrictEffectful.Bundled

open CategoryTheory

universe u v

instance : Category Bundled.{u,v} where
  Hom A B := A.model.Hom B.model
  id A :=
    { value := 𝟭 A.Value
      computation := 𝟭 A.Computation
      valueStrict := by exact Proofs.EffectfulAdjunction.id_strict
      computationStrict := by exact Proofs.EffectfulAdjunction.id_strict
      square := rfl }
  comp a b :=
    { value := a.value ⋙ b.value
      computation := a.computation ⋙ b.computation
      valueStrict := by exact Proofs.EffectfulAdjunction.comp_strict a.valueStrict b.valueStrict
      computationStrict := by
        exact Proofs.EffectfulAdjunction.comp_strict a.computationStrict b.computationStrict
      square := by exact Proofs.EffectfulAdjunction.comp_square a b }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end Silmaril.RuntimeWires.StrictEffectful.Bundled
