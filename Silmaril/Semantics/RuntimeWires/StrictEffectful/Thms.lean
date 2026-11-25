module

public import Silmaril.Semantics.RuntimeWires.StrictEffectful.Defs

@[expose] public section

namespace Silmaril.RuntimeWires

open CategoryTheory
open scoped MonoidalCategory

universe u v

namespace Diagram.Presented

instance {O : Type u} {S : Signature.{u,v} O} {E : Equations S} :
    IsStrictTensor (Presented S E) where
  assocObj := concat_assoc
  leftObj := empty_concat
  rightObj := concat_empty
  associator_hom _ _ _ := rfl
  leftUnitor_hom _ := rfl
  rightUnitor_hom _ := rfl

end Diagram.Presented

namespace Presentation.Computations

instance {G : EffectfulPolygraph.{u,v}} : IsStrictTensor (Computations G) where
  assocObj := concat_assoc
  leftObj := empty_concat
  rightObj := concat_empty
  associator_hom _ _ _ := rfl
  leftUnitor_hom _ := rfl
  rightUnitor_hom _ := rfl

end Presentation.Computations

namespace Presentation

/-- The strict effectful category supplied by Lemmas 3.11 and 3.12. -/
def strictRuntime (G : EffectfulPolygraph.{u,v}) : StrictEffectful (Pure G) (Computations G) where
  pure := pureInclusion G
  strict :=
    { unit := rfl
      tensor _ _ := rfl
      left X {_ _} f := (Category.comp_id _).trans
        ((pureInclusion_whiskerLeft X f).symm.trans (Category.id_comp _).symm)
      right f Z := (Category.comp_id _).trans
        ((pureInclusion_whiskerRight f Z).symm.trans (Category.id_comp _).symm) }
  objects :=
    ⟨fun _ _ h => congrArg (fun X : Computations G => (⟨X.word⟩ : Pure G)) h,
      fun X => ⟨⟨X.word⟩, rfl⟩⟩
  central f := pureInclusion_central f

end Presentation
end Silmaril.RuntimeWires
