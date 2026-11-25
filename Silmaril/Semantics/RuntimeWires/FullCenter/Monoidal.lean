module

public import Silmaril.Semantics.RuntimeWires.FullCenter.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.FullCenter.Monoidal

@[expose] public section

namespace Silmaril.RuntimeWires.FullCenter

open CategoryTheory PremonoidalCategory
open scoped MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C] [IsStrictTensor C]

/-- The full center of a strict premonoidal category is monoidal. -/
instance centerMonoidal : MonoidalCategory (Center C) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by exact Proofs.FullCenter.monoidal_id)
    (id_tensorHom := by exact Proofs.FullCenter.monoidal_left)
    (tensorHom_id := by exact Proofs.FullCenter.monoidal_right)
    (tensorHom_comp_tensorHom := by exact Proofs.FullCenter.monoidal_comp)
    (associator_naturality := by exact Proofs.FullCenter.monoidal_assoc)
    (leftUnitor_naturality := by exact Proofs.FullCenter.monoidal_unitor_left)
    (rightUnitor_naturality := by exact Proofs.FullCenter.monoidal_unitor_right)
    (pentagon := by
      intro W X Y Z
      rw [Proofs.FullCenter.monoidal_left, Proofs.FullCenter.monoidal_right]
      exact Proofs.FullCenter.monoidal_pentagon W X Y Z)
    (triangle := by
      intro X Y
      rw [Proofs.FullCenter.monoidal_left, Proofs.FullCenter.monoidal_right]
      exact Proofs.FullCenter.monoidal_triangle X Y)

instance centerStrict : IsStrictTensor (Center C) where
  assocObj X Y Z := congrArg WideSubcategory.mk (IsStrictTensor.assocObj X.obj Y.obj Z.obj)
  leftObj X := congrArg WideSubcategory.mk (IsStrictTensor.leftObj X.obj)
  rightObj X := congrArg WideSubcategory.mk (IsStrictTensor.rightObj X.obj)
  associator_hom X Y Z := WideSubcategory.hom_ext (central C)
    ((IsStrictTensor.associator_hom X.obj Y.obj Z.obj).trans (eqToHom_map (centerInclusion C) _).symm)
  leftUnitor_hom X := WideSubcategory.hom_ext (central C)
    ((IsStrictTensor.leftUnitor_hom X.obj).trans (eqToHom_map (centerInclusion C) _).symm)
  rightUnitor_hom X := WideSubcategory.hom_ext (central C)
    ((IsStrictTensor.rightUnitor_hom X.obj).trans (eqToHom_map (centerInclusion C) _).symm)

/-- The strict effectful category obtained from the full center inclusion. -/
def model (C : Type u) [Category.{v} C] [PremonoidalCategory C] [IsStrictTensor C] :
    StrictEffectful (Center C) C where
  pure := centerInclusion C
  strict :=
    { unit := rfl
      tensor _ _ := rfl
      left _ {_ _} _ := (Category.comp_id _).trans (Category.id_comp _).symm
      right {_ _} _ _ := (Category.comp_id _).trans (Category.id_comp _).symm }
  objects := by exact Proofs.FullCenter.model_objects C
  central f := f.property

end Silmaril.RuntimeWires.FullCenter
