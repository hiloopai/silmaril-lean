module

public import Silmaril.Semantics.RuntimeWires.StrictEffectful.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.FullCenter.Whiskering

@[expose] public section

/-!
# The tensor on the full center

Definition 5.1 (p. 9:15) of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.FullCenter

open CategoryTheory PremonoidalCategory
open scoped MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [PremonoidalCategory C]

/-- A central isomorphism defines an isomorphism in the center. -/
def liftIso {X Y : Center C} (i : X.obj ≅ Y.obj) (h : IsCentral i.hom) : X ≅ Y where
  hom := ⟨i.hom, h⟩
  inv := ⟨i.inv, h.inv i⟩
  hom_inv_id := WideSubcategory.hom_ext (central C) i.hom_inv_id
  inv_hom_id := WideSubcategory.hom_ext (central C) i.inv_hom_id

variable [IsStrictTensor C]

/-- Tensor inherited from the ambient premonoidal category on central arrows. -/
instance centerTensor : MonoidalCategoryStruct (Center C) where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft X {_ _} f := ⟨X.obj ◁ f.hom, by
    exact Proofs.FullCenter.central_left X.obj f.property⟩
  whiskerRight f X := ⟨f.hom ▷ X.obj, by
    exact Proofs.FullCenter.central_right X.obj f.property⟩
  tensorHom f g := ⟨f.hom ⊗ₘ g.hom, by
    exact Proofs.FullCenter.central_tensor f.property g.property⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z := liftIso (α_ X.obj Y.obj Z.obj) (associator_central _ _ _)
  leftUnitor X := liftIso (λ_ X.obj) (leftUnitor_central _)
  rightUnitor X := liftIso (ρ_ X.obj) (rightUnitor_central _)

end Silmaril.RuntimeWires.FullCenter
