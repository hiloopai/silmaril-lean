module

public import Silmaril.Semantics.RuntimeWires.StrictEffectful.Thms

@[expose] public section

/-!
# Comparing chosen purity with the full center

Conditional comparison for Lemma 5.3 and an all-effectful adjunction
with chosen pure structure in the setting of Theorem 5.5 (p. 9:16) of
Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.StrictEffectful

open CategoryTheory PremonoidalCategory

universe u v u' v'

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]

/-- Lift the chosen pure functor to the wide subcategory of central arrows. -/
def toCenter (S : StrictEffectful V C) : V ⥤ Center C where
  obj X := ⟨S.pure.obj X⟩
  map f := ⟨S.pure.map f, S.central f⟩
  map_id X := WideSubcategory.hom_ext (PremonoidalCategory.central C) (S.pure.map_id X)
  map_comp f g := WideSubcategory.hom_ext (PremonoidalCategory.central C) (S.pure.map_comp f g)

/-- The chosen pure structure exhausts the central arrows at every pair of
objects. Since the pure object map is bijective this tests the entire center. -/
def ExhaustsCenter (S : StrictEffectful V C) : Prop :=
  ∀ ⦃X Y : V⦄ (f : S.pure.obj X ⟶ S.pure.obj Y), IsCentral f →
    ∃ p : X ⟶ Y, S.pure.map p = f

end Silmaril.RuntimeWires.StrictEffectful
