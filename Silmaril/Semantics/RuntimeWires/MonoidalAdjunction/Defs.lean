module

public import Silmaril.Semantics.RuntimeWires.EffectfulAdjunction.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulAdjunction.Category

@[expose] public section

/-!
# The strict monoidal adjunction on polygraphs

Lemma 3.4, Lemma 3.5, and Theorem 3.6 (pp. 9:7–9:8) of Mario Román and
Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5. The free side uses the algebraic presentation.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires

open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory

universe u v

/-- A strict monoidal category bundled at the hom universe used by presentations. -/
structure StrictMonoidal where
  Object : Type u
  [category : Category.{max u v} Object]
  [monoidal : MonoidalCategory Object]
  [strict : IsStrictTensor Object]

attribute [instance] StrictMonoidal.category StrictMonoidal.monoidal StrictMonoidal.strict

namespace StrictMonoidal

instance : Category StrictMonoidal.{u,v} where
  Hom X Y := {F : X.Object ⥤ Y.Object // IsStrictTensorFunctor F}
  id X := ⟨𝟭 X.Object, by exact Proofs.EffectfulAdjunction.id_strict⟩
  comp F G := ⟨F.1 ⋙ G.1, by exact Proofs.EffectfulAdjunction.comp_strict F.2 G.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The two orders of monoidal tensoring agree. -/
theorem exchange {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) : f ⋉ g = f ⋊ g :=
  (MonoidalCategory.tensorHom_def f g).symm.trans (MonoidalCategory.tensorHom_def' f g)

/-- The premonoidal structure associated to a monoidal category. -/
@[instance_reducible] def asPremonoidal (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    PremonoidalCategory C where
  toMonoidalCategoryStruct := inferInstance
  tensorHom_def := MonoidalCategory.tensorHom_def
  whiskerLeft_id := MonoidalCategory.whiskerLeft_id
  whiskerLeft_comp := MonoidalCategory.whiskerLeft_comp
  id_whiskerRight := MonoidalCategory.id_whiskerRight
  comp_whiskerRight := MonoidalCategory.comp_whiskerRight
  associator_central _ _ _ := ⟨fun g => exchange _ g, fun g => exchange g _⟩
  leftUnitor_central _ := ⟨fun g => exchange _ g, fun g => exchange g _⟩
  rightUnitor_central _ := ⟨fun g => exchange _ g, fun g => exchange g _⟩
  associator_naturality_left := MonoidalCategory.associator_naturality_left
  associator_naturality_middle := MonoidalCategory.associator_naturality_middle
  associator_naturality_right := MonoidalCategory.associator_naturality_right
  leftUnitor_naturality := MonoidalCategory.leftUnitor_naturality
  rightUnitor_naturality := MonoidalCategory.rightUnitor_naturality
  pentagon := MonoidalCategory.pentagon
  triangle := MonoidalCategory.triangle

/-- A strict monoidal category viewed as an effectful category in which every arrow is pure. -/
def model (X : StrictMonoidal.{u,v}) : StrictEffectful.Bundled.{u,v} :=
  letI : PremonoidalCategory X.Object := asPremonoidal X.Object
  { Value := X.Object
    Computation := X.Object
    computationStrict := X.strict
    model :=
      { pure := 𝟭 X.Object
        strict := by exact Proofs.EffectfulAdjunction.id_strict
        objects := Function.bijective_id
        central _ := ⟨fun g => exchange _ g, fun g => exchange g _⟩ } }

/-- Include strict monoidal categories as effectful categories with identity pure functor. -/
def asEffectful : StrictMonoidal.{u,v} ⥤ StrictEffectful.Bundled.{u,v} where
  obj := model
  map H :=
    { value := H.1
      computation := H.1
      valueStrict := H.2
      computationStrict := H.2
      square := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Lemma 3.5. The underlying polygraph has all typed arrows of the category as edges. -/
def forget : StrictMonoidal.{u,v} ⥤ Polygraph.{u,max u v} :=
  asEffectful ⋙ StrictEffectful.Bundled.forget ⋙ EffectfulPolygraph.forgetPure

open Diagram

/-- The strict monoidal quotient presentation of a polygraph. -/
def terms (G : Polygraph.{u,max u v}) : StrictMonoidal.{u,v} where
  Object := Presented G.edges (fun _ _ => False)

end StrictMonoidal
end Silmaril.RuntimeWires
