module

public import Silmaril.Semantics.RuntimeWires.PureInclusion.Thms

@[expose] public section

/-!
# Strict effectful targets

Definitions 2.5 and 2.7 and the targets of Lemma 3.13 (pp. 9:4, 9:10–9:13)
in Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires

open CategoryTheory
open scoped MonoidalCategory

universe u v u' v' u₁ v₁ u₂ v₂

/-- Strict tensor on a category. The structural arrows are identities along
the indicated equalities of objects. This uses Mathlib's categorical transport. -/
class IsStrictTensor (C : Type u) [Category.{v} C] [MonoidalCategoryStruct C] : Prop where
  assocObj (X Y Z : C) : (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)
  leftObj (X : C) : (𝟙_ C) ⊗ X = X
  rightObj (X : C) : X ⊗ (𝟙_ C) = X
  associator_hom (X Y Z : C) : (α_ X Y Z).hom = eqToHom (assocObj X Y Z)
  leftUnitor_hom (X : C) : (λ_ X).hom = eqToHom (leftObj X)
  rightUnitor_hom (X : C) : (ρ_ X).hom = eqToHom (rightObj X)

/-- A strict tensor-preserving functor. Between strict categories the two
whiskering squares and object equalities also determine preservation of
the structural isomorphisms. -/
structure IsStrictTensorFunctor {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D] [MonoidalCategoryStruct C] [MonoidalCategoryStruct D]
    (F : C ⥤ D) : Prop where
  unit : F.obj (𝟙_ C) = 𝟙_ D
  tensor (X Y : C) : F.obj (X ⊗ Y) = F.obj X ⊗ F.obj Y
  left (X : C) {Y Z : C} (f : Y ⟶ Z) :
    F.map (X ◁ f) ≫ eqToHom (tensor X Z) = eqToHom (tensor X Y) ≫ F.obj X ◁ F.map f
  right {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map (f ▷ Z) ≫ eqToHom (tensor Y Z) = eqToHom (tensor X Z) ≫ F.map f ▷ F.obj Z

/-- A strict effectful category with a chosen monoidal category of values.
A bijection on objects implements the paper's shared object set when the
two Lean categories use different types for their objects. -/
structure StrictEffectful (V : Type u) (C : Type u')
    [Category.{v} V] [Category.{v'} C] [MonoidalCategory V] [PremonoidalCategory C]
    [IsStrictTensor V] [IsStrictTensor C] where
  pure : V ⥤ C
  strict : IsStrictTensorFunctor pure
  objects : Function.Bijective pure.obj
  central {A B : V} (f : A ⟶ B) : PremonoidalCategory.IsCentral (pure.map f)

namespace StrictEffectful

/-- Interpret the object and both generator families of an effectful polygraph
in a target. The word order agrees with the paper's tensor order. -/
def wordObject {V : Type u} [Category.{v} V] [MonoidalCategoryStruct V]
    {O : Type u₁} (f : O → V) : List O → V
  | [] => 𝟙_ V
  | x :: xs => f x ⊗ wordObject f xs

variable {V : Type u} {C : Type u'} {W : Type u₁} {D : Type u₂}
variable [Category.{v} V] [Category.{v'} C] [Category.{v₁} W] [Category.{v₂} D]
variable [MonoidalCategory V] [PremonoidalCategory C] [MonoidalCategory W] [PremonoidalCategory D]
variable [IsStrictTensor V] [IsStrictTensor C] [IsStrictTensor W] [IsStrictTensor D]

/-- A strict effectful functor as in Definition 2.7. The pure square commutes,
and both functors strictly preserve the tensor structure. -/
structure Hom (S : StrictEffectful V C) (T : StrictEffectful W D) where
  value : V ⥤ W
  computation : C ⥤ D
  valueStrict : IsStrictTensorFunctor value
  computationStrict : IsStrictTensorFunctor computation
  square : S.pure ⋙ computation = value ⋙ T.pure

/-- The generator assignment used in Lemma 3.13. The chosen pure target
interprets pure generators. Computation generators may use any target arrow. -/
structure Assignment (S : StrictEffectful V C) (G : EffectfulPolygraph.{u₁,v₁}) where
  obj : G.Obj → V
  pure (e : G.pure.Edge) : wordObject obj (G.pure.source e) ⟶ wordObject obj (G.pure.target e)
  effect (e : G.effect.Edge) :
    S.pure.obj (wordObject obj (G.effect.source e)) ⟶ S.pure.obj (wordObject obj (G.effect.target e))

end StrictEffectful
end Silmaril.RuntimeWires
