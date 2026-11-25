module

public import Silmaril.Semantics.RuntimeWires.EffectfulUniversal.Thms
public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Algebra.Group.End

@[expose] public section

/-!
# State-only interpretation of a runtime wire

An application of Lemma 3.13 and Theorem 3.14 (pp. 9:10–9:13) of
Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5. Value boundaries are interpreted in the terminal value
category, so the interpretation observes only the effect on the runtime state.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.StateWire

open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory

universe u v s

/-- An isomorphism with identity endomorphism in a single-object category. -/
def unitIso {M : Type s} [Monoid M] (X Y : SingleObj M) : X ≅ Y where
  hom := 1
  inv := 1
  hom_inv_id := by change (1 : M) * 1 = 1; exact one_mul _
  inv_hom_id := by change (1 : M) * 1 = 1; exact one_mul _

/-- Sequential actions form a premonoidal category. Tensoring by the sole
object leaves an action unchanged. -/
instance actionCategory (M : Type s) [Monoid M] : PremonoidalCategory (SingleObj M) where
  tensorUnit := SingleObj.star M
  tensorObj _ _ := SingleObj.star M
  whiskerLeft _ {_ _} f := f
  whiskerRight f _ := f
  tensorHom f g := g * f
  associator _ _ _ := unitIso _ _
  leftUnitor _ := unitIso _ _
  rightUnitor _ := unitIso _ _
  tensorHom_def _ _ := rfl
  whiskerLeft_id _ _ := rfl
  whiskerLeft_comp _ {_ _ _} _ _ := rfl
  id_whiskerRight _ _ := rfl
  comp_whiskerRight {_ _ _} _ _ _ := rfl
  associator_central _ _ _ := ⟨fun g => (mul_one g).trans (one_mul g).symm,
    fun g => (one_mul g).trans (mul_one g).symm⟩
  leftUnitor_central _ := ⟨fun g => (mul_one g).trans (one_mul g).symm,
    fun g => (one_mul g).trans (mul_one g).symm⟩
  rightUnitor_central _ := ⟨fun g => (mul_one g).trans (one_mul g).symm,
    fun g => (one_mul g).trans (mul_one g).symm⟩
  associator_naturality_left f _ _ := (one_mul f).trans (mul_one f).symm
  associator_naturality_middle _ {_ _} f _ := (one_mul f).trans (mul_one f).symm
  associator_naturality_right _ _ {_ _} f := (one_mul f).trans (mul_one f).symm
  leftUnitor_naturality f := (one_mul f).trans (mul_one f).symm
  rightUnitor_naturality f := (one_mul f).trans (mul_one f).symm
  pentagon _ _ _ _ := by change ((1 : M) * 1) * 1 = 1 * 1; simp
  triangle _ _ := by change (1 : M) * 1 = 1; exact one_mul _

instance strictAction (M : Type s) [Monoid M] : IsStrictTensor (SingleObj M) where
  assocObj _ _ _ := rfl
  leftObj _ := Subsingleton.elim _ _
  rightObj _ := Subsingleton.elim _ _
  associator_hom _ _ _ := rfl
  leftUnitor_hom X := by have h : X = SingleObj.star M := Subsingleton.elim _ _; subst X; rfl
  rightUnitor_hom X := by have h : X = SingleObj.star M := Subsingleton.elim _ _; subst X; rfl

instance strictValue : IsStrictTensor (Discrete PUnit.{1}) where
  assocObj _ _ _ := Subsingleton.elim _ _
  leftObj _ := Subsingleton.elim _ _
  rightObj _ := Subsingleton.elim _ _
  associator_hom _ _ _ := Subsingleton.elim _ _
  leftUnitor_hom _ := Subsingleton.elim _ _
  rightUnitor_hom _ := Subsingleton.elim _ _

/-- Interpret the terminal pure category as identity actions. -/
def model (M : Type s) [Monoid M] : StrictEffectful (Discrete PUnit.{1}) (SingleObj M) where
  pure :=
    { obj := fun _ => SingleObj.star M
      map _ := 1
      map_id _ := rfl
      map_comp _ _ := (one_mul _).symm }
  strict :=
    { unit := rfl
      tensor _ _ := rfl
      left _ {_ _} _ := rfl
      right {_ _} _ _ := rfl }
  objects := ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨⟨PUnit.unit⟩, Subsingleton.elim _ _⟩⟩
  central _ := ⟨fun g => (mul_one g).trans (one_mul g).symm,
    fun g => (one_mul g).trans (mul_one g).symm⟩

open Presentation

variable {G : EffectfulPolygraph.{u,v}} {S : Type s}

/-- Assign one state transition to each effectful generator. -/
def assignment (update : G.effect.Edge → S → S) :
    (model (Function.End S)).Assignment G where
  obj _ := ⟨PUnit.unit⟩
  pure _ := eqToHom (Subsingleton.elim _ _)
  effect e := update e

/-- The strict computation functor supplied by the universal property. -/
def interpretation (update : G.effect.Edge → S → S) : Computations G ⥤ SingleObj (Function.End S) :=
  (assignment update).extension.computation

/-- The state transition of a one-runtime computation. -/
def run (update : G.effect.Edge → S → S) {A B : Computations G} (f : A ⟶ B) : S → S :=
  (interpretation update).map f

end Silmaril.RuntimeWires.StateWire
