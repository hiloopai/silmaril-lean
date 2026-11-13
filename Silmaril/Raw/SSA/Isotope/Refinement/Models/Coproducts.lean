module

public import Silmaril.Semantics.Categories.Thms

/-! # Explicitly chosen coproducts

The written calculus specifies pure injections into its type constructors.
Those chosen cocones must be retained as data: Mathlib's proposition-valued
`HasColimit` uses an opaque choice, whose injections need not be pure.
-/

@[expose] public section
noncomputable section

universe u v

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable (C : Type u) [Category.{v} C]

/-- Chosen binary coproduct and initial objects, with their genuine universal properties. -/
structure ChosenCoproducts where
  sum : C → C → C
  zero : C
  inl (A B : C) : A ⟶ sum A B
  inr (A B : C) : B ⟶ sum A B
  isColimit (A B : C) : IsColimit (BinaryCofan.mk (inl A B) (inr A B))
  isInitial : IsInitial zero

namespace ChosenCoproducts

variable {C} (S : ChosenCoproducts C)

def desc {A B D : C} (f : A ⟶ D) (g : B ⟶ D) : S.sum A B ⟶ D :=
  (S.isColimit A B).desc (BinaryCofan.mk f g)

def abort (A : C) : S.zero ⟶ A := S.isInitial.to A

@[simp] theorem inl_desc {A B D : C} (f : A ⟶ D) (g : B ⟶ D) :
    S.inl A B ≫ S.desc f g = f := (S.isColimit A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩

@[simp] theorem inr_desc {A B D : C} (f : A ⟶ D) (g : B ⟶ D) :
    S.inr A B ≫ S.desc f g = g := (S.isColimit A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩

/-- The chosen coproducts supply ordinary categorical coproduct existence. -/
theorem hasBinaryCoproducts (S : ChosenCoproducts C) : HasBinaryCoproducts C := by
  let (A B : C) : HasColimit (pair A B) := ⟨⟨⟨_, S.isColimit A B⟩⟩⟩
  exact hasBinaryCoproducts_of_hasColimit_pair C

theorem hasInitial (S : ChosenCoproducts C) : HasInitial C := S.isInitial.hasInitial

/-- The canonical distributor uses the designated, rather than an arbitrary, injections. -/
def distributor [PremonoidalCategory C] (A B D : C) :
    S.sum (A ⊗ B) (A ⊗ D) ⟶ A ⊗ S.sum B D := S.desc (A ◁ S.inl B D) (A ◁ S.inr B D)

/-- Coproduct action on two arrows, derived from its universal property. -/
def map {A B D E : C} (f : A ⟶ B) (g : D ⟶ E) : S.sum A D ⟶ S.sum B E :=
  S.desc (f ≫ S.inl B E) (g ≫ S.inr B E)

end ChosenCoproducts

end Silmaril.Isotope.Refinement.Models
