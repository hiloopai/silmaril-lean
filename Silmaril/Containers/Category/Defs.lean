module

public import Silmaril.Containers.Runtime.Defs
public import Silmaril.Containers.Adapter.Defs
public import Mathlib.CategoryTheory.Functor.Basic

/-! # Experimental categories of loaders and runtime simulations

Arrows point from an implementation to an abstraction. A loader arrow preserves successful
loads; its target may accept more images. A runtime arrow additionally maps *all* observable
behaviours, including refusals and UB, and proves simulation. Certificate transfer also needs
`Adapter.ReflectsNoUB`; simulation alone may mask source UB. -/

@[expose] public section
namespace Silmaril.Containers
open CategoryTheory

/-- An independently auditable loader. -/
structure LoaderCat : Type 1 where
  Image : Type
  Program : Type
  load : Image → Except Refusal Program

namespace LoaderCat
/-- Success preservation allows a target loader to be more permissive. -/
@[ext] structure Hom (A B : LoaderCat) where
  image : A.Image → B.Image
  program : A.Program → B.Program
  loads : ∀ i p, A.load i = .ok p → B.load (image i) = .ok (program p)

def Hom.id (A : LoaderCat) : Hom A A := ⟨_root_.id, _root_.id, fun _ _ h => h⟩
def Hom.comp {A B C : LoaderCat} (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨g.image ∘ f.image, g.program ∘ f.program, fun i p h => g.loads _ _ (f.loads i p h)⟩

instance : Category LoaderCat where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intros; ext <;> rfl
  comp_id := by intros; ext <;> rfl
  assoc := by intros; ext <;> rfl

/-- Refusal classification is relative to an explicit wellformedness contract. Missing blobs
and resources are not automatically evidence of an invalid image. -/
structure Contract (A : LoaderCat) where
  Wellformed : A.Image → Prop
  permanent : Refusal → Prop
  rejects : ∀ i r, A.load i = .error r → permanent r → ¬ Wellformed i

end LoaderCat

/-- Runtime objects retain the existing runtime representation. -/
structure RuntimeCat : Type 1 where
  Image : Type
  Program : Type
  Event : Type
  runtime : Runtime Image Program Event

namespace RuntimeCat

def loader (A : RuntimeCat) : LoaderCat := ⟨A.Image, A.Program, A.runtime.load⟩

@[ext] structure Hom (A B : RuntimeCat) where
  loading : A.loader ⟶ B.loader
  observe : Adapter A.Event B.Event
  simulates : ∀ i b, A.runtime.beh i b → B.runtime.beh (loading.image i) (observe.run b)

def Hom.id (A : RuntimeCat) : Hom A A := ⟨𝟙 A.loader, Adapter.id, fun _ _ h => h⟩
def Hom.comp {A B C : RuntimeCat} (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨f.loading ≫ g.loading, f.observe.comp g.observe, fun i b h =>
    g.simulates _ _ (f.simulates i b h)⟩

instance : Category RuntimeCat where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intros; ext <;> rfl
  comp_id := by intros; ext <;> rfl
  assoc := by intros; ext <;> rfl

/-- A genuine forgetful functor: both object and arrow retain the loader data. -/
def forget : RuntimeCat ⥤ LoaderCat where
  obj := loader
  map f := f.loading

end RuntimeCat
end Silmaril.Containers
