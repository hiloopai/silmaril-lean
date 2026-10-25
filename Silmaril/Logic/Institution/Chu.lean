module

public import Silmaril.Logic.Institution.Room

@[expose] public section

/-!
# Chu spaces and rooms

A Chu space `(A, r, X)` over an alphabet `K` is a matrix `r : A → X → K` with rows the points `A`
and columns the states `X`; a Chu transform `(f, g) : (A, r, X) → (B, s, Y)` is a pair
`f : A → B`, `g : Y → X` with `s (f a) y = r a (g y)` (Pratt's "adjointness condition").

A room is a Chu space over `Prop` whose states carry morphisms: points are sentences, states are
models, and the matrix is satisfaction. A corridor is a Chu transform, its adjointness condition
being the satisfaction condition. `Room.toChu` is this forgetful functor; it is how the room view
of institutions meets Pratt's Chu spaces and the observation that "Chu transformations are …
comorphisms" of one-signature institutions
(`goguen-2004-information-integration-institutions` in `references.bib`, §3.3).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe z a b w m₁ m₂

/-- A Chu space over the alphabet `K`.

Source: `pratt-chu-1999` in `references.bib`, §1.1, Definition 1. -/
structure ChuSpace (K : Type z) where
  /-- The points (the carrier). -/
  pts : Type a
  /-- The states (the cocarrier). -/
  states : Type b
  /-- The matrix. -/
  r : pts → states → K

namespace ChuSpace

variable {K : Type z}

/-- A Chu transform: a forward map on points and a backward map on states satisfying the
adjointness condition `s (f a) y = r a (g y)`.

Source: `pratt-chu-1999` in `references.bib`, §1.4. -/
@[ext]
structure Hom (A B : ChuSpace.{z, a, b} K) : Type (max a b) where
  /-- The forward map on points. -/
  f : A.pts → B.pts
  /-- The backward map on states. -/
  g : B.states → A.states
  /-- The adjointness condition. -/
  adj : ∀ x y, B.r (f x) y = A.r x (g y)

/-- Chu spaces over `K` and Chu transforms form the category `Chu_K`.

Source: `pratt-chu-1999` in `references.bib`, §1.4 ("The category whose
objects are Chu spaces over Σ and whose morphisms are Chu transforms … is denoted Chu_Σ"). -/
instance category : Category.{max a b} (ChuSpace.{z, a, b} K) where
  Hom := Hom
  id _ := ⟨id, id, fun _ _ => rfl⟩
  comp h k := ⟨k.f ∘ h.f, h.g ∘ k.g, fun x y => (k.adj (h.f x) y).trans (h.adj x (k.g y))⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end ChuSpace

/-- Forgetting model morphisms, a room is a Chu space over `Prop` (points: sentences, states:
models, matrix: satisfaction) and a corridor is a Chu transform.

Source: `pratt-chu-1999` in `references.bib`, §1.1 and §1.4;
`goguen-2004-information-integration-institutions` in `references.bib`, §3.3 (Chu spaces as
institutions with one signature, Chu transformations as their comorphisms). -/
def Room.toChu : Room.{w, m₁, m₂} ⥤ ChuSpace.{0, w, m₂} Prop where
  obj R := ⟨R.Sen, R.Mod, fun φ M => R.Sat M φ⟩
  map c := ⟨c.sen, c.mod.obj, fun φ M => propext (c.sat M φ)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A corridor is exactly a Chu transform of the underlying Chu spaces together with a functor on
models whose action on objects is the transform's state map: the satisfaction condition of the
corridor is the adjointness condition of the transform.

Source: `pratt-chu-1999` in `references.bib`, §1.4 (adjointness condition);
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.4 and footnote 10. -/
def Room.corridorEquiv (R₁ R₂ : Room.{w, m₁, m₂}) :
    (R₁ ⟶ R₂) ≃ {p : (Room.toChu.obj R₁ ⟶ Room.toChu.obj R₂) × (R₂.Mod ⥤ R₁.Mod) //
      p.2.obj = p.1.g} where
  toFun c := ⟨(Room.toChu.map c, c.mod), rfl⟩
  invFun p := ⟨p.1.1.f, p.1.2, fun M φ => by
    rw [p.2]
    exact Iff.of_eq (p.1.1.adj φ M)⟩
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext (ChuSpace.Hom.ext rfl p.2) rfl)

end Silmaril.Logic.Institution
