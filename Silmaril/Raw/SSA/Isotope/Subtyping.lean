module

public import Silmaril.SSA.Isotope.Types.Thms
public import Silmaril.Raw.SSA.Isotope.Subtyping.Core

/-!
# Proof-relevant subtyping

Subtyping derivations live in `Type`, rather than `Prop`, so denotations may
depend on the chosen coercion derivation.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope

variable {τ : Type u} {α : Type u}

/-- The operations required of a proof-relevant subtyping discipline. -/
class Subtyping (τ : Type u) [TypeFormers τ] extends SubtypingCore τ where
  product {A A' B B' : τ} : Subty A A' → Subty B B' →
    Subty (Silmaril.product A B) (Silmaril.product A' B')
  coprod {A A' B B' : τ} : Subty A A' → Subty B B' →
    Subty (Silmaril.coprod A B) (Silmaril.coprod A' B')
  empty (A : τ) : Subty Silmaril.empty A
  unit (A : τ) : Subty A Silmaril.unit

namespace Subty

def product [TypeFormers τ] [Subtyping τ] {A A' B B' : τ}
    (f : Subty A A') (g : Subty B B') :
    Subty (Silmaril.product A B) (Silmaril.product A' B') := Subtyping.product f g

def coprod [TypeFormers τ] [Subtyping τ] {A A' B B' : τ}
    (f : Subty A A') (g : Subty B B') :
    Subty (Silmaril.coprod A B) (Silmaril.coprod A' B') := Subtyping.coprod f g

def empty [TypeFormers τ] [Subtyping τ] (A : τ) : Subty Silmaril.empty A :=
  Subtyping.empty A

def unit [TypeFormers τ] [Subtyping τ] (A : τ) : Subty A Silmaril.unit :=
  Subtyping.unit A

end Subty

namespace Ty

/-- The freely generated proof-relevant subtyping derivations for simple types. -/
inductive Subty {α : Type u} : Ty α → Ty α → Type u where
  | refl (A : Ty α) : Subty A A
  | trans {A B C : Ty α} : Subty A B → Subty B C → Subty A C
  | product {A A' B B' : Ty α} : Subty A A' → Subty B B' →
      Subty (.product A B) (.product A' B')
  | coprod {A A' B B' : Ty α} : Subty A A' → Subty B B' →
      Subty (.coprod A B) (.coprod A' B')
  | empty (A : Ty α) : Subty .empty A
  | unit (A : Ty α) : Subty A .unit

instance : Subtyping (Ty α) where
  Subty := Ty.Subty
  refl := Ty.Subty.refl
  trans := Ty.Subty.trans
  product := Ty.Subty.product
  coprod := Ty.Subty.coprod
  empty := Ty.Subty.empty
  unit := Ty.Subty.unit

section Examples

variable {α : Type u} (A : Ty α)

/-- Reflexivity and reflexivity followed by reflexivity remain distinct data. -/
example : Ty.Subty.refl A ≠ Ty.Subty.trans (Ty.Subty.refl A) (Ty.Subty.refl A) := by
  intro h
  cases h

end Examples

end Ty

end Silmaril.Isotope
