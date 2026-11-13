module

public import Silmaril.Compile.Category.Convention
public import Silmaril.Logic.Institution.Morphism

@[expose] public section

/-!
# Behavioural institutions of languages

Every language determines an institution, its *behavioural institution*
(`Silmaril.Compile.Category.Language`): signatures are interfaces (a discrete category for now),
sentences are sets of observations, models are behaviour sets ordered by inclusion, and
satisfaction is inclusion. A read-back convention is an institution comorphism between the
behavioural institutions of its languages.

This file is the only part of the category of compilers that uses `Silmaril.Logic.Institution`;
the rest depends on order and category theory only.

## Main definitions

* `Language.room`, `Language.inst`: the behavioural institution.
* `Convention.corridor`, `Convention.comorphism`: the comorphism of a read-back convention.
-/

namespace Silmaril.Compile.Category

open CategoryTheory Silmaril.Logic.Institution

universe u

namespace Language

variable (L : Language.{u})

/-- The room of an interface: sentences are sets of observations, models are behaviour sets
ordered by inclusion, and satisfaction is inclusion.

Source: Mossakowski, Diaconescu and Tarlecki, *What is a logic translation?*, Logica Universalis 3 (2009), §3,
Definition 3.1. -/
def room (_ : L.Iface) : Room.{u, u, u} where
  Sen := Set L.Obs
  Mod := Cat.of (Set L.Obs)
  Sat := fun (B : Set L.Obs) (φ : Set L.Obs) => B ⊆ φ

/-- The behavioural institution of a language: a room functor on the discrete category of
interfaces.

Source: Goguen and Burstall, *Institutions: abstract model theory for specification and programming*, J. ACM 39 (1992), §2.5, Definition 12. -/
def inst : Inst.{u, u, u, u, u} where
  Sign := Discrete L.Iface
  I := Discrete.functor fun S => L.room S

/-- Satisfaction of a program is satisfaction of its behaviour model in the room of its
interface. -/
theorem sat_iff_room (p : L.Prog) (φ : Set L.Obs) :
    L.Sat p φ ↔ (L.room (L.iface p)).Sat (L.beh p) φ := Iff.rfl

end Language

namespace Convention

variable {L L' L'' : Language.{u}}

/-- The corridor `L.room S ⟶ L'.room (Φ S)` of a read-back convention: specifications translate
forwards by `α = c.lift`, behaviour models translate backwards by `β = g ''`, and
`B' ⊆ α φ ↔ β B' ⊆ φ` (the comorphism satisfaction condition).

Source: Mossakowski, Diaconescu and Tarlecki, *What is a logic translation?*, Logica Universalis 3 (2009), §3,
Definition 3.4. -/
def corridor {c : Convention L L'} (h : ReadBack c) (S : L.Iface) :
    L.room S ⟶ L'.room (c.Φ S) where
  sen := c.lift
  mod := Monotone.functor (X := Set L'.Obs) (Y := Set L.Obs) (f := Set.image h.g)
    fun _ _ hB => Set.image_mono hB
  sat B' φ := h.subset_lift_iff (B' : Set L'.Obs) φ

/-- The institution comorphism `(Φ, α, β) : L.inst → L'.inst` of a read-back convention.

Source: Goguen and Roşu, *Institution morphisms*, Formal Aspects of Computing 13 (2002), §4, Definition 4.2. -/
def comorphism {c : Convention L L'} (h : ReadBack c) : Inst.CoHom L.inst L'.inst where
  Φ := Discrete.functor fun S => Discrete.mk (c.Φ S)
  ρ := Discrete.natTrans fun S => corridor h S.as

/-- The corridors of a composite read-back convention are the composites of the corridors. -/
theorem corridor_comp {c : L ⟶ L'} {d : L' ⟶ L''} (hc : ReadBack c) (hd : ReadBack d)
    (S : L.Iface) :
    corridor (hc.comp hd) S = corridor hc S ≫ corridor hd (c.Φ S) := by
  refine Room.hom_ext (funext fun (B : Set L.Obs) => lift_comp c d B) ?_
  exact Functor.ext (fun (B : Set L''.Obs) => Set.image_comp hc.g hd.g B) (fun _ _ _ => rfl)

end Convention

end Silmaril.Compile.Category
