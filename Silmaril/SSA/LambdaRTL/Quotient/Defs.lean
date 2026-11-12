module

public import Silmaril.Logic.Institution.Morphism

/-!
# Institutions modulo semantic equivalence of sentences

`Room.quot R` identifies two sentences of a room when they hold in exactly the same models;
corridors descend (their satisfaction condition is exactly what is needed), giving a functor
`quotFunctor : Room ⥤ Room`, institutions `Inst.quot A` and comorphisms `CoHom.quot f`.

This is the setting in which comorphisms that are identity on signatures and models can be
mutually inverse although their sentence translations are not inverse on the nose (e.g. named
vs nameless syntax, where the round trip renames binders and the context).
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.Quotient

open CategoryTheory Silmaril.Logic.Institution

universe w m₁ m₂ u v

/-- Semantic equivalence of sentences: same models. -/
def semSetoid (R : Room.{w, m₁, m₂}) : Setoid R.Sen where
  r φ ψ := ∀ M, R.Sat M φ ↔ R.Sat M ψ
  iseqv := ⟨fun _ _ => Iff.rfl, fun h M => (h M).symm, fun h k M => (h M).trans (k M)⟩

/-- A room with sentences taken up to semantic equivalence. -/
def Room.quot (R : Room.{w, m₁, m₂}) : Room.{w, m₁, m₂} where
  Sen := Quotient (semSetoid R)
  Mod := R.Mod
  Sat M := Quotient.lift (R.Sat M) (fun _ _ h => propext (h M))

/-- Corridors descend to the quotients. -/
def Corridor.quot {R₁ R₂ : Room.{w, m₁, m₂}} (c : R₁ ⟶ R₂) : Room.quot R₁ ⟶ Room.quot R₂ :=
  ⟨Quotient.map c.sen (fun φ ψ h M => (c.sat M φ).trans ((h _).trans (c.sat M ψ).symm)),
    c.mod, fun M q => by
      induction q using Quotient.ind with
      | _ φ => exact c.sat M φ⟩

/-- Quotienting by semantic equivalence, as an endofunctor of rooms. -/
def quotFunctor : Room.{w, m₁, m₂} ⥤ Room.{w, m₁, m₂} where
  obj := Room.quot
  map := Corridor.quot
  map_id R := by
    apply Room.hom_ext
    · funext q; induction q using Quotient.ind; rfl
    · rfl
  map_comp f g := by
    apply Room.hom_ext
    · funext q; induction q using Quotient.ind; rfl
    · rfl

/-- An institution with sentences up to semantic equivalence. -/
def Inst.quot (A : Inst.{u, v, w, m₁, m₂}) : Inst.{u, v, w, m₁, m₂} :=
  ⟨A.Sign, A.I ⋙ quotFunctor⟩

/-- Comorphisms descend to the quotients. -/
def CoHom.quot {A B : Inst.{u, v, w, m₁, m₂}} (f : Inst.CoHom A B) :
    Inst.CoHom (Inst.quot A) (Inst.quot B) :=
  ⟨f.Φ, Functor.whiskerRight f.ρ quotFunctor⟩

/-- The sentence translation of a descended comorphism on a class. -/
theorem CoHom.quot_sen_mk {A B : Inst.{u, v, w, m₁, m₂}} (f : Inst.CoHom A B) (S : A.Sign)
    (φ : (A.I.obj S).Sen) :
    (((CoHom.quot f).ρ.app S).sen (Quotient.mk (semSetoid (A.I.obj S)) φ)) =
      Quotient.mk (semSetoid (B.I.obj (f.Φ.obj S))) ((f.ρ.app S).sen φ) := rfl

end Silmaril.SSA.LambdaRTL.Quotient
