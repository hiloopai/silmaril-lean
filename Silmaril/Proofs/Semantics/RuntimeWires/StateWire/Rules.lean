module

public import Silmaril.Semantics.RuntimeWires.StateWire.Defs

public section

namespace Silmaril.RuntimeWires.Proofs.StateWire

open CategoryTheory Presentation
open Silmaril.RuntimeWires.StateWire
open scoped MonoidalCategory

universe u v s

variable {G : EffectfulPolygraph.{u,v}} {S : Type s}

theorem transport_one {M : Type s} [Monoid M] {X Y : SingleObj M} (h : X = Y) :
    eqToHom h = (1 : M) := by
  subst h
  rfl

variable (update : G.effect.Edge → S → S)

local notation "F" => interpretation update

theorem run_gen (e : G.effect.Edge) : run update (effectGenerator G e) = update e := by
  have h := (assignment update).extension_extends.effects e
  simp only [SingleObj.comp_as_mul, transport_one, one_mul, mul_one] at h
  exact h

theorem run_pure {A B : Pure G} (f : A ⟶ B) :
    run update ((pureInclusion G).map f) = id := by
  have h := Functor.congr_hom (assignment update).extension.square f
  change (F).map ((pureInclusion G).map f) =
    eqToHom _ ≫ (𝟙 (SingleObj.star (Function.End S))) ≫ eqToHom _ at h
  simp only [SingleObj.comp_as_mul, transport_one, SingleObj.id_as_one, one_mul] at h
  exact h

theorem run_left (X : Computations G) {Y Z : Computations G} (f : Y ⟶ Z) :
    run update (X ◁ f) = run update f := by
  have h := (assignment update).extension.computationStrict.left X f
  change (F).map (X ◁ f) ≫ eqToHom _ = eqToHom _ ≫ (F).map f at h
  simp only [SingleObj.comp_as_mul, transport_one, one_mul, mul_one] at h
  exact h

theorem run_right {X Y : Computations G} (f : X ⟶ Y) (Z : Computations G) :
    run update (f ▷ Z) = run update f := by
  have h := (assignment update).extension.computationStrict.right f Z
  change (F).map (f ▷ Z) ≫ eqToHom _ = eqToHom _ ≫ (F).map f at h
  simp only [SingleObj.comp_as_mul, transport_one, one_mul, mul_one] at h
  exact h

end Silmaril.RuntimeWires.Proofs.StateWire
