module

public import Silmaril.Logic.Metatheory.ArithmeticSystems.Basic

@[expose] public section

/-!
# Limits of forgetting arithmetic structure

The forgetful functor is faithful but fails to be full whenever the base has
a proof. Doubling each proof fiber leaves the syntax untouched. An ambient
arrow can flip the extra Boolean label, whereas a structured arrow must keep
the chosen base proofs (whose label is false).
-/

namespace Silmaril.Logic.Metatheory.ArithmeticSystems.System

open CategoryTheory

universe u v

variable (B : InferenceSystemCat.{u, v})

/-- A system with two distinguishable copies of each base proof. -/
def doubled : System B where
  inference := ⟨B.Conclusion, fun a => B.Derivation a × Bool⟩
  base := { map := id, mapDerivation := fun d => (d, false) }
  faithfulSyntax := Function.injective_id

/-- An ambient automorphism that changes the chosen base proof label. -/
def flip : (doubled B).inference ⟶ (doubled B).inference where
  map := id
  mapDerivation d := (d.1, !d.2)

theorem flip_comp_flip : flip B ≫ flip B = 𝟙 (doubled B).inference := by
  apply InferenceSystemCat.hom_ext
  · intro a
    rfl
  · intro a d
    cases d with
    | mk d b => cases b <;> rfl

theorem flip_not_lift {a : B.Conclusion} (d : B.Derivation a) :
    ¬ ∃ f : doubled B ⟶ doubled B, forget.map f = flip B := by
  intro h
  have commutes := (lift_iff (flip B)).mp h
  have hd := InferenceSystemCat.hom_congr_derivation commutes a d
  have heq : (d, true) = (d, false) := eq_of_heq hd
  have hb := congrArg Prod.snd heq
  cases hb

/-- A base with a theorem gives an explicit obstruction to fullness. -/
theorem forget_not_full {a : B.Conclusion} (d : B.Derivation a) :
    ¬ (forget (B := B)).Full := by
  intro h
  let := h
  exact flip_not_lift B d
    (Functor.map_surjective (F := forget) (X := doubled B) (Y := doubled B) (flip B))

/-- The ambient inference system with two additional underivable conclusions. -/
def paddedInference : InferenceSystemCat.{u, v} :=
  ⟨B.Conclusion ⊕ Bool, fun
    | .inl a => B.Derivation a
    | .inr _ => PEmpty⟩

/-- Add two extra conclusions with no proofs, leaving the arithmetic base intact. -/
def padded : System B where
  inference := paddedInference B
  base := { map := Sum.inl, mapDerivation := fun d => d }
  faithfulSyntax := Sum.inl_injective

/-- A structured arrow can still rename conclusions outside the chosen arithmetic. -/
def flipPadding : padded B ⟶ padded B where
  inference := {
    map := fun
      | .inl a => .inl a
      | .inr b => .inr (!b)
    mapDerivation := fun {a} d => match a with
      | .inl _ => d
      | .inr _ => d.elim }
  commutes := rfl

theorem flipPadding_ne_id : flipPadding B ≠ 𝟙 (padded B) := by
  intro h
  have hc := congrArg (fun f : padded B ⟶ padded B => f.inference.map (.inr false)) h
  have hb : (Sum.inr true : B.Conclusion ⊕ Bool) = .inr false := hc
  cases hb

theorem fragment_flipPadding : fragment.map (flipPadding B) = 𝟙 (fragment.obj (padded B)) := rfl

/-- The common arithmetic fragment forgets ambient conclusions and is not faithful. -/
theorem fragment_not_faithful : ¬ (fragment (B := B)).Faithful := by
  intro h
  let := h
  apply flipPadding_ne_id B
  apply Functor.map_injective (F := fragment)
  rw [fragment_flipPadding, Functor.map_id]

end Silmaril.Logic.Metatheory.ArithmeticSystems.System
