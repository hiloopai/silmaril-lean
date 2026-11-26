module

public import Silmaril.Logic.Consequence.Structural.Witness.Thms

/-!
# Examples: witness-carrying derivations

Successor steps `[n] ⊢ n + 1` carry their `n` as a witness. A derivation of `[0] ⊢ 2` keeps
both steps (`leaves` lists them); erasing it gives a `Derives` proof.
-/

@[expose] public section

namespace Silmaril.Consequence.Structural.Witness.Examples

/-- A successor step `[n] ⊢ n + 1`, witnessed by `n`. -/
def Step : List Nat → Nat → Type := fun Γ c => { n : Nat // Γ = [n] ∧ c = n + 1 }

/-- The witnesses at the leaves of a derivation, left to right. -/
def leaves {rs : Rules Nat} : {Γ : List Nat} → {c : Nat} → WDerives rs Step Γ c → List Nat
  | _, _, .base w => [w.1]
  | _, _, .refl _ _ => []
  | _, _, .weak _ d => leaves d
  | _, _, .cut ps _ ds d =>
    (ps.attach.flatMap fun p => leaves (ds p.1 p.2)) ++ leaves d

/-- `[0] ⊢ 2` by one cut of `[0] ⊢ 1` against `[1] ⊢ 2`. -/
def zeroTwo : WDerives (jointRules List.Sublist) Step [0] 2 :=
  .cut [([0], 1)] trivial (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact .base ⟨0, rfl, rfl⟩)
    (.base ⟨1, rfl, rfl⟩)

theorem zeroTwo_leaves : leaves zeroTwo = [0, 1] := by decide

theorem zeroTwo_erase : Derives (jointRules List.Sublist) (fun Γ c => Nonempty (Step Γ c)) [0] 2 :=
  zeroTwo.erase

/-- Flattening: a leaf holding `zeroTwo` grafts to `zeroTwo` itself. -/
theorem flatten_base_zeroTwo : WDerives.flatten (.base zeroTwo) = zeroTwo := rfl

end Silmaril.Consequence.Structural.Witness.Examples
