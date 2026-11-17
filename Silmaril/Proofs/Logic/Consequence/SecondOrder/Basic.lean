module

public import Silmaril.Logic.Consequence.SecondOrder.Defs
public import Silmaril.Logic.SecondOrderArithmetic.Thms

/-! Proofs for `Silmaril.Logic.Consequence.SecondOrder.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.SecondOrder

open Silmaril.Logic.SecondOrderArithmetic Silmaril.Logic.ArithmeticToSecondOrder

/-- Hilbert proofs from hypotheses are sound point-wise in every structure validating the axioms. -/
theorem hproof_sound {S : Subsystem} (M : HenkinStructure) (hM : ValidAxioms (N := String) S M)
    {Γ : List (Formula String)} {φ : Formula String} (d : HProof S Γ φ) (ρ : M.Env String)
    (hΓ : ∀ γ ∈ Γ, γ.henkinEval M ρ) : φ.henkinEval M ρ := by
  induction d with
  | hyp h => exact hΓ _ h
  | proved p => exact Theorems.proof_sound M hM p ρ
  | mp _ _ ih ih' => exact ih' ih

/-- Translate the theorems used in a Hilbert proof from one subsystem to another. -/
def HProof.mapSystem {S T : Subsystem} (f : ∀ {p : Formula String}, Proof S p → Proof T p)
    {Γ : List (Formula String)} : {φ : Formula String} → HProof S Γ φ → HProof T Γ φ
  | _, .hyp h => .hyp h
  | _, .proved p => .proved (f p)
  | _, .mp d e => .mp (HProof.mapSystem f d) (HProof.mapSystem f e)

end Silmaril.Proofs.Logic.Consequence.SecondOrder
