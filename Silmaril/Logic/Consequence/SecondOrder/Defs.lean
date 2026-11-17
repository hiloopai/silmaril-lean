module

public import Silmaril.Logic.Consequence.Soundness.Defs
public import Silmaril.Logic.ArithmeticToSecondOrder.Hilbert
public import Silmaril.Logic.SecondOrderArithmetic.Defs
public import Silmaril.Logic.SecondOrderArithmetic.SExp.Defs

/-!
# Second-order arithmetic as consequence systems: full and Henkin semantics

**Systems**, one per subsystem `S` of `Silmaril.Logic.SecondOrderArithmetic.Subsystem`:
* `RCA0` (Σ⁰₁ induction, Δ⁰₁ comprehension);
* `WKL0Sep` (RCA0 with Σ⁰₁ separation; its equivalence to weak König's lemma is not proved here);
* `ACA0` (Σ⁰₁ induction, arithmetical comprehension);
* `Z2` and `Z2Full` (full induction and full comprehension; they prove the same formulas).

`derives S`: `Γ ⊢ φ` when there is an explicit Hilbert proof `HProof S Γ φ` from the hypotheses
`Γ` (axiom instances, theorems of `S`, hypotheses and modus ponens). Formulas have names as strings.

**Interpretations**, kept apart:
* `full`: **full standard semantics**: numbers ℕ and sets *every* subset of ℕ (`fullStandard`), at
  a point (an environment); premises and conclusion are evaluated at the same point;
* `henkin S`: **Henkin semantics** of `S`: any two-sorted structure in which the axioms of `S`
  hold (`ValidAxioms`), with possibly nonstandard numbers and only some sets, at a point.
-/

@[expose] public section

namespace Silmaril.Consequence.SecondOrder

open Silmaril.Logic.SecondOrderArithmetic Silmaril.Logic.ArithmeticToSecondOrder

/-- **Second-order derivability** in the subsystem `S`: an explicit Hilbert proof from the
hypotheses. -/
def derives (S : Subsystem) : System (List (Formula String)) (Formula String) :=
  fun Γ φ => Nonempty (HProof S Γ φ)

/-- **Full standard semantics**, point-wise. -/
def full : Satisfaction (List (Formula String)) (Formula String) where
  Model := fullStandard.Env String
  satAx ρ Γ := ∀ γ ∈ Γ, γ.henkinEval fullStandard ρ
  satC ρ φ := φ.henkinEval fullStandard ρ

/-- **Henkin semantics** of `S`, point-wise: structures validating the axioms of `S`. -/
def henkin (S : Subsystem) : Satisfaction (List (Formula String)) (Formula String) where
  Model := Σ M : {M : HenkinStructure // ValidAxioms (N := String) S M}, M.1.Env String
  satAx p Γ := ∀ γ ∈ Γ, γ.henkinEval p.1.1 p.2
  satC p φ := φ.henkinEval p.1.1 p.2

/-- The chosen falsity: `succ 0 = 0`. -/
def falsum : Formula String := .equal (.succ .zero) .zero

end Silmaril.Consequence.SecondOrder
