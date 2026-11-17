module

public import Silmaril.Logic.SecondOrderArithmetic.Defs
public import Silmaril.Logic.SecondOrderArithmetic.Thms
public import Silmaril.Logic.SecondOrderArithmetic.Semantics
import Silmaril.Proofs.Logic.SecondOrderArithmetic.FullStandard

/-!
# Second-order arithmetic in the full standard model

`fullStandard` is ℕ with **every** subset of ℕ (full, not Henkin, semantics). Every axiom of every
subsystem (`RCA0`, `WKL0Sep`, `ACA0`, `Z2`, `Z2Full`) holds there (`validAxioms_fullStandard`):
the base axioms in every ω-model, induction in every ω-model, comprehension and separation because
every defined set is a set. With `proof_sound` this gives soundness of each subsystem for the full
standard model (`proof_fullStandard`) and its consistency (`consistent`): `1 = 0`, written
`succ 0 = 0`, is not provable. These are relative to Lean (with its classical axioms); they do not
claim consistency of any extension by further axioms.
-/

@[expose] public section

namespace Silmaril.Logic.SecondOrderArithmetic

variable {N : Type} [DecidableEq N]

/-- **Every axiom of every subsystem is valid in the full standard model.** -/
theorem validAxioms_fullStandard (S : Subsystem) : ValidAxioms (N := N) S fullStandard :=
  Proofs.Logic.SecondOrderArithmetic.validAxioms_fullStandard S

/-- **Soundness for the full standard model.** -/
theorem proof_fullStandard {S : Subsystem} {p : Formula N} (d : Proof S p) (ρ : fullStandard.Env N) :
    p.henkinEval fullStandard ρ :=
  Theorems.proof_sound fullStandard (validAxioms_fullStandard S) d ρ

/-- An environment of the full standard model: every number `0`, every set empty. -/
def fullStandard.env₀ : fullStandard.Env N
  | .inl _ => (0 : ℕ)
  | .inr _ => ⟨∅, trivial⟩

/-- **Every subsystem is consistent**: `succ 0 = 0` is not provable. -/
theorem consistent (S : Subsystem) : ¬ Provable (N := N) S (.equal (.succ .zero) .zero) := by
  rintro ⟨d⟩
  have := proof_fullStandard d fullStandard.env₀
  simp [Formula.henkinEval, Term.henkinEval, fullStandard, omegaStructure] at this

end Silmaril.Logic.SecondOrderArithmetic
