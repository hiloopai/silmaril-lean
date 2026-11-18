module

public import Silmaril.ProofFormats.Alethe.Defs
public import Silmaril.Logic.Consequence.Resolution.Thms
import Silmaril.Proofs.ProofFormats.Alethe

/-!
# Alethe refutations: soundness

`checkRefutation_sound`: when an Alethe proof of the supported fragment checks against an SMT-LIB
problem, no valuation of the atoms satisfies all of the problem's assertions (propositional
unsatisfiability). The translation of the proof is untrusted: only the clause checker is relied
on.
-/

@[expose] public section

namespace Silmaril.ProofFormats.Alethe

open Silmaril.Consequence.Resolution
open Silmaril.Logic.Smt (SE)

/-- **An accepted Alethe refutation refutes the problem's assertions.** -/
theorem checkRefutation_sound {problem proof : List UInt8} {φs : List SE}
    (h : checkRefutation problem proof = .ok φs) : ¬ ∃ v : SE → Prop, ∀ φ ∈ φs, Holds v φ :=
  Proofs.ProofFormats.Alethe.checkRefutation_sound h

end Silmaril.ProofFormats.Alethe
