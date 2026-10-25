module

public import Silmaril.Logic.SecondOrderArithmetic.Defs
public import Silmaril.Logic.SecondOrderArithmetic.MetamathSystems
import Silmaril.Proofs.Logic.SecondOrderArithmetic.Soundness

@[expose] public section

/-! Public statements for subsystem inclusions and the certified common
Hilbert fragment. The syntax correspondence for the remaining subsystem
schemas is in `MetamathSystems`; full proof transport for those schemas
requires additional sorting and disjoint-variable certificates. -/

namespace Silmaril.Logic.SecondOrderArithmetic.Theorems

variable {N : Type} [DecidableEq N]

/-- Every independent proof is sound once its axiom family is valid in the structure. -/
theorem proof_sound {S : Subsystem} (M : HenkinStructure)
    (h : ValidAxioms (N := N) S M) {p : Formula N} (d : Proof S p)
    (ρ : M.Env N) : p.henkinEval M ρ :=
  Silmaril.Proofs.Logic.SecondOrderArithmetic.proof_sound M h d ρ

/-- The common propositional fragment is valid in every Henkin structure. -/
theorem hilbert_sound (M : HenkinStructure) {p : Formula N} (d : HilbertProof p)
    (ρ : M.Env N) : p.henkinEval M ρ :=
  Silmaril.Proofs.Logic.SecondOrderArithmetic.hilbert_sound M d ρ

/-- RCA₀ derivations translate to the independent ACA₀ proof system. -/
theorem rca0_provable_in_aca0 {p : Formula N} (d : Proof .RCA0 p) :
    Provable .ACA0 p := ⟨d.rcaToACA⟩

/-- ACA₀ derivations translate to the independent full second-order system. -/
theorem aca0_provable_in_z2 {p : Formula N} (d : Proof .ACA0 p) :
    Provable .Z2 p := ⟨d.acaToZ2⟩

/-- The two full-schema presentations prove exactly the same formulas. -/
theorem z2_full_provable_iff (p : Formula N) : Provable .Z2 p ↔ Provable .Z2Full p :=
  z2_iff_full p

/-- The standard ω-structure agrees with the separately defined recursive evaluator. -/
theorem henkin_omega_eval (p : Formula N) (sets : Set (Set ℕ)) :
    p.henkinEval (omegaStructure sets) = p.eval (𝒮 := sets) := p.henkin_omega sets

/-- A sorted independent Hilbert proof produces a genuine native RCA₀ derivation. -/
theorem hilbert_to_native_rca0
    {A : Metamath.Grammar.TAssertion Metamath.SecondOrder.L
      Metamath.SecondOrder.C Metamath.SecondOrder.V}
    {p : Formula Metamath.SecondOrder.V} (d : HilbertProof p) (hd : d.Sorted A.ctx) :
    Nonempty (Metamath.Grammar.TDerivation Metamath.SecondOrder.grammar
      Metamath.SecondOrder.RCA0 A ⟨.turnstile, p.toTree⟩) := d.toNativeRCA0 hd

end Silmaril.Logic.SecondOrderArithmetic.Theorems
