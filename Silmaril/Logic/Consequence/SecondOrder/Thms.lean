module

public import Silmaril.Logic.Consequence.SecondOrder.Defs
public import Silmaril.Logic.Consequence.Soundness.Thms
public import Silmaril.Logic.SecondOrderArithmetic.FullStandard
public import Silmaril.Logic.SecondOrderArithmetic.SExp.Thms
import Silmaril.Proofs.Logic.Consequence.SecondOrder.Basic

/-!
# Second-order arithmetic: soundness, consistency, inclusions, concrete syntax and problems

* **Soundness**: `derives_soundFor_henkin S` (Henkin models of `S`) and `derives_soundFor_full S`
  (the full standard model, `Silmaril.Logic.SecondOrderArithmetic.validAxioms_fullStandard`).
* **Consistency**, relative to Lean and to the full standard model: `consistent S` for every
  subsystem (no derivation of `succ 0 = 0` from no hypotheses). No claim about extensions.
* **Inclusions**: `rca0_le_aca0`, `aca0_le_z2`, `rca0_le_wkl0`.
* **Concrete syntax** (`silmaril.soa.formula`): `concrete_consistent`.
* **Problems** with explicit derivations and their standard meaning: `succNeZero`
  (`(not (= (succ zero) zero))`, from the base axiom `axS0`, in RCA0) and `comprehensionEq`
  (`∃X ∀x (x ∈ X ↔ x = x)`, by full comprehension, in Z2).
-/

@[expose] public section

namespace Silmaril.Consequence.SecondOrder

open Silmaril.Logic.SecondOrderArithmetic Silmaril.Logic.ArithmeticToSecondOrder
open Silmaril.Logic.Concrete
open Silmaril.Logic.Smt (SE)

/-- **Soundness for Henkin semantics.** -/
theorem derives_soundFor_henkin (S : Subsystem) : (derives S).SoundFor (henkin S) :=
  fun _ _ ⟨d⟩ p hΓ => Proofs.Logic.Consequence.SecondOrder.hproof_sound p.1.1 p.1.2 d p.2 hΓ

/-- **Soundness for the full standard model.** -/
theorem derives_soundFor_full (S : Subsystem) : (derives S).SoundFor full :=
  fun _ _ ⟨d⟩ ρ hΓ =>
    Proofs.Logic.Consequence.SecondOrder.hproof_sound fullStandard (validAxioms_fullStandard S) d ρ hΓ

/-- **Every subsystem is consistent**: no derivation of `succ 0 = 0` from no hypotheses. -/
theorem consistent (S : Subsystem) : (derives S).ConsistentWrt falsum [] :=
  consistentWrt_of_sound (derives_soundFor_full S) fullStandard.env₀ (fun _ h => by cases h)
    (by simp [full, falsum, Formula.henkinEval, Term.henkinEval, fullStandard, omegaStructure])

theorem rca0_le_aca0 : derives .RCA0 ≤ derives .ACA0 :=
  fun _ _ ⟨d⟩ => ⟨Proofs.Logic.Consequence.SecondOrder.HProof.mapSystem Proof.rcaToACA d⟩

theorem aca0_le_z2 : derives .ACA0 ≤ derives .Z2 :=
  fun _ _ ⟨d⟩ => ⟨Proofs.Logic.Consequence.SecondOrder.HProof.mapSystem Proof.acaToZ2 d⟩

theorem rca0_le_wkl0 : derives .RCA0 ≤ derives .WKL0Sep :=
  fun _ _ ⟨d⟩ => ⟨Proofs.Logic.Consequence.SecondOrder.HProof.mapSystem Proof.rcaToWkl d⟩

/-- **Over S-expressions, every subsystem is consistent.** -/
theorem concrete_consistent (S : Subsystem) :
    ((derives S).viaCodec SExp.codec).ConsistentWrt (SExpCodec.Sen.ofAbs falsum) [] :=
  (viaCodec_consistentWrt_iff (derives S) SExp.codec [] falsum).2 (consistent S)

/-! ## Concrete problems -/

/-- `succ 0 ≠ 0`, written `(not (= (succ zero) zero))`. -/
def succNeZero : Formula String := .neg (.equal (.succ .zero) .zero)

theorem succNeZero_decode :
    SExp.codec.decode (.list [.atom "not", .list [.atom "=", .list [.atom "succ", .atom "zero"],
      .atom "zero"]]) = some succNeZero :=
  (SExp.codec.decode_eq_some_iff _ _).2 (by simp [SExp.codec, SExp.encodeFormula, SExp.encodeTerm, succNeZero])

/-- Derived in RCA0, from the base axiom `axS0`. -/
theorem succNeZero_derived : derives .RCA0 [] succNeZero := ⟨HProof.base (.axS0 .zero)⟩

/-- Its standard meaning. -/
theorem succNeZero_true (ρ : fullStandard.Env String) : succNeZero.henkinEval fullStandard ρ :=
  derives_soundFor_full .RCA0 [] _ succNeZero_derived ρ (fun _ h => by cases h)

/-- `∃X ∀x (x ∈ X ↔ x = x)`, an instance of comprehension. -/
def comprehensionEq : Formula String :=
  .comprehension "x" "X" (.equal (.var "x") (.var "x"))

/-- Derived in Z2, by full comprehension. -/
theorem comprehensionEq_z2 : derives .Z2 [] comprehensionEq :=
  ⟨.proved (.axiom (.fullComp "x" "X" _ (Or.inl rfl) (by decide)))⟩

/-- Its standard meaning, from soundness. -/
theorem comprehensionEq_true (ρ : fullStandard.Env String) :
    comprehensionEq.henkinEval fullStandard ρ :=
  derives_soundFor_full .Z2 [] _ comprehensionEq_z2 ρ (fun _ h => by cases h)

end Silmaril.Consequence.SecondOrder
