module

public import Silmaril.Proofs.Wasm.Auto.Front.Prove
public import Silmaril.Wasm.Auto.Bridge.Thms

/-!
# The front end with the extended summaries: soundness

A `proved` report of `checkRefines`/`checkEquiv`/`proveStage` proves `ModEquiv` at every
profile (from the summaries stage of `Silmaril.Wasm.Auto.Front` or from
`Silmaril.Wasm.Auto.Bridge.modEquiv_of_fnCheckX`); a `refuted` report is a refutation (that of
`Silmaril.Wasm.Auto.Front`). Stated in `Silmaril.Wasm.Auto.Front.Thms`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Front

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Front
open Silmaril.Wasm.Auto
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (profile)
open Silmaril.Wasm.Verify (refOracle)

theorem upgrade_proved {r : Report} {ok : Bool} (h : (upgrade r ok).verdict = .proved) :
    r.verdict = .proved ∨ ok = true := by
  unfold upgrade at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact Or.inr hc.2
  · exact Or.inl h

theorem upgrade_refuted {r : Report} {ok : Bool} (h : (upgrade r ok).verdict = .refuted) :
    r.verdict = .refuted := by
  unfold upgrade at h
  split at h
  · cases h
  · exact h

/-- **A `proved` report of `checkRefines` proves the equivalence**, every profile (`hid`: the
`identical` flag is only set for identical modules). -/
theorem checkRefines_proved {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → impl = spec) (h : (checkRefines R impl spec j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P impl spec j := by
  rcases upgrade_proved h with h | h
  · exact checkRefinesBase_proved hid h P
  · exact Bridge.modEquiv_of_fnCheckX (Bridge.rel_refl R) h

/-- **A `proved` report of `checkEquiv` proves the equivalence**, every profile. -/
theorem checkEquiv_proved {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → m₁ = m₂) (h : (checkEquiv R m₁ m₂ j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P m₁ m₂ j := by
  rcases upgrade_proved h with h | h
  · exact checkEquivBase_proved hid h P
  · exact Bridge.modEquiv_of_fnCheckX (Bridge.rel_refl R) h

/-- **A `proved` verdict of the proving stages is an equivalence**, every profile. -/
theorem modEquiv_of_proveStage {m₁ m₂ : Module} {j : Nat}
    (h : (proveStage m₁ m₂ j).verdict = .proved) (R : Rel) (P : Profile) :
    ModEquiv R.toProp P m₁ m₂ j := by
  rcases upgrade_proved h with h | h
  · exact modEquiv_of_proveStageBase h R P
  · exact Bridge.modEquiv_of_fnCheckX (Bridge.rel_refl R) h

/-- A `refuted` report of `checkRefines` is a refutation. -/
theorem checkRefines_refuted {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (h : (checkRefines R impl spec j n idt).verdict = .refuted) :
    ¬ ModRefines R.toProp (profile refOracle) impl spec j :=
  checkRefinesBase_refuted (upgrade_refuted h)

/-- A `refuted` report of `checkEquiv` is a refutation. -/
theorem checkEquiv_refuted {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (h : (checkEquiv R m₁ m₂ j n idt).verdict = .refuted) :
    ¬ ModEquiv R.toProp (profile refOracle) m₁ m₂ j :=
  checkEquivBase_refuted (upgrade_refuted h)

end Silmaril.Proofs.Wasm.Auto.Front
