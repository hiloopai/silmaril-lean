module

public import Silmaril.Wasm.Auto2.Front2.Defs
public import Silmaril.Wasm.Auto2.Summ2.Thms
public import Silmaril.Wasm.Auto2.Calls.Thms

/-!
# The front end, soundness (unrefined)

`checkEquivV_proved`, `checkRefinesV_proved`, `modEquiv_of_proveStageV`: a `proved` report proves
`ModEquiv` at every profile; `checkEquivV_refuted`: a `refuted` report is a refutation at the
deterministic profile (the later stages never refute).

New proofs (unrefined).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Front2

open Silmaril.Wasm Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Front (Report Rel ModEquiv)

theorem upgradeV_proved {r : Report} {st : String} {ok : Unit → Bool}
    (h : (upgradeV r st ok).verdict = .proved) : r.verdict = .proved ∨ ok () = true := by
  unfold upgradeV at h
  split at h
  · split at h
    · rename_i hc
      exact Or.inr hc
    · exact Or.inl h
  · exact Or.inl h

theorem upgradeV_refuted {r : Report} {st : String} {ok : Unit → Bool}
    (h : (upgradeV r st ok).verdict = .refuted) : r.verdict = .refuted := by
  unfold upgradeV at h
  split at h
  · split at h
    · cases h
    · exact h
  · exact h

/-- The later stages prove what they claim. -/
theorem laterStages_proved {r : Report} {m₁ m₂ : Module} {j : Nat}
    (h : (laterStages r m₁ m₂ j).verdict = .proved) (R : Rel) (P : Profile)
    (hr : r.verdict = .proved → ModEquiv R.toProp P m₁ m₂ j) : ModEquiv R.toProp P m₁ m₂ j := by
  rcases upgradeV_proved h with h | h
  · rcases upgradeV_proved h with h | h
    · exact hr h
    · exact Silmaril.Wasm.Auto2.Summ2.modEquiv_of_fnCheckV (Silmaril.Wasm.Auto.Bridge.rel_refl R) h
  · exact Silmaril.Wasm.Auto2.VCEquiv.modEquiv_of_vcEquivAny (Silmaril.Wasm.Auto.Bridge.rel_refl R) h

theorem laterStages_refuted {r : Report} {m₁ m₂ : Module} {j : Nat}
    (h : (laterStages r m₁ m₂ j).verdict = .refuted) : r.verdict = .refuted :=
  upgradeV_refuted (upgradeV_refuted h)

/-- **A `proved` report of `checkEquivV` proves the equivalence**, every profile (`hid`: the
`identical` flag is only set for identical modules). -/
theorem checkEquivV_proved {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → m₁ = m₂) (h : (checkEquivV R m₁ m₂ j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P m₁ m₂ j :=
  laterStages_proved h R P fun h => Silmaril.Wasm.Auto2.Calls.checkEquivC_proved hid h P

/-- **A `proved` report of `checkRefinesV` proves the equivalence**, every profile. -/
theorem checkRefinesV_proved {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → impl = spec) (h : (checkRefinesV R impl spec j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P impl spec j :=
  laterStages_proved h R P fun h => Silmaril.Wasm.Auto2.Calls.checkRefinesC_proved hid h P

/-- A `refuted` report of `checkEquivV` is a refutation at the deterministic profile. -/
theorem checkEquivV_refuted {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (h : (checkEquivV R m₁ m₂ j n idt).verdict = .refuted) :
    ¬ ModEquiv R.toProp (Silmaril.Wasm.SingleThreaded.profile Silmaril.Wasm.Verify.refOracle)
      m₁ m₂ j :=
  Silmaril.Wasm.Auto2.Calls.checkEquivC_refuted (laterStages_refuted h)

/-- **A `proved` verdict of the proving stages is an equivalence**, every profile. -/
theorem modEquiv_of_proveStageV {m₁ m₂ : Module} {j : Nat}
    (h : (proveStageV m₁ m₂ j).verdict = .proved) (R : Rel) (P : Profile) :
    ModEquiv R.toProp P m₁ m₂ j :=
  laterStages_proved h R P fun h => Silmaril.Wasm.Auto2.Calls.modEquiv_of_proveStageC h R P

end Silmaril.Wasm.Auto2.Front2
