module

public import Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.CastsV.Assemble

/-!
# SpecTec ↔ Core 3.0, round 6, track casts-v: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.CastsV`; see `docs/projects/spectec/README.md`.

* `castsInv_of_configOk`: a valid configuration has a valid store and, at each top-level cast
  (under labels, handlers and frames), an instantiated type valid in `{}` (`CastsInv`).
  `castsInv_closed`, `castsInv_of_configEq`: it is closed under the context rules and transfers
  along `ConfigEq`.
* `castRefOk_of_refOkBV`: `RefOkB.RefOkBV` gives `CastRefOk` wherever `CastsInv` and a bounded
  frame module hold.
* `casts_backend_of_refOkBV`, `casts_backend_spec_of_refOkBV`: **`Target.Casts Int.backend` from
  `RefOkBV`**, through track casts' generalized recursions `Casts.castsFwdG`/`Casts.castsBwdG`
  (and `fwd_*G`/`bwdKG_*`).
* `openR_backend_of_refOkBV`, `wholeStepValidR_backend_of_refOkBV`, `runsR_backend_of_refOkBV`:
  the round-6 target and its multi-step corollary at the backend reading, from `RefOkBV`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.castsInv_of_configOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.CastsV.castsInv_of_configOk

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.casts_backend_of_refOkBV' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.CastsV.casts_backend_of_refOkBV

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.casts_backend_spec_of_refOkBV' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.CastsV.casts_backend_spec_of_refOkBV

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.openR_backend_of_refOkBV' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.CastsV.openR_backend_of_refOkBV

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.wholeStepValidR_backend_of_refOkBV' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.CastsV.wholeStepValidR_backend_of_refOkBV

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.runsR_backend_of_refOkBV' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.CastsV.runsR_backend_of_refOkBV

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Casts.backwardG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Casts.backwardG

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Casts.castsFwdG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Casts.castsFwdG
