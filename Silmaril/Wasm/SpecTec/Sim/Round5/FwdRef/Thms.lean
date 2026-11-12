module

public import Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.FwdRef.Assemble

/-!
# SpecTec ↔ Core 3.0, round 5, pass 2, track fwdref: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef`; see `docs/projects/spectec/README.md`.

* `newDataNumB_builtins`: `Round5.Fwd.NewDataNumB` (`array.new_data-num`, forward)
  for the concrete `B`, through `tryClauses_concatn` (`$concatn_` on equal-length chunks).
* `storeV_junkStore`, `not_hostRespects_junkHost`: `storeV` is not injective, and the finite,
  `HostOk` host `junkHost` does not respect the encoding; so `Round5.Int.Open` fails for it
  (`not_open_junkHost`) and the hypothesis of `Round5.Int.wholeStepValidOk_of_open` is
  unsatisfiable (`not_open_all`).
* `hostRespectsT_of`, `hostRespectsT_of_storeInj`: the restatement `HostRespectsT` (at calls on
  typed store images) follows from `HostRespects`, and for every host from `StoreInjT`.
* `hostcall_typed`, `hostInv_typed`, `fwd_callRefHostT`, `fwd_callRefHostDivT`,
  `bwd_callRefHostT`, `bwd_callRefHostDivT`, `hostStepsV_of_T`: the host-call rules, forward and
  backward (`Bwd.HostStepsV`), from `HostRespectsT`.
* `oblT`, `forward_validT`: track fwd's obligations and forward conjunct with `HostRespectsT` and
  `newDataNumB_builtins`.
* `openT_of_open`, `partsOkR_of_openT`, `wholeStepValidOk_of_openT`: `Round5.Task.wholeStepValidOk`
  from `OpenT` (`Round5.Int.Open` with `HostRespectsT`, without `newDataNum`), which is no
  stronger than `Open`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.newDataNumB_builtins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round5.FwdRef.newDataNumB_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.tryClauses_concatn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef.tryClauses_concatn

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.storeV_junkStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef.storeV_junkStore

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.not_hostRespects_junkHost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef.not_hostRespects_junkHost

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.not_open_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef.not_open_all

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.hostRespectsT_of_storeInj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef.hostRespectsT_of_storeInj

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.hostStepsV_of_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef.hostStepsV_of_T

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.forward_validT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef.forward_validT

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.openT_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef.openT_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.partsOkR_of_openT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef.partsOkR_of_openT

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef.wholeStepValidOk_of_openT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.FwdRef.wholeStepValidOk_of_openT
