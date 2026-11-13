module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NopEx.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NopEx.Witness

/-!
# SpecTec ↔ Core 3.0, a run-domain witness with exports (proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NopEx`; see `docs/projects/spectec/README.md`, "re
". Definitions (`callFreeA`, `callFreeL`) are in `Round7/NopEx/Defs.lean`.

* `step_noHost_of_callFree` (unrefined): on call-free code a step for any host is a `noHost` step.
* `step_expNop_inv`: `expDoneCfg` is the only Core successor of `expNopCfg`, for every profile and
  host; `steps_expNop`: nothing else is reachable.
* `runDomDetE_expNopCfg`: `expNopCfg`, whose frame's module exports `"g"`
  (`exports_expNopCfg`), is in `Atlas.SpecTecR7Runs.RunDomDetE` for every profile and host.
* `backendE_step_expNopCfg`, `backendE_bwd_expNopCfg`, `backendE_step_expNopCfg_divHost`: its
  image steps in `Round7.backendE` to the image of a witness of `expDoneCfg`, and only there.
* `sat_iff_expNopCfg`: the round-7 run theorem at this point, at round 5's diverging host.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NopEx

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NopEx.step_noHost_of_callFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_noHost_of_callFree

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NopEx.step_expNop_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_expNop_inv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NopEx.runDomDetE_expNopCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runDomDetE_expNopCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NopEx.backendE_step_expNopCfg_divHost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms backendE_step_expNopCfg_divHost

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NopEx.backendE_bwd_expNopCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms backendE_bwd_expNopCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NopEx.sat_iff_expNopCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_expNopCfg

end Silmaril.Wasm.SpecTec.Sim.Round7.NopEx
