module

public import Silmaril.Wasm.SpecTec.Sim.Round7.BMHost.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.BMHost.Refute

/-!
# Round 7, memory SIMD: round 7's reductions at `BM` fail at a host call that returns memory SIMD
code (round 6, pass 2, proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.BMHost`; see `docs/projects/spectec/README.md`. Definitions (`msAddHost`, `addMS`, `msFnAt`, `ForwardBM`) are in `Round7/BMHost/Defs.lean`.

* `msAddHost_finite`, `msAddHost_ok`: **a finite, `HostOk` host whose every call appends a memory
  and a valid function with memory SIMD code** (`unreachable; v128.store`), and returns `trap`.
* `step_msSrc_inv`, `boundedSelM_srcCfg`, `boundedSelM_msDst`, `not_castRedex_srcCfg`: at round
  5's `srcCfg` (`ref.func 0; call_ref dt0`, no memory SIMD code), Core's only successor is
  `msDst`, and both are in `BoundedSelM`. `step_callRef_inv` is the Core inversion at
  `ref.func a; call_ref d` for any host function `a`.
* `bm_step_srcCfg`: every step at `BM` from `configVD srcCfg` reaches a `configV` image (the step
  moves to `BI` off memory SIMD atoms, then round 6's `backwardNC`).
* **`not_forwardBM`**: `ForwardBM hnU (Profile.spec nd r) msAddHost` is false. The image of
  `msDst` has the store `storeVD (addMS store0)`, which is no `storeV` image.
* `not_openRMRest`, `not_openRM`, `not_openRMRestMS`, **`not_openRMRest_all`**,
  **`not_openRMRestMS_all`**: round 7's reductions at `BM` (`MemSimd.wholeStepValidRM_of_rest`,
  `wholeStepValidRM_of_open`, `VInv.wholeStepValidRM_of_restMS`) have unsatisfiable hypotheses.
* `not_forwardBM_backend`: the forward half of `Round7.Task.wholeStepValidRM` fails at the witness
  `B := BM`. The target (`∃ B`) is not refuted; `RMD.wholeStepValidRM_of_restD` uses `HostD.BD`.
* `bd_step_srcCfg`: at `BD` the same Core step is simulated (`HostRulesD.fwd_callRefHostD`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.BMHost

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.BMHost.msAddHost_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms msAddHost_ok

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.BMHost.step_msSrc_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_msSrc_inv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.BMHost.not_forwardBM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_forwardBM

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.BMHost.not_openRMRest_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_openRMRest_all

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.BMHost.not_openRMRestMS_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_openRMRestMS_all

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.BMHost.not_forwardBM_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_forwardBM_backend

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.BMHost.bd_step_srcCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bd_step_srcCfg

end Silmaril.Wasm.SpecTec.Sim.Round7.BMHost
