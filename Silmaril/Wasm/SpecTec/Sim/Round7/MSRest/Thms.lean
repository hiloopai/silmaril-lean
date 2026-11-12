module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MSRest.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSRest.Pure

/-!
# Round 7, memory SIMD: a proved slice of `RestMSHC` (round 7, pass 2, track rm)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.MSRest`; see `docs/projects/spectec/README.md`. Definitions (`pureVal`, `RestMSHCR`, `OpenRMRestDPR`) are in `Round7/MSRest/Defs.lean`.

* `pure_val`: the `Step_pure` obligation of `NullHost.RestMSHC` for the 42 value-level rules
  (`pureVal`) at configurations whose memory SIMD code is only in the store, at every host.
* `restMSHC_of_R`: `RestMSHCR` (the rest) gives `RestMSHC`.
* `wholeStepValidRM_of_restDPR`: `Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPR`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSRest

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSRest.pure_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pure_val

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MSRest.wholeStepValidRM_of_restDPR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPR

end Silmaril.Wasm.SpecTec.Sim.Round7.MSRest
