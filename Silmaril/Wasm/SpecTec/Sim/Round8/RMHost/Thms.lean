module

public import Silmaril.Wasm.SpecTec.Sim.Round8.RMHost.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.RMHost.Pure

/-!
# Round 8, memory SIMD: every `Step_pure` rule at memory-SIMD-free code (round 8, pass 1, rm)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round8.RMHost`; see `docs/projects/spectec/README.md`. Definitions (`hostFI`, `hostify`, `withFuncs`, `setF`, `RestMSHCP`, `OpenRMRestDPP`) are in
`Round8/RMHost/Defs.lean`.

* `step_setF` (Core, unrefined): a step at a store of host functions, at the host with no
  outcome, is a step with any function instances of the same types, at any host.
* `typed_hostify`: `TypedD` at memory-SIMD-free code gives `Typed` at the host store.
* `pure_hostify`: the `Step_pure` obligation of `NullHost.RestMSHC` for **every** rule at
  configurations whose code has no memory SIMD instruction, at every store and host. This
  extends round 7's 42-rule slice `MSRest.pure_val` to all 79 rules.
* `restMSHCR_of_P`, `wholeStepValidRM_of_restDPP`: `Round7.MemSimd.Task.wholeStepValidRM` from
  the narrower `OpenRMRestDPP`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMHost

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.RMHost.step_setF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_setF

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.RMHost.typed_hostify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed_hostify

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.RMHost.pure_hostify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pure_hostify

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.RMHost.wholeStepValidRM_of_restDPP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPP

end Silmaril.Wasm.SpecTec.Sim.Round8.RMHost
