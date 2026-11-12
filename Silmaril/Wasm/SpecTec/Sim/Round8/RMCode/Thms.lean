module

public import Silmaril.Wasm.SpecTec.Sim.Round8.RMCode.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.RMCode.Assemble

/-!
# Round 8, memory SIMD: `Step_read` and `Step` through the code-erased store (round 8, pass 2, rm)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round8.RMCode`; see `docs/projects/spectec/README.md`. Definitions (`codeVD`, `hostSFI`, `hostifyS`, `hostC`, `FiresEraseD`, `RestMSHCQ`,
`OpenRMRestDPQ`) are in `Round8/RMCode/Defs.lean`.

* `eraseC_configVD`: at memory-SIMD-free code, `eraseC (configVD hn c) = configV id (hostC hn c)`;
* `typed_hostC`, `noCastV_hostC`: the named host configuration is typed and keeps round 6's
  `NoCastV`;
* `step_setFS` (Core, unrefined): steps at the named host store, at the host with no outcome, move
  back to any function instances of the same types;
* `read_of_firesErase`, `step_of_firesErase`: the `Step_read` obligation and the `Step`
  obligation (rules from 6 on, other than 8, 9 and 22–25) of `RMHost.RestMSHCP` at
  memory-SIMD-free code, from `FiresEraseD` for the rule;
* `wholeStepValidRM_of_restDPQ`: `Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPQ`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMCode

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.RMCode.eraseC_configVD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseC_configVD

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.RMCode.step_setFS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_setFS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.RMCode.read_of_firesErase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_of_firesErase

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.RMCode.step_of_firesErase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_of_firesErase

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.RMCode.wholeStepValidRM_of_restDPQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPQ

end Silmaril.Wasm.SpecTec.Sim.Round8.RMCode
