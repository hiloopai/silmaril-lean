module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMPure.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMPure.Assemble

/-!
# Round 9, rm: `Step_pure` at memory SIMD code (round 9, pass 1, track rm)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.RMPure`; see `docs/projects/spectec/README.md`.

* `pure_struct`: the 15 `Step_pure` rules that are not flat (`if`, the label, handler and frame
  exits, `br` and `return` out of labels, handlers and frames, the trap rules) hold backward at
  `adminsToVD`, in every `simEnv B`, at every code, with no typing hypothesis. Round 6's leaves
  re-run at `adminsToVD` (`Raw/…/Round9/RMPure/`); the decoders at heads that are not
  `RMAtom.badHead` are round 6's, through `toV_of_atomD`.
* `restMSHCH_of_I`, `wholeStepValidRM_of_restDPI`: `Round7.MemSimd.Task.wholeStepValidRM` from
  `OpenRMRestDPI`, which has no `Step_pure` obligation left.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMPure

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMPure.pure_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pure_struct

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMPure.wholeStepValidRM_of_restDPI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPI

end Silmaril.Wasm.SpecTec.Sim.Round9.RMPure
