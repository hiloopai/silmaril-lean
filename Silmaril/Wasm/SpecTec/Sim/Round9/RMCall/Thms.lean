module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMCall.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMCall.Assemble

/-!
# Round 9, rm: `Step` rule 7 at `configVD` (round 9, pass 1, track rm)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.RMCall`; see `docs/projects/spectec/README.md`.

* `bwd_callRefFuncD`: **`Step` rule 7 (`call_ref-func`) backward at `configVD`**, in every
  `simEnv B` with `Bwd.CallInv`, at every configuration (memory SIMD code in the active code or in
  the store's function bodies included), with no typing hypothesis; `bwd_callRefFuncD_builtins` at
  `Prims.builtins P hn host`.
* `restMSHCF_of_G`, `openRMRestDPF_of_G`, `wholeStepValidRM_of_restDPG`:
  `Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPG`, which no longer asks for rule 7.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMCall

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMCall.bwd_callRefFuncD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bwd_callRefFuncD

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMCall.bwd_callRefFuncD_builtins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms bwd_callRefFuncD_builtins

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.RMCall.wholeStepValidRM_of_restDPG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDPG

end Silmaril.Wasm.SpecTec.Sim.Round9.RMCall
