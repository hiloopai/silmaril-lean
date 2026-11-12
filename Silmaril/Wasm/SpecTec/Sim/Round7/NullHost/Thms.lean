module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NullHost.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NullHost.Rest

/-!
# Round 7, memory SIMD: `RestMSH` reduced to configurations holding memory SIMD code, at every
host (round 6, pass 2, proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NullHost`; see `docs/projects/spectec/README.md`. Definitions (`nullHost`, `RestMSHC`, `OpenRMRestDC`) are in `Round7/NullHost/Defs.lean`.

* `agreeOff_host`: round 6's primitives at two hosts agree off `$hostcall`.
* `restSH_noMemSimd`: **the per-rule backward obligations off memory SIMD and off `Step` 8 and
  9 hold at every memory-SIMD-free `NoCastVM` configuration, for every host**, with no condition
  on Core successors. They are read at `nullHost`, where Core steps add no memory SIMD code.
* `restMSH_iff_restMSHC`: `RMD.RestMSH` is `RestMSHC` (the obligations at configurations that
  hold memory SIMD code themselves), at every host. Round 7 had the analogous equivalence
  (`MSPres.restMS_iff_restMSC`) only for hosts that add no memory SIMD code.
* `wholeStepValidRM_of_restDC`: `Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDC`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NullHost

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NullHost.agreeOff_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms agreeOff_host

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NullHost.restSH_noMemSimd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms restSH_noMemSimd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NullHost.restMSH_iff_restMSHC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms restMSH_iff_restMSHC

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NullHost.wholeStepValidRM_of_restDC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDC

end Silmaril.Wasm.SpecTec.Sim.Round7.NullHost
