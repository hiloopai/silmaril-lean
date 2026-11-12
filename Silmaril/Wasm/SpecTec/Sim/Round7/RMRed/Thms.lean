module

public import Silmaril.Wasm.SpecTec.Sim.Round7.RMRed.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.RMRed.Assemble

/-!
# Round 7, `BD`: the reduction of `Task.wholeStepValidRM` with the proved pieces removed (round 6,
pass 3, proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.RMRed`; see `docs/projects/spectec/README.md`. Definitions (`Easy`, `OpenRMRestDR`) are in `Round7/RMRed/Defs.lean`.

* `openRMRestDC_of_R`: `OpenRMRestDR` gives `NullHost.OpenRMRestDC` at spec profiles, injective
  encodings and finite `HostOk` hosts.
* `wholeStepValidRM_of_restDR`: **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDR`**:
  `RestMSHC`, `forward` off `Easy` sources and off host calls under contexts, and `castsFwd`,
  `castsBwd` off `Easy` sources.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.RMRed

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.RMRed.openRMRestDC_of_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms openRMRestDC_of_R

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.RMRed.wholeStepValidRM_of_restDR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wholeStepValidRM_of_restDR

end Silmaril.Wasm.SpecTec.Sim.Round7.RMRed
