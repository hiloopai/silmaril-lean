module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.Thms

/-! # Round 7, REH route 2: side conditions on the signatures (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped (sigX tsigFixed)

set_option maxRecDepth 100000 in
/-- **The signatures pass `sigsAux`.** -/
theorem sigsAux_fixed : sigsAux sigX tsigFixed = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
