module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.Thms

/-! # Round 7, REH route 2: side conditions, slice 5 (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped (tsigFixed)

set_option maxRecDepth 100000 in
/-- Slice 5 of `auxItems_fixed`. -/
theorem aux05 : auxItems tsigFixed ((fixed.drop 500).take 100) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
