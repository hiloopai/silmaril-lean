module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant.Defs

/-! # Round 7, REH route 2: type side conditions, slice 0 (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped (sigX)

set_option maxRecDepth 100000 in
/-- Slice 0 of `typVtItems_fixed`. -/
theorem vt00 : typVtItems sigX ((fixed.drop 0).take 100) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant
