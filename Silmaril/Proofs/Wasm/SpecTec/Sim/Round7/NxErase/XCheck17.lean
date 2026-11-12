module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.Defs

/-! # Round 7, REH route 2: the side conditions of the erasure copy, slice 17 (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 17 of `xItems_fixed`: top-level definitions 850 to 899. -/
theorem x17 : xItems ((fixed.drop 850).take 50) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
