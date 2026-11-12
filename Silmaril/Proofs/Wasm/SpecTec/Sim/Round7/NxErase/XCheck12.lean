module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.Defs

/-! # Round 7, REH route 2: the side conditions of the erasure copy, slice 12 (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 12 of `xItems_fixed`: top-level definitions 600 to 649. -/
theorem x12 : xItems ((fixed.drop 600).take 50) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
