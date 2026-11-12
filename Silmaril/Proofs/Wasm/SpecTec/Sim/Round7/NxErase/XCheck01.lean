module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.Defs

/-! # Round 7, REH route 2: the side conditions of the erasure copy, slice 1 (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 1 of `xItems_fixed`: top-level definitions 50 to 99. -/
theorem x01 : xItems ((fixed.drop 50).take 50) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
