module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.Defs

/-! # Round 7, REH route 2: the side conditions of the erasure copy, slice 19 (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 19 of `xItems_fixed`: top-level definitions 950 to 999. -/
theorem x19 : xItems ((fixed.drop 950).take 50) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
