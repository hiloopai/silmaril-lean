module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.Defs

/-! # Round 8, REH route 2: the clause check on the script, slice 0 (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 0 of `yItems_fixed`: top-level definitions 0 to 49. -/
theorem y00 : yItems ((fixed.drop 0).take 50) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
