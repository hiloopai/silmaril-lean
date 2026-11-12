module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.Defs

/-! # Round 8, REH route 2: the clause check on the script, slice 19 (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 19 of `yItems_fixed`: top-level definitions 950 to 999. -/
theorem y19 : yItems ((fixed.drop 950).take 50) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
