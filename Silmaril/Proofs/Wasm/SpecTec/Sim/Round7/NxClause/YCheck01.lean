module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.Defs

/-! # Round 8, REH route 2: the clause check on the script, slice 1 (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 1 of `yItems_fixed`: top-level definitions 50 to 99. -/
theorem y01 : yItems ((fixed.drop 50).take 50) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
