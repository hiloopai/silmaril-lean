module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxRule.Defs

/-! # Round 7, REH route 2: the side conditions on the rules, slice 2 (kernel) -/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxRule

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- Slice 2 of `ruleAuxRels_fixed`: rules 14 to 20 of each relation. -/
theorem ruleAux02 :
    ruleAuxRelsAt (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) 14 7 = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxRule
