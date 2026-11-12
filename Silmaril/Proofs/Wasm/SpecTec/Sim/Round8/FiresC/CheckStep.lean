module

public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Defs

/-!
# Round 8, firing across code erasure: the rules of `Step` from 6 on

Kernel computations (`decide +kernel`, kernel reduction, no native code): `Step` has 36 rules, and the rules
`relStep` (6 and 10–35) pass round 8's check, have no `otherwise` premise and consult only
`relG`. Rules 7–9 read `CODE` and fail the check.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

set_option maxRecDepth 100000

/-- **The rules `relStep` of `Step` move with `relG`.** -/
theorem relStep_ok : relAt "Step" relStep = true := by
  decide +kernel

/-- `Step` has 36 rules. -/
theorem step_length : (rulesOf "Step").length = 36 := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
