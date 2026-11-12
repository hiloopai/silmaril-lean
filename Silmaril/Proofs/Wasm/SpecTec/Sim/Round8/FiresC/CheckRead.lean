module

public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Defs

/-!
# Round 8, firing across code erasure: the rules of `Step_read` without `otherwise`

Kernel computations (`decide +kernel`, kernel reduction, no native code): `Step_read` has 103 rules, and the 75
rules `relRead` pass round 8's check, have no `otherwise` premise and consult only `relG`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

set_option maxRecDepth 100000

/-- **The rules `relRead` of `Step_read` move with `relG`.** -/
theorem relRead_ok : relAt "Step_read" relRead = true := by
  decide +kernel

/-- `Step_read` has 103 rules. -/
theorem stepRead_length : (rulesOf "Step_read").length = 103 := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
