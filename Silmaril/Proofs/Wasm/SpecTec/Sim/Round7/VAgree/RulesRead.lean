module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.Defs

/-!
# Round 7, memory SIMD: the rules of `Step_read` that refer to `Step` or `Step_read`

Kernel computations (`decide +kernel`, kernel reduction, no native code) on the relation as the fixed wasm-3.0
script's environment finds it. Split from `Rules` in round 4 so that each module stays under the
time budget under parallel load.

No rule of `Step_read` refers to `Step` or `Step_read`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

set_option maxRecDepth 100000

theorem read_step : relRulesUsersK 0 "Step" "Step_read" = some [] := by decide +kernel
theorem read_read : relRulesUsersK 0 "Step_read" "Step_read" = some [] := by decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
