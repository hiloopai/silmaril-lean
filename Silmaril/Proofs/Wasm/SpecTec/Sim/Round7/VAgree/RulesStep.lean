module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.Defs

/-!
# Round 7, memory SIMD: the rules of `Step` that refer to `Step` or `Step_read`

Kernel computations (`decide +kernel`, kernel reduction, no native code) on the relation as the fixed wasm-3.0
script's environment finds it. Split from `Rules` in round 4 so that each module stays under the
time budget under parallel load.

Of `Step`, rule 1 refers to `Step_read` and rules 2–5 (the context rules) refer to `Step`
itself. No other rule of `Step` refers to either.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

set_option maxRecDepth 100000

theorem step_step : relRulesUsersK 0 "Step" "Step" = some [2, 3, 4, 5] := by decide +kernel
theorem step_read : relRulesUsersK 0 "Step_read" "Step" = some [1] := by decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
