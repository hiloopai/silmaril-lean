module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.RulesRead
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.RulesStep

/-!
# Round 7, memory SIMD: the rules of `Step_pure`, `Step_read` and `Step` that refer to `Step`

Kernel computations (`decide +kernel`, kernel reduction, no native code) on the relations as the fixed
wasm-3.0 script's environment finds them:

* no rule of `Step_pure` or `Step_read` refers to `Step` or `Step_read`;
* of `Step`, rule 1 refers to `Step_read` and rules 2–5 (the context rules) refer to `Step`
  itself. No other rule of `Step` refers to either.

The `Step_read` and `Step` facts are in `RulesRead` and `RulesStep` (split in round 4 so that
each module stays under the time budget under parallel load).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

set_option maxRecDepth 100000

theorem pure_step : relRulesUsersK 0 "Step" "Step_pure" = some [] := by decide +kernel
theorem pure_read : relRulesUsersK 0 "Step_read" "Step_pure" = some [] := by decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
