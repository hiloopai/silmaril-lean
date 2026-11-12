module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs

/-!
# Round 9, `otherwise` rules: the kernel check of the pairs left

`elsePairs_fixed` (`decide +kernel`): in the fixed wasm-3.0 script, the pairs of `Step_read` left
by the head check are `elsePairs`, and no rule of `Step` has an `otherwise` premise.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The pairs left in the fixed script.** -/
theorem elsePairs_fixed : elsePairsIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed)
    elsePairs = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
