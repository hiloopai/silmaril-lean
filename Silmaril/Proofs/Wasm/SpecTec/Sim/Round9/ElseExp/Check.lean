module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.Defs

/-!
# Round 9, RE: the kernel check of the `Expand` pairs

`expPairs_fixed` (`decide +kernel`): in the fixed wasm-3.0 script, at the four `Expand` pairs the
`otherwise` rule has `ElseBwd.lhsRule` and the earlier rule passes `simpleRuleR`, and rule 100
(`array.init_data-oob2`) has no `otherwise` premise; `innerPairs_fixed`, the same, at `(21, 9)`, for `innerDiffer`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The `Expand` pairs of the fixed script.** -/
theorem expPairs_fixed : expPairsIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The pair with nested instructions in the fixed script.** -/
theorem innerPairs_fixed : innerPairsIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) =
    true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp
