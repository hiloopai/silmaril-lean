module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef.Defs

/-!
# Round 9, RE: the kernel checks of the `Ref_ok` pairs

`refRel_fixed` (`decide +kernel`): in the fixed wasm-3.0 script every rule of `Ref_ok` passes
`refRule`. `refPairs_fixed`: at the four `Ref_ok` pairs the `otherwise` rule has `lhsRuleSF` and
the earlier rule passes `refRuleJ`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **`Ref_ok` in the fixed script reads backward across erasure of its store.** -/
theorem refRel_fixed : refRelIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The `Ref_ok` pairs of the fixed script.** -/
theorem refPairs_fixed : refPairsIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) =
    true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef
