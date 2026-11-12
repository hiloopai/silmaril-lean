module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs

/-!
# Round 9, `otherwise` rules: the kernel check of the chain pairs

`chainPairs_fixed` (`decide +kernel`): in the fixed wasm-3.0 script, at every pair of `chainPairs`
the `otherwise` rule has `lhsRule` and the earlier rule passes `simpleRuleE`; `chain2Pairs_fixed`, the same at `chain2Pairs`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The chain pairs of the fixed script.** -/
theorem chainPairs_fixed : chainPairsIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The chain pairs of the second level in the fixed script.** -/
theorem chain2Pairs_fixed : chain2PairsIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) =
    true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
