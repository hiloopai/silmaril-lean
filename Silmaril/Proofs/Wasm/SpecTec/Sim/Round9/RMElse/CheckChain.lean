module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.Defs

/-!
# Round 9, rm: the kernel check on the chain pairs

`chainPairsC_fixed` (`decide +kernel`): at every pair of `chainPairsC` and `chain2PairsC` the
`otherwise` rule has a left-hand side `lhsRuleC` and the earlier rule is `simpleRuleCE`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

open Round8.FiresC (rulesOf)

set_option maxRecDepth 100000 in
theorem chainPairsC_fixed :
    pairsOk simpleRuleCE (rulesOf "Step_read") (chainPairsC ++ chain2PairsC) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
