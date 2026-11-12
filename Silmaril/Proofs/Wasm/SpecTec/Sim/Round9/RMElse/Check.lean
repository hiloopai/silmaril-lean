module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.Defs

/-!
# Round 9, rm: the kernel check on the 28 `otherwise` rules of `Step_read`

`elseAt_ok` (`decide +kernel`): every rule of `FiresC.elseRead` passes round 8's evaluator check,
has a top-level `otherwise` premise, and every other premise is a `FiresC.relPrem`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

set_option maxRecDepth 100000 in
/-- **The 28 `otherwise` rules of `Step_read` are `elseRuleC`.** -/
theorem elseAt_ok : elseAt "Step_read" Round8.FiresC.elseRead = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
