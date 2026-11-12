module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HPair.Defs

/-!
# Round 7, `BD`: the kernel fact behind `LhsNoPair`

`step_pairOk`: on `Step` as the fixed wasm-3.0 script's environment finds it, the `Step` and
`Step_read` premises of rules 1–5 have left-hand sides in `LFragP`, and every conclusion
alternative of rules 8 and 9 ends in `REF.FUNC_ADDR`, `CALL_REF` (`decide +kernel`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HPair

set_option maxRecDepth 100000

/-- **`stepPairOk` holds of `Step`.** -/
theorem step_pairOk : VElse.onRel "Step" stepPairOk = some true := by decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.HPair
