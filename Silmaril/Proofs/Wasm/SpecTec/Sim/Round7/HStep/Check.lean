module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HStep.Defs

/-!
# Round 7, `BD`: the context rules and rules 8, 9 and 23 of `Step` (kernel checks)

Kernel computations (`decide +kernel`, kernel reduction, no native code) on `Step` as the fixed wasm-3.0
script's environment finds it:

* `step_ctxOkH`: the premises of rules 1–5 are `HAgree.RG` or `RG` calls of `Step`/`Step_read`;
  rule 23 ends in `VSTORE` and rules 8 and 9 in `CALL_REF` on every conclusion alternative;
* `ctx_lhsOkH`: the context rules' left-hand sides are in `VInv.LFrag hAtoms`, on the
  conclusion's variables (`VInv.ctx_lhsOk` with `CALL_REF` excluded too).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HStep

set_option maxRecDepth 100000

/-- **`stepCtxOkH` holds of `Step`.** -/
theorem step_ctxOkH : VElse.onRel "Step" stepCtxOkH = some true := by decide +kernel

/-- **The context rules' left-hand sides are in `LFrag hAtoms`.** -/
theorem ctx_lhsOkH : VElse.onRel "Step" (VInv.ctxLhsOk hAtoms) = some true := by decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.HStep
