module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VInv.Defs

/-!
# Round 7, memory SIMD: the left-hand sides of the context rules (kernel check)

`ctx_lhsOk`: in `Step` rules 1–5 of the fixed wasm-3.0 script, every conclusion alternative has a
left-hand side in the fragment `LFrag msAtoms`, and every `Step`/`Step_read` premise has a fragment
left-hand side whose variables are among the conclusion's. A kernel computation
(`decide +kernel`, kernel reduction, no native code).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VInv

set_option maxRecDepth 100000

/-- **The context rules' left-hand sides are in the fragment, on the conclusion's variables.** -/
theorem ctx_lhsOk : VElse.onRel "Step" (ctxLhsOk msAtoms) = some true := by decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.VInv
