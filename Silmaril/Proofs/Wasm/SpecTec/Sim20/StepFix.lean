module

public import Silmaril.Wasm.SpecTec.Sim20.StepFix.Defs

/-!
# The 2.0 `Step` erratum applies

`stepErratum20_applies`: `stepErratum20` applies to `Scripts.Wasm20.fixed` (its target `Step` is
declared exactly once, the corrected definition declares it, and the patch changes it), checked
by the kernel; `applyErratum_step20` names the result `fixedS20`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StepFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **The erratum applies** to the fixed wasm-2.0 script (kernel `rfl`). -/
theorem stepErratum20_applies :
    stepErratum20.applies Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed = true := by
  decide +kernel

/-- Applying the erratum gives `fixedS20`. -/
theorem applyErratum_step20 :
    applyErratum stepErratum20 Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed = some fixedS20 := by
  simp only [applyErratum, stepErratum20_applies, ↓reduceIte]
  rfl

end Silmaril.Wasm.SpecTec.Sim20.StepFix
