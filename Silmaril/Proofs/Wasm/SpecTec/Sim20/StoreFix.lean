module

public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs

/-!
# The `STORE` erratum applies

* `storeInstrErratum20_applies`, `storeAdminErratum20_applies` (kernel): each erratum applies
  (its target is declared once, and the corrected definition differs from the original);
  `applyErrata_store20`: applied in order to `StepFix.fixedS20`, they give `fixedT20`.
* Non-vacuity is in `StoreFixTyped`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)

/-! ## The errata apply -/

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **The `instr` erratum applies** to `fixedS20` (kernel). -/
theorem storeInstrErratum20_applies : storeInstrErratum20.applies StepFix.fixedS20 = true := by
  decide +kernel

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **The `admininstr` erratum applies** after it (kernel). -/
theorem storeAdminErratum20_applies :
    storeAdminErratum20.applies (replaceDefs instrFix20 StepFix.fixedS20) = true := by
  decide +kernel

set_option maxRecDepth 8000000 in
/-- Applying both gives `fixedT20`. -/
theorem applyErrata_store20 :
    applyErrata [storeInstrErratum20, storeAdminErratum20] StepFix.fixedS20 = some fixedT20 := by
  simp only [applyErrata_cons, applyErrata_nil, applyErratum, storeInstrErratum20_applies,
    ↓reduceIte, Option.bind_some]
  have h : storeInstrErratum20.corrected = instrFix20 := rfl
  simp only [h, storeAdminErratum20_applies, ↓reduceIte, Option.bind_some, applyErrata_nil]
  rfl

end Silmaril.Wasm.SpecTec.Sim20.StoreFix
