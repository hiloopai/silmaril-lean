module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreFix10Step

/-!
# `Step` is closed in the 1.0 script with the `STORE` erratum

`closedB_step10T` (kernel): `Step`, `Step_pure` and `Step_read` are closed in `fixedT10`, so in
`simEnv10T` the backend reading of `Step` is the declarative one (`sstepB10T_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk Fires SStep TypedV dderives_iff_fires)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB closedB Closed closed_of_closedB closed_congr
  dderivesB_otherwise_iff_of_closed)
open Silmaril.Wasm.SpecTec.Sim10.Whole (storeNumTrapRule10 not_typed_store3 typedV_code_of_typed10)

set_option maxRecDepth 100000

variable (B : Builtins)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step`, `Step_pure` and `Step_read` are closed in `fixedT10`. -/
theorem closedB_step10T :
    closedB (envOfScript fixedT10) ["Step", "Step_pure", "Step_read"] = true := by
  decide +kernel

/-- The three reduction relations are closed in `simEnv10T B`. -/
theorem closed_step10T : Closed (simEnv10T B) (· ∈ ["Step", "Step_pure", "Step_read"]) :=
  closed_congr (fun _ => rfl) (closed_of_closedB closedB_step10T)

/-- **In `simEnv10T` the backend reading of `Step` is the declarative one.** -/
theorem sstepB10T_iff {c c' : Value} : SStepB (simEnv10T B) c c' ↔ SStep (simEnv10T B) c c' :=
  dderivesB_otherwise_iff_of_closed (closed_step10T B) (by simp)

end Silmaril.Wasm.SpecTec.Sim10.StoreFix
