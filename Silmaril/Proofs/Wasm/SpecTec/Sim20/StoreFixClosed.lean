module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixTyped

/-!
# The corrected `Step` in `simEnv20T` is closed

`closedB_step20T` (kernel), `sstepB20T_iff`: `Step`, `Step_pure` and `Step_read` are closed in
`fixedT20`, so the backend reading of `Step` is the declarative one in `simEnv20T` (as
`StepFix.sstepB20S_iff` for `simEnv20S`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat pctV)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk DDerives otherwise Fires PremW SStep cfgV TypedV
  ValsOnly stateT dderives_iff_fires dderives_of_ruleAt evalExp_tup2 evalExp_case
  evalExp_cat evalExp_ne_nil evalExp_or prems_two)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB closedB Closed closed_of_closedB closed_congr
  dderivesB_otherwise_iff_of_closed)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S ctxtInstrsFix valsTy adminsTy valsE iterV)
open Silmaril.Wasm.SpecTec.Sim20.Whole (evalExp_subIterPat storeNumTrapRule)

set_option maxRecDepth 100000

variable (B : Builtins)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step`, `Step_pure` and `Step_read` are closed in `fixedT20`. -/
theorem closedB_step20T :
    closedB (envOfScript fixedT20) ["Step", "Step_pure", "Step_read"] = true := by
  decide +kernel

/-- The three reduction relations are closed in `simEnv20T B`. -/
theorem closed_step20T : Closed (simEnv20T B) (· ∈ ["Step", "Step_pure", "Step_read"]) :=
  closed_congr (fun _ => rfl) (closed_of_closedB closedB_step20T)

/-- **In `simEnv20T` the backend reading of `Step` is the declarative one.** -/
theorem sstepB20T_iff {c c' : Value} : SStepB (simEnv20T B) c c' ↔ SStep (simEnv20T B) c c' :=
  dderivesB_otherwise_iff_of_closed (closed_step20T B) (by simp)

end Silmaril.Wasm.SpecTec.Sim20.StoreFix
