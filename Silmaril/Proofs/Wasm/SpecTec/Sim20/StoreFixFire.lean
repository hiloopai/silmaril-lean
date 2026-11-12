module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixStep
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixClosed

/-!
# The `STORE` erratum, non-vacuously: the step

* `fires_storeTrapM`: `Step/store-num-trap` (rule 12 of the corrected `Step`) fires in
  `simEnv20T` on the redex `CONST I32 0; CONST I32 0; STORE I32 ε {0 0}` of `memStoreCfg`, from
  its storing state (whose memory is empty, so the store traps);
* **`sstepT_memStoreCfg`**: `Step/ctxt-instrs` lifts it over the suffix `NOP`, so the
  corrected script with the `STORE` erratum steps between the images of `memStoreCfg` and of
  its V2 successor (`step_memStoreCfg`), at every builtins. In `simEnv20S` the image of
  `memStoreCfg` has no step (`stuck_memStoreCfg`).
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

variable {B}

/-! ## The step -/

/-- The quantifiers of `store-num-trap` at the inner redex. -/
def σM : List (IL.Id × Value) :=
  [("z", zM), ("i", pctV 0), ("nt", numTypeV (.int .i32)), ("c", numV ⟨.int .i32, 0⟩),
    ("ao", memargV ⟨0, 0⟩)]

set_option maxHeartbeats 8000000 in
/-- **`Step/store-num-trap` fires in `simEnv20T`** on the redex, from the storing state. -/
theorem fires_storeTrapM :
    Fires (simEnv20T B) "Step" 12 (.tuple [cfgV zM redexM, cfgV zM (adminsToV [.trap])]) := by
  have hq : QuantsOk (simEnv20T B) (VarEnv.empty.bindVals σM)
      (match storeNumTrapRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (typedV_zM _ (Pure.valsOnly_bindVals σM))
      (QuantsOk.cons rfl ⟨60, by with_unfolding_all rfl⟩
      (QuantsOk.cons rfl ⟨60, by with_unfolding_all rfl⟩
      (QuantsOk.cons rfl ⟨60, by with_unfolding_all rfl⟩
      (QuantsOk.cons rfl ⟨60, by with_unfolding_all rfl⟩ QuantsOk.nil))))
  refine Pure.fires_of_ruleAt (hasRuleAt_storeNumTrapT B) σM hq ⟨60, by with_unfolding_all rfl⟩ ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr ⟨60, by with_unfolding_all rfl⟩


/-- **The store step below the top, in the corrected script with the `STORE` erratum**, at every
builtins: the images of `memStoreCfg` and of its V2 successor `memStoreCfg'`. -/
theorem sstepT_memStoreCfg :
    SStepB (simEnv20T B) (configV Empty.elim memStoreCfg) (configV Empty.elim memStoreCfg') := by
  have hin : SStep (simEnv20T B) (cfgV zM redexM) (cfgV zM (adminsToV [.trap])) := by
    obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_ctxtInstrsFixT B
    exact (dderives_iff_fires hrel).2 ⟨12, fires_storeTrapM⟩
  have hvs : TypedV (simEnv20T B) valsTy (.list []) := Sim.typedV_list_iff.2 (by simp)
  have h := sstepT_ctxtInstrs (vs := []) (rest := adminsToV [.plain .nop]) typedV_zM typedV_zM hvs
    typedV_redexM typedV_trapM typedV_nopM (Or.inr (by simp [adminsToV])) hin
  exact (sstepB20T_iff B).2 h

end Silmaril.Wasm.SpecTec.Sim20.StoreFix
