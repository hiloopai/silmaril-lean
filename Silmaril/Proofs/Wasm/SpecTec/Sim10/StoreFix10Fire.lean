module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreFix10Closed

/-!
# The 1.0 `STORE` erratum: `store-num-trap` fires at `memStoreCfg10`

`Step` is closed in `fixedT10` (`closedB_step10T`, kernel), so the backend reading is the
declarative one (`sstepB10T_iff`); rule 7 (`store-num-trap`) fires at the images of
`memStoreCfg10` and its V1 successor (`fires10T_storeTrap`, by evaluation), so the corrected
script steps between them (`sstep10T_memStoreCfg`), at every builtins.
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

/-! ## The step -/

theorem hasRuleAt10T_storeNumTrap : HasRuleAt (simEnv10T B) "Step" "%~>%" 7 storeNumTrapRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The quantifiers of `store-num-trap` at the redex. -/
def σS10 : List (IL.Id × Value) :=
  [("z", stateV Empty.elim memStoreStore10 memStoreFrame10), ("i", pctV 0),
    ("t", valTypeV (.int .i32)), ("c", numV ⟨.int .i32, 0⟩), ("ao", memargV ⟨0, 0⟩)]

set_option maxHeartbeats 8000000 in
/-- **`Step/store-num-trap` fires in `simEnv10T`** at the configuration. -/
theorem fires10T_storeTrap :
    Fires (simEnv10T B) "Step" 7 (.tuple [configV Empty.elim memStoreCfg10,
      configV Empty.elim memStoreCfg10']) := by
  have hz : HasTyp (simEnv10T B) (VarEnv.empty.bindVals σS10) (.varT "state" [])
      (stateV Empty.elim memStoreStore10 memStoreFrame10) :=
    Sim20.StoreFix.typedV_of_empty (env := simEnv10T B) (x := "state")
      (v := stateV Empty.elim memStoreStore10 memStoreFrame10) ⟨300, by with_unfolding_all rfl⟩ _
      (Sim20.Pure.valsOnly_bindVals σS10)
  have hq : QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σS10)
      (match storeNumTrapRule10 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl hz
      (QuantsOk.cons rfl ⟨60, by with_unfolding_all rfl⟩
      (QuantsOk.cons rfl ⟨60, by with_unfolding_all rfl⟩
      (QuantsOk.cons rfl ⟨60, by with_unfolding_all rfl⟩
      (QuantsOk.cons rfl ⟨60, by with_unfolding_all rfl⟩ QuantsOk.nil))))
  refine Sim20.Pure.fires_of_ruleAt (hasRuleAt10T_storeNumTrap B) σS10 hq
    ⟨60, by with_unfolding_all rfl⟩ ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr ⟨60, by with_unfolding_all rfl⟩

/-- **The corrected 1.0 script steps between the images**, at every builtins. -/
theorem sstep10T_memStoreCfg :
    SStepB (simEnv10T B) (configV Empty.elim memStoreCfg10) (configV Empty.elim memStoreCfg10') := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt10T_storeNumTrap B
  exact (sstepB10T_iff B).2 ((dderives_iff_fires hrel).2 ⟨7, fires10T_storeTrap B⟩)

end Silmaril.Wasm.SpecTec.Sim10.StoreFix
