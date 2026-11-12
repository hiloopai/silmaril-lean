module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixLift

/-!
# The `STORE` erratum, non-vacuously: a storing configuration with a store below the top

`StoreFixNeed` shows that `simEnv20S` has no step from a state whose store has a storing
function. This module sets up a configuration of that kind on which `simEnv20T` does step
(`StoreFixFire`):

* `memStoreCfg`: a store holding the storing function of `storeFnCfg` and one empty memory, a
  frame whose module has that memory, and code `i32.const 0; i32.const 0; i32.store; nop`;
* `step_memStoreCfg`: V2 steps it to `trap; nop` (`storeIntTrap` under `Step.ctxtInstrs`);
* `stuck_memStoreCfg`: in `simEnv20S` its image has no step (`stuck_storeFn20S`);
* `typedV_zM`, `typedV_redexM`, `typedV_trapM`, `typedV_nopM`: its state and code are typed in
  `simEnv20T` (by evaluation).

This is one instance; the general forward store rules in `simEnv20T` need the `hasTyp`
agreement theorem described in `StoreFixTyped`.
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

/-! ## The configuration -/

/-- The storing function of `storeFnStore`, and one empty memory. -/
def memStoreStore : Store Empty :=
  { funcs := (storeFnStore (H := Empty)).funcs, mems := [⟨⟨⟨0, none⟩⟩, ByteArray.empty⟩] }

/-- A frame whose module has memory `0`. -/
def memFrame : Frame := { module := { mems := [0] } }

/-- `i32.store` at `memarg 0 0`. -/
abbrev i32Store0 : V2.Instr := .intStore .i32 none ⟨0, 0⟩

/-- **The configuration**: `i32.const 0; i32.const 0; i32.store; nop`. -/
def memStoreCfg : Config Empty :=
  ⟨memStoreStore, memFrame, [constI32 0, .plain (.intConst .i32 0), .plain i32Store0, .plain .nop]⟩

/-- Its successor: `trap; nop`. -/
def memStoreCfg' : Config Empty := ⟨memStoreStore, memFrame, [.trap, .plain .nop]⟩

theorem storeFn_memStoreStore : StoreFn20 memStoreStore :=
  ⟨0, _, _, _, rfl, rfl, List.mem_singleton_self _, .int .i32 none ⟨0, 0⟩⟩

/-- **V2 steps it**: the store traps (the memory is empty), under `ctxt-instrs`. -/
theorem step_memStoreCfg (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Empty) :
    Step P host memStoreCfg memStoreCfg' := by
  have h : Step P host ⟨memStoreStore, memFrame, [constI32 0, .plain (.intConst .i32 0),
      .plain i32Store0]⟩ ⟨memStoreStore, memFrame, [.trap]⟩ :=
    .storeIntTrap (a := 0) rfl rfl (by decide)
  have h₂ := Step.ctxtInstrs (vs := []) (rest := [.plain .nop]) h (Or.inr (by simp))
  simpa [vals, memStoreCfg, memStoreCfg'] using h₂

/-- **The original corrected script is stuck there.** -/
theorem stuck_memStoreCfg (w : Value) :
    ¬ SStepB (simEnv20S B) (configV Empty.elim memStoreCfg) w :=
  stuck_configV_storeFn20S (c := memStoreCfg) storeFn_memStoreStore w

/-! ## The step in `simEnv20T` -/

/-- The state. -/
abbrev zM : Value := stateV Empty.elim memStoreStore memFrame

/-- The inner redex `CONST I32 0; CONST I32 0; STORE I32 ε {0 0}`. -/
abbrev redexM : List Value :=
  adminsToV [constI32 0, .plain (.intConst .i32 0), .plain i32Store0]

set_option maxHeartbeats 8000000 in
/-- The storing state is typed in `simEnv20T`. -/
theorem typedV_zM : TypedV (simEnv20T B) stateT zM :=
  typedV_of_empty ⟨300, by with_unfolding_all rfl⟩

set_option maxHeartbeats 8000000 in
/-- The redex, the trap and the suffix are typed `admininstr*`. -/
theorem typedV_redexM : TypedV (simEnv20T B) adminsTy (.list redexM) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  simp only [redexM, adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact typedV_of_empty ⟨300, by with_unfolding_all rfl⟩
  · exact typedV_of_empty ⟨300, by with_unfolding_all rfl⟩
  · exact typedV_i32Store20T B

set_option maxHeartbeats 8000000 in
theorem typedV_trapM : TypedV (simEnv20T B) adminsTy (.list (adminsToV [.trap])) :=
  Sim.typedV_list_iff.2 fun u hu => by
    simp only [adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
    exact hu ▸ typedV_of_empty ⟨300, by with_unfolding_all rfl⟩

set_option maxHeartbeats 8000000 in
theorem typedV_nopM : TypedV (simEnv20T B) adminsTy (.list (adminsToV [.plain .nop])) :=
  Sim.typedV_list_iff.2 fun u hu => by
    simp only [adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
    exact hu ▸ typedV_of_empty ⟨300, by with_unfolding_all rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.StoreFix
