module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreFix10Cfg
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.MemTrap

/-!
# The 1.0 `STORE` erratum, non-vacuously: a store step

`memStoreCfg10` is `i32.const 0; i32.const 0; i32.store` over one empty memory. V1 traps there
(`step_memStoreCfg10`).

* In the original script its image is not typed (`not_typed10_memStoreCfg`, from
  `not_typed_store3`), so the forward theorems say nothing about it.
* In `simEnv10T` both images are typed (`typed10T_memStoreCfg`, `typed10T_memStoreCfg'`, kernel
  evaluation), `Step` is closed (`closedB_step10T`), and the script steps between the images
  (`sstep10T_memStoreCfg`, rule 7 `store-num-trap`, by evaluation), at every builtins.

This is one instance, checked by evaluation. The general forward store rules in `simEnv10T` need
the type-table agreement described in `StoreFix10`.
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

/-! ## The configuration -/

/-- One empty memory. -/
def memStoreStore10 : Store Empty := { memories := [⟨ByteArray.empty, none⟩] }

/-- A frame whose module's memory 0 is that memory. -/
def memStoreFrame10 : Frame := { module := { memories := [⟨0⟩] } }

/-- **The configuration**: `i32.const 0; i32.const 0; i32.store`. -/
def memStoreCfg10 : Config Empty :=
  ⟨memStoreStore10, memStoreFrame10, [value (.int .i32 0), value (.int .i32 0),
    .source (.intStore .i32 none ⟨0, 0⟩)]⟩

/-- Its successor: `trap`. -/
def memStoreCfg10' : Config Empty := ⟨memStoreStore10, memStoreFrame10, [.trap]⟩

/-- **V1 steps it**: the store traps, the memory being empty. -/
theorem step_memStoreCfg10 (host : HostSemantics Empty) : Step host memStoreCfg10 memStoreCfg10' :=
  .intStoreTrap _ _ _ _ _ _ _ ⟨0⟩ ⟨ByteArray.empty, none⟩ rfl (by decide)

/-- **In the original script its image is not typed**, at every builtins. -/
theorem not_typed10_memStoreCfg : ¬ Typed10 (simEnv10 B) Empty.elim memStoreCfg10 :=
  fun h => not_typed_store3 ⟨_, rfl⟩ (typedV_code_of_typed10 h)

set_option maxHeartbeats 8000000 in
/-- **Its image is typed in `simEnv10T`.** -/
theorem typed10T_memStoreCfg : Typed10 (simEnv10T B) Empty.elim memStoreCfg10 :=
  ⟨300, by with_unfolding_all rfl⟩

set_option maxHeartbeats 8000000 in
/-- So is its successor's. -/
theorem typed10T_memStoreCfg' : Typed10 (simEnv10T B) Empty.elim memStoreCfg10' :=
  ⟨300, by with_unfolding_all rfl⟩

end Silmaril.Wasm.SpecTec.Sim10.StoreFix
