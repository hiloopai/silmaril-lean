module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkWit

/-!
# Witnesses: `table.copy`, `table.init`, `elem.drop` and `data.drop` steps inside `Good20B`

Over `segStore`, one table of one null `funcref` and one element segment `[ref.null funcref]`:

* `tcopyCfg`: `i32.const 0; i32.const 0; i32.const 1; table.copy 0 0`. V2 steps by
  `table.copy-le` to code with `table.get 0; table.set 0` (`step_tcopyCfg`);
* `tinitCfg`: `i32.const 0; i32.const 0; i32.const 1; table.init 0 0`. V2 steps by
  `table.init-succ` to code with `ref.null funcref; table.set 0` (`step_tinitCfg`);
* `edropCfg`: `elem.drop 0`, which empties the segment (`step_edropCfg`).

Over round 6's `initStore`, `ddropCfg`: `data.drop 0`, which empties the data segment.

Each configuration is `Good20B` and not `Good20F`, and its V2 step is a step of `simEnv20T`
(`sstep_tcopyCfg`, `sstep_tinitCfg`, `sstep_edropCfg`, `sstep_ddropCfg`). Their typing is
checked by evaluation at every profile.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Plain20 storeB typed20_iff)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (eDA)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (Good20F eraseS)

set_option maxRecDepth 100000

/-! ## The store -/

/-- An element segment of one null `funcref`. -/
def oneElem : ElemInst := ⟨.funcref, [.null .funcref]⟩

/-- One table of one null `funcref` and one element segment of one null `funcref`. -/
def segStore : Store Empty := { tables := [oneTable], elems := [oneElem] }

/-- A frame whose module has table 0 and element segment 0. -/
def segFrame : Frame := { module := { tables := [0], elems := [0] } }

theorem storeSmall_segStore : StoreSmall segStore := by
  refine ⟨fun mi hmi => by simp [segStore] at hmi, fun di hdi => by simp [segStore] at hdi,
    fun ti hti => ?_, fun ei hei => ?_⟩
  · simp only [segStore, List.mem_singleton] at hti
    subst hti
    decide
  · simp only [segStore, List.mem_singleton] at hei
    subst hei
    decide

/-! ## `table.copy` -/

/-- `i32.const 0; i32.const 0; i32.const 1; table.copy 0 0`. -/
def tcopyCodeW : List Admin := [constI32 0, constI32 0, constI32 1, .plain (.tableCopy ⟨0⟩ ⟨0⟩)]

def tcopyCfg : Config Empty := ⟨segStore, segFrame, tcopyCodeW⟩

def tcopyCfg' : Config Empty := ⟨segStore, segFrame,
  [constI32 0, constI32 0, .plain (.tableGet ⟨0⟩), .plain (.tableSet ⟨0⟩), constI32 (0 + 1),
    constI32 (0 + 1), constI32 (1 - 1), .plain (.tableCopy ⟨0⟩ ⟨0⟩)]⟩

/-- **V2 copies the entry**: `table.copy-le`. -/
theorem step_tcopyCfg (P : Profile) (host : HostSemantics Empty) :
    Step P host tcopyCfg tcopyCfg' :=
  TableCopyFwd.step (.le (tx := oneTable) (ty := oneTable) rfl rfl (by decide) (by decide)
    (by decide))

set_option maxHeartbeats 4000000 in
theorem good20B_tcopyCfg (P : Profile) : Good20B Empty.elim P tcopyCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨eraseS segStore, segFrame, tcopyCodeW.map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  plain := Plain20.plain (s := segStore) (f := segFrame)
    [.num ⟨.int .i32, 0⟩, .num ⟨.int .i32, 0⟩, .num ⟨.int .i32, 1⟩] (.tableCopy ⟨0⟩ ⟨0⟩) [] rfl
  ok := by decide
  store := fun a fi h => by simp [tcopyCfg, segStore, Store.funcInst?] at h
  small := storeSmall_segStore

theorem not_good20F_tcopyCfg (P : Profile) : ¬ Good20F Empty.elim P tcopyCfg := by
  intro h
  have := h.ok
  revert this
  decide

/-- **`table.copy-le` is a step of the script with the `STORE` erratum**, from a configuration
outside `Good20F`; the next configuration, with `table.get` and `table.set`, is `Good20B`. -/
theorem sstep_tcopyCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim tcopyCfg) (configV Empty.elim tcopyCfg') ∧
      Good20B Empty.elim P tcopyCfg' :=
  ⟨(fwd_good20B (good20B_tcopyCfg P) (step_tcopyCfg P fun _ _ _ _ => False)).2,
    (fwd_good20B (good20B_tcopyCfg P) (step_tcopyCfg P fun _ _ _ _ => False)).1⟩

/-! ## `table.init` -/

/-- `i32.const 0; i32.const 0; i32.const 1; table.init 0 0`. -/
def tinitCodeW : List Admin := [constI32 0, constI32 0, constI32 1, .plain (.tableInit ⟨0⟩ ⟨0⟩)]

def tinitCfg : Config Empty := ⟨segStore, segFrame, tinitCodeW⟩

def tinitCfg' : Config Empty := ⟨segStore, segFrame,
  [constI32 0, aref (.null .funcref), .plain (.tableSet ⟨0⟩), constI32 (0 + 1), constI32 (0 + 1),
    constI32 (1 - 1), .plain (.tableInit ⟨0⟩ ⟨0⟩)]⟩

/-- **V2 copies the segment's entry**: `table.init-succ`. -/
theorem step_tinitCfg (P : Profile) (host : HostSemantics Empty) :
    Step P host tinitCfg tinitCfg' :=
  TableInitFwd.step (.succ (ti := oneTable) (ei := oneElem) rfl rfl (by decide) (by decide) rfl)

set_option maxHeartbeats 4000000 in
theorem good20B_tinitCfg (P : Profile) : Good20B Empty.elim P tinitCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨eraseS segStore, segFrame, tinitCodeW.map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  plain := Plain20.plain (s := segStore) (f := segFrame)
    [.num ⟨.int .i32, 0⟩, .num ⟨.int .i32, 0⟩, .num ⟨.int .i32, 1⟩] (.tableInit ⟨0⟩ ⟨0⟩) [] rfl
  ok := by decide
  store := fun a fi h => by simp [tinitCfg, segStore, Store.funcInst?] at h
  small := storeSmall_segStore

theorem not_good20F_tinitCfg (P : Profile) : ¬ Good20F Empty.elim P tinitCfg := by
  intro h
  have := h.ok
  revert this
  decide

/-- **`table.init-succ` is a step of the script with the `STORE` erratum**, from a
configuration outside `Good20F`; the next configuration is `Good20B`. -/
theorem sstep_tinitCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim tinitCfg) (configV Empty.elim tinitCfg') ∧
      Good20B Empty.elim P tinitCfg' :=
  ⟨(fwd_good20B (good20B_tinitCfg P) (step_tinitCfg P fun _ _ _ _ => False)).2,
    (fwd_good20B (good20B_tinitCfg P) (step_tinitCfg P fun _ _ _ _ => False)).1⟩

/-! ## `elem.drop` and `data.drop` -/

def edropCfg : Config Empty := ⟨segStore, segFrame, [.plain (.elemDrop ⟨0⟩)]⟩

def edropCfg' : Config Empty := ⟨segStore.setElemInst 0 { oneElem with refs := [] }, segFrame, []⟩

/-- **V2 drops the element segment.** -/
theorem step_edropCfg (P : Profile) (host : HostSemantics Empty) :
    Step P host edropCfg edropCfg' :=
  DropFwd.step (.elem (ei := oneElem) rfl rfl)

set_option maxHeartbeats 4000000 in
theorem good20B_edropCfg (P : Profile) : Good20B Empty.elim P edropCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨eraseS segStore, segFrame, [Admin.plain (.elemDrop ⟨0⟩)].map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  plain := Plain20.plain (s := segStore) (f := segFrame) [] (.elemDrop ⟨0⟩) [] rfl
  ok := by decide
  store := fun a fi h => by simp [edropCfg, segStore, Store.funcInst?] at h
  small := storeSmall_segStore

theorem not_good20F_edropCfg (P : Profile) : ¬ Good20F Empty.elim P edropCfg := by
  intro h
  have := h.ok
  revert this
  decide

/-- **`elem.drop` is a step of the script with the `STORE` erratum**, from a configuration
outside `Good20F`. -/
theorem sstep_edropCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim edropCfg) (configV Empty.elim edropCfg') :=
  (fwd_good20B (good20B_edropCfg P) (step_edropCfg P fun _ _ _ _ => False)).2

def ddropCfg : Config Empty := ⟨initStore, initFrame, [.plain (.dataDrop ⟨0⟩)]⟩

def ddropCfg' : Config Empty := ⟨initStore.setDataInst 0 ⟨ByteArray.empty⟩, initFrame, []⟩

/-- **V2 drops the data segment.** -/
theorem step_ddropCfg (P : Profile) (host : HostSemantics Empty) :
    Step P host ddropCfg ddropCfg' :=
  DropFwd.step (.data (di := ⟨⟨#[5]⟩⟩) rfl rfl)

set_option maxHeartbeats 4000000 in
theorem good20B_ddropCfg (P : Profile) : Good20B Empty.elim P ddropCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨eraseS initStore, initFrame, [Admin.plain (.dataDrop ⟨0⟩)].map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  plain := Plain20.plain (s := initStore) (f := initFrame) [] (.dataDrop ⟨0⟩) [] rfl
  ok := by decide
  store := fun a fi h => by simp [ddropCfg, initStore, Store.funcInst?] at h
  small := storeSmall_initStore

theorem not_good20F_ddropCfg (P : Profile) : ¬ Good20F Empty.elim P ddropCfg := by
  intro h
  have := h.ok
  revert this
  decide

/-- **`data.drop` is a step of the script with the `STORE` erratum**, from a configuration
outside `Good20F`. -/
theorem sstep_ddropCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim ddropCfg) (configV Empty.elim ddropCfg') :=
  (fwd_good20B (good20B_ddropCfg P) (step_ddropCfg P fun _ _ _ _ => False)).2

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
