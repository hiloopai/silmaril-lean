module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkRun

/-!
# Witnesses: `memory.copy`, `memory.init` and `table.fill` steps inside `Good20B`

* `copyCfg`: `i32.const 0; i32.const 0; i32.const 1; memory.copy` over a one-byte memory. V2
  steps by `memory.copy-le` to code with `i32.load8_u` and `i32.store8` (`step_copyCfg`); the
  configuration is `Good20B` and not `Good20F`, and the step is a step of `simEnv20T`
  (`sstep_copyCfg`).
* `tfillCfg`: `i32.const 0; ref.null funcref; i32.const 1; table.fill 0` over a one-entry
  table; `table.fill-succ` steps to code with `table.set` (`sstep_tfillCfg`).
* `initCfg`: `i32.const 0; i32.const 0; i32.const 1; memory.init 0` over a one-byte memory and
  a one-byte data segment `[5]`. V2 steps by `memory.init-succ` to code with
  `i32.const 5; i32.store8` (`step_initCfg`); the same holds (`sstep_initCfg`).
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

/-! ## `memory.copy` -/

/-- `i32.const 0; i32.const 0; i32.const 1; memory.copy`. -/
def copyCodeW : List Admin := [constI32 0, constI32 0, constI32 1, .plain .memoryCopy]

def copyCfg : Config Empty := ⟨oneByteStore, StoreFix.memFrame, copyCodeW⟩

def copyCfg' : Config Empty := ⟨oneByteStore, StoreFix.memFrame,
  [constI32 0, constI32 0, load8u, store8, constI32 (0 + 1), constI32 (0 + 1), constI32 (1 - 1),
    .plain .memoryCopy]⟩

/-- **V2 copies the byte**: `memory.copy-le`. -/
theorem step_copyCfg (P : Profile) (host : HostSemantics Empty) : Step P host copyCfg copyCfg' :=
  MemCopyFwd.step (.le mem_oneByteStore (by decide) (by decide) (by decide))

theorem plain20_copyCodeW : Plain20 oneByteStore StoreFix.memFrame copyCodeW :=
  Plain20.plain (s := oneByteStore) (f := StoreFix.memFrame)
    [.num ⟨.int .i32, 0⟩, .num ⟨.int .i32, 0⟩, .num ⟨.int .i32, 1⟩] .memoryCopy [] rfl

set_option maxHeartbeats 4000000 in
theorem good20B_copyCfg (P : Profile) : Good20B Empty.elim P copyCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨eraseS oneByteStore, StoreFix.memFrame, copyCodeW.map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  plain := plain20_copyCodeW
  ok := by decide
  store := fun a fi h => by simp [copyCfg, oneByteStore, Store.funcInst?] at h
  small := storeSmall_oneByteStore

theorem not_good20F_copyCfg (P : Profile) : ¬ Good20F Empty.elim P copyCfg := by
  intro h
  have := h.ok
  revert this
  decide

/-- **`memory.copy-le` is a step of the script with the `STORE` erratum**, from a
configuration outside `Good20F`. -/
theorem sstep_copyCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim copyCfg) (configV Empty.elim copyCfg') :=
  (fwd_good20B (good20B_copyCfg P) (step_copyCfg P fun _ _ _ _ => False)).2

/-! ## `memory.init` -/

/-- A one-byte memory and a one-byte data segment `[5]`. -/
def initStore : Store Empty := { mems := [oneByteMem], datas := [⟨⟨#[5]⟩⟩] }

/-- A frame whose module has memory 0 and data segment 0. -/
def initFrame : Frame := { module := { mems := [0], datas := [0] } }

/-- `i32.const 0; i32.const 0; i32.const 1; memory.init 0`. -/
def initCodeW : List Admin := [constI32 0, constI32 0, constI32 1, .plain (.memoryInit ⟨0⟩)]

def initCfg : Config Empty := ⟨initStore, initFrame, initCodeW⟩

def initCfg' : Config Empty := ⟨initStore, initFrame,
  [constI32 0, constI32 (BitVec.ofNat 32 (5 : UInt8).toNat), store8, constI32 (0 + 1),
    constI32 (0 + 1), constI32 (1 - 1), .plain (.memoryInit ⟨0⟩)]⟩

/-- **V2 writes the data byte**: `memory.init-succ`. -/
theorem step_initCfg (P : Profile) (host : HostSemantics Empty) : Step P host initCfg initCfg' :=
  MemInitFwd.step (.succ (mi := oneByteMem) (di := ⟨⟨#[5]⟩⟩) rfl rfl (by decide) (by decide) rfl)

theorem plain20_initCodeW : Plain20 initStore initFrame initCodeW :=
  Plain20.plain (s := initStore) (f := initFrame)
    [.num ⟨.int .i32, 0⟩, .num ⟨.int .i32, 0⟩, .num ⟨.int .i32, 1⟩] (.memoryInit ⟨0⟩) [] rfl

theorem storeSmall_initStore : StoreSmall initStore := by
  refine ⟨fun mi hmi => ?_, fun di hdi => ?_, fun ti hti => by simp [initStore] at hti,
    fun ei hei => by simp [initStore] at hei⟩
  · simp only [initStore, List.mem_singleton] at hmi
    subst hmi
    decide
  · simp only [initStore, List.mem_singleton] at hdi
    subst hdi
    decide

set_option maxHeartbeats 4000000 in
theorem good20B_initCfg (P : Profile) : Good20B Empty.elim P initCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨eraseS initStore, initFrame, initCodeW.map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  plain := plain20_initCodeW
  ok := by decide
  store := fun a fi h => by simp [initCfg, initStore, Store.funcInst?] at h
  small := storeSmall_initStore

theorem not_good20F_initCfg (P : Profile) : ¬ Good20F Empty.elim P initCfg := by
  intro h
  have := h.ok
  revert this
  decide

/-- **`memory.init-succ` is a step of the script with the `STORE` erratum**, from a
configuration outside `Good20F`. -/
theorem sstep_initCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim initCfg) (configV Empty.elim initCfg') :=
  (fwd_good20B (good20B_initCfg P) (step_initCfg P fun _ _ _ _ => False)).2

/-! ## `table.fill` -/

/-- A table of one null `funcref`. -/
def oneTable : TableInst := ⟨⟨⟨1, none⟩, .funcref⟩, [.null .funcref]⟩

def tableStore : Store Empty := { tables := [oneTable] }

/-- A frame whose module has table 0. -/
def tableFrame : Frame := { module := { tables := [0] } }

/-- The value written, `ref.null funcref`. -/
abbrev nullF : Val := .ref (.null .funcref)

/-- `i32.const 0; ref.null funcref; i32.const 1; table.fill 0`. -/
def tfillCodeW : List Admin := [constI32 0, nullF.toAdmin, constI32 1, .plain (.tableFill ⟨0⟩)]

def tfillCfg : Config Empty := ⟨tableStore, tableFrame, tfillCodeW⟩

def tfillCfg' : Config Empty := ⟨tableStore, tableFrame,
  [constI32 0, nullF.toAdmin, .plain (.tableSet ⟨0⟩), constI32 (0 + 1), nullF.toAdmin,
    constI32 (1 - 1), .plain (.tableFill ⟨0⟩)]⟩

/-- **V2 fills the entry**: `table.fill-succ`. -/
theorem step_tfillCfg (P : Profile) (host : HostSemantics Empty) :
    Step P host tfillCfg tfillCfg' :=
  TableFillFwd.step (.succ (ti := oneTable) rfl (by decide) (by decide))

theorem plain20_tfillCodeW : Plain20 tableStore tableFrame tfillCodeW :=
  Plain20.plain (s := tableStore) (f := tableFrame)
    [.num ⟨.int .i32, 0⟩, nullF, .num ⟨.int .i32, 1⟩] (.tableFill ⟨0⟩) [] rfl

theorem storeSmall_tableStore : StoreSmall tableStore := by
  refine ⟨fun mi hmi => by simp [tableStore] at hmi, fun di hdi => by simp [tableStore] at hdi,
    fun ti hti => ?_, fun ei hei => by simp [tableStore] at hei⟩
  simp only [tableStore, List.mem_singleton] at hti
  subst hti
  decide

set_option maxHeartbeats 4000000 in
theorem good20B_tfillCfg (P : Profile) : Good20B Empty.elim P tfillCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨eraseS tableStore, tableFrame, tfillCodeW.map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  plain := plain20_tfillCodeW
  ok := by decide
  store := fun a fi h => by simp [tfillCfg, tableStore, Store.funcInst?] at h
  small := storeSmall_tableStore

theorem not_good20F_tfillCfg (P : Profile) : ¬ Good20F Empty.elim P tfillCfg := by
  intro h
  have := h.ok
  revert this
  decide

/-- **`table.fill-succ` is a step of the script with the `STORE` erratum**, from a configuration
outside `Good20F`; the next configuration holds a `table.set`, and is `Good20B`. -/
theorem sstep_tfillCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim tfillCfg) (configV Empty.elim tfillCfg') ∧
      Good20B Empty.elim P tfillCfg' :=
  ⟨(fwd_good20B (good20B_tfillCfg P) (step_tfillCfg P fun _ _ _ _ => False)).2,
    (fwd_good20B (good20B_tfillCfg P) (step_tfillCfg P fun _ _ _ _ => False)).1⟩

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
