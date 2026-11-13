module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.CallIndGoodCode
public import Silmaril.Wasm.SpecTec.Sim20.ElseAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim20.StoreAgree.Thms

/-!
# `call_indirect`, `table.size`, `memory.size` and `table.get` inside a covered run

`Good20CI hn P c` is round 3's `Whole.Good20C` with `call_indirect` admitted wherever the
frame's module defines its type index, and with `table.size`, `memory.size` and `table.get`
(`adminOkI`),
over a store whose functions are covered in their own modules (`StoreOkI`).

* **`fwd_good20CI`**: every V2 step from a `Good20CI` configuration is a step of the corrected
  script `simEnv20S (storeB P)` between the images (round 3's `Whole.wholeStepFwd20F` fragment
  with `SizeFwd20` and `TableGetFwd20`, through `cover20CI` and `fwdBase20_fwdG`), and its successor is `Good20CI`. **`good20CI_steps`**: so is every
  configuration of a run; `fwd_good20CI_T`: the step is also one of `simEnv20T`.
* `good20CI_of_good20C`, `good20CI_invoke`: every `Good20C` configuration is `Good20CI`, and at an
  invocation `val* (CALL_ADDR a)` only a typed image, whole pages and `StoreOkI` are needed.
* `memSizeCfg`: `memory.size` over one empty memory is `Good20CI`, and its V2 step is a step of
  the corrected script (`sstep_memSizeCfg`).
* `callIndCfg`: `i32.const 0; call_indirect 0 0` over an empty table and one function type. It
  is `Good20CI` (`good20CI_callIndCfg`; the image is typed by evaluation), V2 traps
  (`step_callIndCfg`), and the trap is a step of the corrected script (`sstep_callIndCfg`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.CallIndGood

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Good20C Plain20 WholePages storeB)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String}

/-- The widened fragment is a base at `storeB`. -/
theorem fwdBase20_fwdG (P : Profile) :
    Whole.FwdBase20 (storeB P) hn WholePages (FwdStep20G (H := H) P) where
  sr c c' hc h := by
    cases h with
    | fwd h => exact (Whole.fwdBase20_fwdF P).sr c c' hc h
    | size h => exact (fwdBase20_size (W := WholePages)).sr c c' hc h
    | tget h => exact (fwdBase20_tableGet (W := WholePages)).sr c c' hc h
  fwd c c' hc hw h := by
    cases h with
    | fwd h => exact (Whole.fwdBase20_fwdF P).fwd c c' hc hw h
    | size h => exact fwdBase20_size.fwd c c' hc hw h
    | tget h => exact fwdBase20_tableGet.fwd c c' hc hw h

/-- **The covered configurations with `call_indirect`**, at profile `P`. -/
structure Good20CI (hn : H → String) (P : Profile) (c : Config H) : Prop where
  typed : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) hn c
  whole : WholePages c.store
  plain : Plain20 c.store c.frame c.code
  ok : c.code.all (adminOkI c.frame.module) = true
  store : StoreOkI c.store

/-- **Every V2 step from a `Good20CI` configuration is a corrected-script step, and its successor
is `Good20CI`.** -/
theorem fwd_good20CI {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hg : Good20CI hn P c) (h : Step P host c c') :
    Good20CI hn P c' ∧ SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c') := by
  have hN := cover20CI h hg.plain.tail hg.ok hg.store
  obtain ⟨ht, hst⟩ := Whole.fwd_nest20 (fwdBase20_fwdG P) hN hg.typed hg.whole
  obtain ⟨hok, hm, -⟩ := adminOkI_step h hg.ok hg.store
  exact ⟨⟨ht, hg.whole.of_fm hm, Whole.plain20_step h hg.plain, hok, hg.store.of_fm hm⟩, hst⟩

/-- The same step in the script with the `STORE` erratum. -/
theorem fwd_good20CI_T {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hg : Good20CI hn P c) (h : Step P host c c') :
    SStepB (StoreFix.simEnv20T (storeB P)) (configV hn c) (configV hn c') :=
  ElseAgree.sstepB20T_of_sstepB20S' (fwd_good20CI hg h).2

/-- **Every configuration of a run from a `Good20CI` configuration is `Good20CI`.** -/
theorem good20CI_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20CI hn P c) : Good20CI hn P c' := by
  induction h with
  | refl => exact hg
  | tail _ h₂ ih => exact (fwd_good20CI ih h₂).1

/-- **Every `Good20C` configuration is `Good20CI`.** -/
theorem good20CI_of_good20C {P : Profile} {c : Config H} (hg : Good20C hn P c) :
    Good20CI hn P c :=
  ⟨hg.typed, hg.whole, hg.plain, by rw [← adminOkIL_eq]; exact adminOkIL_of_adminOk _ _ hg.ok,
    storeOkI_of_storeOk hg.store⟩

/-- **At an invocation**, `Good20CI` asks for a typed image, whole pages and `StoreOkI`. -/
theorem good20CI_invoke {P : Profile} {s : Store H} {f : Frame} {args : List Val} {a : FuncAddr}
    (ht : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) hn ⟨s, f, vals args ++ [.callAddr a]⟩)
    (hw : WholePages s) (hs : StoreOkI s) : Good20CI hn P ⟨s, f, vals args ++ [.callAddr a]⟩ :=
  ⟨ht, hw, Whole.plain20_invoke args a, by simp [List.all_append], hs⟩

/-! ## A configuration that runs `call_indirect` -/

/-- The function type `[] → []`. -/
def unitFT : V2.FuncType := ⟨[], []⟩

/-- One empty `funcref` table. -/
def callIndStore : Store Empty := { tables := [⟨⟨⟨0, none⟩, .funcref⟩, []⟩] }

/-- A frame whose module has that table and the type `[] → []`. -/
def callIndFrame : Frame := { module := { types := [unitFT], tables := [0] } }

/-- `i32.const 0; call_indirect 0 0`. -/
def callIndCfg : Config Empty :=
  ⟨callIndStore, callIndFrame, [constI32 0, .plain (.callIndirect ⟨0⟩ ⟨0⟩)]⟩

/-- Its successor: the table is empty, so the call traps. -/
def callIndCfg' : Config Empty := ⟨callIndStore, callIndFrame, [.trap]⟩

theorem table?_callInd : (⟨callIndStore, callIndFrame⟩ : State Empty).table? ⟨0⟩ =
    some ⟨⟨⟨0, none⟩, .funcref⟩, []⟩ := rfl

/-- **V2 traps on it.** -/
theorem step_callIndCfg (P : Profile) (host : HostSemantics Empty) :
    Step P host callIndCfg callIndCfg' :=
  .read (.callIndirectTrap table?_callInd (by simp))

set_option maxHeartbeats 4000000 in
/-- **It is `Good20CI`**: the image is typed by evaluation. -/
theorem good20CI_callIndCfg (P : Profile) : Good20CI Empty.elim P callIndCfg where
  typed := ⟨300, by with_unfolding_all rfl⟩
  whole := by intro mi hm; simp [callIndCfg, callIndStore] at hm
  plain := Whole.plain20_vals_expr [Whole.i32V 0] [.callIndirect ⟨0⟩ ⟨0⟩]
  ok := by decide
  store := by intro a fi h; simp [callIndCfg, callIndStore, Store.funcInst?] at h

/-- **The trap is a step of the corrected script.** -/
theorem sstep_callIndCfg (P : Profile) :
    SStepB (simEnv20S (storeB P)) (configV Empty.elim callIndCfg) (configV Empty.elim callIndCfg') :=
  (fwd_good20CI (good20CI_callIndCfg P) (step_callIndCfg P fun _ _ _ _ => False)).2

/-! ## A configuration that runs `memory.size` -/

/-- `memory.size` over one empty memory. -/
def memSizeCfg : Config Empty :=
  ⟨StoreAgree.memOnlyStore, StoreFix.memFrame, [.plain .memorySize]⟩

/-- Its successor `i32.const 0`. -/
def memSizeCfg' : Config Empty := ⟨StoreAgree.memOnlyStore, StoreFix.memFrame, [constI32 0]⟩

/-- **V2 reads the size 0.** -/
theorem step_memSizeCfg (P : Profile) (host : HostSemantics Empty) :
    Step P host memSizeCfg memSizeCfg' :=
  .read (.memorySize (mi := ⟨⟨⟨0, none⟩⟩, ByteArray.empty⟩) rfl rfl)

set_option maxHeartbeats 4000000 in
/-- **It is `Good20CI`.** -/
theorem good20CI_memSizeCfg (P : Profile) : Good20CI Empty.elim P memSizeCfg where
  typed := ⟨300, by with_unfolding_all rfl⟩
  whole := by
    intro mi hm
    simp [memSizeCfg, StoreAgree.memOnlyStore] at hm
    subst hm
    rfl
  plain := Whole.plain20_vals_expr [] [.memorySize]
  ok := by decide
  store := by intro a fi h; simp [memSizeCfg, StoreAgree.memOnlyStore, Store.funcInst?] at h

/-- **The size read is a step of the corrected script.** -/
theorem sstep_memSizeCfg (P : Profile) :
    SStepB (simEnv20S (storeB P)) (configV Empty.elim memSizeCfg) (configV Empty.elim memSizeCfg') :=
  (fwd_good20CI (good20CI_memSizeCfg P) (step_memSizeCfg P fun _ _ _ _ => False)).2

end Silmaril.Wasm.SpecTec.Sim20.CallIndGood
