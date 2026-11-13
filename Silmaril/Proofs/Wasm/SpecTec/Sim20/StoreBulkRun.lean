module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkNest

/-!
# An invariant with the memory bulk instructions, preserved by steps

`Good20B hn P c` is round 5's `StoreFn.Good20F` with `memory.fill`, `memory.copy` and
`memory.init` admitted at every depth, in the code and in the store's functions:

* `TypF`: the state with its function bodies deeply erased, and the deeply erased code, typed in
  `simEnv20` (the erasure keeps the bulk instructions);
* the plain-tail invariant `Whole.Plain20`, the code `okB` in the frame's module, a `StoreOkB`
  store, and `StoreSmall`: every memory and every data segment has fewer than `2 ^ 32` bytes,
  every table and every element segment fewer than `2 ^ 32` entries.

`StoreSmall` is the restatement of the `-succ`, `-le` and `-gt` rules: V2 computes their sums in
`i32`, the script over the naturals. It holds of every memory below the 2.0 maximum of 65536
pages and every data segment below `2 ^ 32` bytes, and steps keep it (no covered step grows a
memory or changes a data segment).

* **`fwd_good20B`**: every V2 step from a `Good20B` configuration is a step of
  `simEnv20T (storeB P)` between the images, and its successor is `Good20B`.
  **`good20B_steps`**, `runT_good20B`, `typed20T_of_good20B`.
* **`good20B_of_good20F`**: `Good20F` with `StoreSmall` is `Good20B`.
* `good20B_invoke`: at `val* (CALL_ADDR a)`, `Good20B` asks for the erased state typed in
  `simEnv20`, `StoreOkB` and `StoreSmall`.
* Witnesses outside `Good20F`: `fillCfg` (`i32.const 0; i32.const 7; i32.const 1; memory.fill`
  over a one-byte memory), whose `memory.fill-succ` step is a step of `simEnv20T`
  (`sstep_fillCfg`), and `callFillCfg`, a call to a function whose body holds `memory.fill`
  (`sstep_callFillCfg`). Neither is `Good20F` (`not_good20F_fillCfg`,
  `not_good20F_callFillCfg`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Plain20 storeB typed20_iff)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (okD eDA)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (TypF Good20F eraseS)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String}

/-- **The covered configurations with the memory bulk instructions and stores at every
depth**, at profile `P`. -/
structure Good20B (hn : H → String) (P : Profile) (c : Config H) : Prop where
  typ : TypF (storeB P) hn c
  plain : Plain20 c.store c.frame c.code
  ok : c.code.all (okB c.frame.module) = true
  store : StoreOkB c.store
  small : StoreSmall c.store

/-- **Every V2 step from a `Good20B` configuration is a step of the script with the `STORE`
erratum, and its successor is `Good20B`.** -/
theorem fwd_good20B {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hg : Good20B hn P c) (h : Step P host c c') :
    Good20B hn P c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hN := cover20B h hg.plain.tail hg.ok hg.store
  obtain ⟨ht', hst⟩ := fwd_nestB host hN hg.typ hg.ok hg.store hg.small
  obtain ⟨hok', hf, hsm, -⟩ := okB_step h hg.ok hg.store
  exact ⟨⟨ht', Whole.plain20_step h hg.plain, hok', storeOkB_of_funcs hg.store hf, hsm hg.small⟩,
    hst⟩

/-- **Every configuration of a run from a `Good20B` configuration is `Good20B`.** -/
theorem good20B_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20B hn P c) : Good20B hn P c' := by
  induction h with
  | refl => exact hg
  | tail _ h₂ ih => exact (fwd_good20B ih h₂).1

/-- **Every run from a `Good20B` configuration is a run of the script with the `STORE`
erratum** between the images. -/
theorem runT_good20B {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20B hn P c) :
    Relation.ReflTransGen (SStepB (simEnv20T (storeB P))) (configV hn c) (configV hn c') := by
  induction h with
  | refl => exact .refl
  | tail h₁ h₂ ih => exact .tail ih (fwd_good20B (good20B_steps h₁ hg) h₂).2

/-- **The image of a `Good20B` configuration is typed in `simEnv20T`.** -/
theorem typed20T_of_good20B {P : Profile} {c : Config H} (hg : Good20B hn P c) :
    Typed20 (simEnv20T (storeB P)) hn c :=
  Pure.typedV_closedCase20 (StoreGood.findTyp_config20T _) rfl
    (Whole.hasTyp_tup2G (typF_stateB hg.typ hg.store) (typF_codeB hg.typ hg.ok)) _ ⟨rfl, rfl, rfl⟩

/-! ## Inclusions and invocation -/

/-- **`Good20F` with memories and data segments below `2 ^ 32` bytes is `Good20B`.** -/
theorem good20B_of_good20F {P : Profile} {c : Config H} (hg : Good20F hn P c)
    (hm : StoreSmall c.store) : Good20B hn P c :=
  ⟨hg.typ, hg.plain, all_okB_of_okD hg.ok, storeOkB_of_storeOkD hg.store, hm⟩

/-- **At an invocation `val* (CALL_ADDR a)`, `Good20B` asks only for the erased state typed in
`simEnv20`, a `StoreOkB` store and `StoreSmall`.** -/
theorem good20B_invoke {P : Profile} {s : Store H} {f : Frame} {args : List Val} {a : FuncAddr}
    (hz : TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) stateT (stateV hn (eraseS s) f))
    (hs : StoreOkB s) (hm : StoreSmall s) : Good20B hn P ⟨s, f, vals args ++ [.callAddr a]⟩ := by
  refine ⟨⟨hz, ?_⟩, Whole.plain20_invoke args a, by simp [List.all_append], hs, hm⟩
  simp only [List.map_append, StoreDeep.map_eDA_vals, List.map_cons, List.map_nil,
    StoreDeep.eDA_callAddr]
  exact Whole.typedV_admins_append20_iff.2 ⟨Whole.typedV_admins_vals20 args,
    Whole.typedV_admins_callAddr20 a⟩

/-- **`Fwd20T` holds on `Good20B`**, with no hypothesis. -/
theorem fwd20T_good20B (hn : H → String) (host : HostSemantics H) :
    StoreAgree.Fwd20T hn host (storeB v2Profile) (Good20B hn v2Profile) :=
  fun _ _ hg h => .single (fwd_good20B hg h).2

/-- **The 1.0 → 2.0-script composite at `simEnv20T`, from a `Good20B` configuration.** -/
theorem composite10T20_good20B (hn : H → String) (src : V1.Execution.HostSemantics H)
    (tgt : HostSemantics H)
    (hosts : Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt)
    {a b : V1.Execution.Config H} {c : Config H} (hab : V1.Execution.Step src a b)
    (hs : Lime1.Execution.ToV2.Sim a.toLime c) (hg : Good20B hn v2Profile c) :
    ∃ c', Lime1.Execution.ToV2.Sim b.toLime c' ∧
      Relation.TransGen (SStepB (simEnv20T (storeB v2Profile))) (configV hn c) (configV hn c') :=
  StoreAgree.composite10T20 H hn src tgt _ _ hosts (fwd20T_good20B hn tgt) a b c hab hs
    fun _ h => good20B_steps h hg

/-! ## Witnesses: `memory.fill` in the code and in a function -/

/-- A memory of one byte. -/
def oneByteMem : MemInst := ⟨⟨⟨0, none⟩⟩, ⟨#[0]⟩⟩

/-- One memory of one byte. -/
def oneByteStore : Store Empty := { mems := [oneByteMem] }

/-- The value written, `i32.const 7`. -/
abbrev seven : Val := .num ⟨.int .i32, 7⟩

/-- `i32.const 0; i32.const 7; i32.const 1; memory.fill`. -/
def fillCode : List Admin := [constI32 0, seven.toAdmin, constI32 1, .plain .memoryFill]

/-- The code over the one-byte memory. -/
def fillCfg : Config Empty := ⟨oneByteStore, StoreFix.memFrame, fillCode⟩

/-- Its successor by `memory.fill-succ`. -/
def fillCfg' : Config Empty := ⟨oneByteStore, StoreFix.memFrame,
  [constI32 0, seven.toAdmin, store8, constI32 (0 + 1), seven.toAdmin, constI32 (1 - 1),
    .plain .memoryFill]⟩

theorem mem_oneByteStore :
    (⟨oneByteStore, StoreFix.memFrame⟩ : State Empty).mem? memIdx0 = some oneByteMem := rfl

/-- **V2 fills the byte**: `memory.fill-succ`. -/
theorem step_fillCfg (P : Profile) (host : HostSemantics Empty) : Step P host fillCfg fillCfg' :=
  MemFillFwd.step (.succ mem_oneByteStore (by decide) (by decide))

theorem storeSmall_oneByteStore : StoreSmall oneByteStore := by
  refine ⟨fun mi hmi => ?_, fun di hdi => by simp [oneByteStore] at hdi,
    fun ti hti => by simp [oneByteStore] at hti,
    fun ei hei => by simp [oneByteStore] at hei⟩
  simp only [oneByteStore, List.mem_singleton] at hmi
  subst hmi
  decide

theorem plain20_fillCode : Plain20 oneByteStore StoreFix.memFrame fillCode := by
  have h := Plain20.plain (s := oneByteStore) (f := StoreFix.memFrame)
    [.num ⟨.int .i32, 0⟩, seven, .num ⟨.int .i32, 1⟩] .memoryFill [] rfl
  exact h

set_option maxHeartbeats 4000000 in
/-- **`fillCfg` is `Good20B`**: the erased image is typed by evaluation. -/
theorem good20B_fillCfg (P : Profile) : Good20B Empty.elim P fillCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨eraseS oneByteStore, StoreFix.memFrame, fillCode.map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  plain := plain20_fillCode
  ok := by decide
  store := fun a fi h => by simp [fillCfg, oneByteStore, Store.funcInst?] at h
  small := storeSmall_oneByteStore

/-- **`fillCfg` is not `Good20F`**: `okD` does not admit `memory.fill`. -/
theorem not_good20F_fillCfg (P : Profile) : ¬ Good20F Empty.elim P fillCfg := by
  intro h
  have := h.ok
  revert this
  decide

/-- **`memory.fill-succ` is a step of the script with the `STORE` erratum**, from a
configuration outside `Good20F`. -/
theorem sstep_fillCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim fillCfg) (configV Empty.elim fillCfg') :=
  (fwd_good20B (good20B_fillCfg P) (step_fillCfg P fun _ _ _ _ => False)).2

/-- A function whose body is `i32.const 0; i32.const 7; i32.const 1; memory.fill`. -/
def fillFnInst : FuncInst Empty :=
  ⟨⟨[], []⟩, StoreFn.storeFnModule, .wasm ⟨⟨0⟩, [],
    [.intConst .i32 0, .intConst .i32 7, .intConst .i32 1, .memoryFill]⟩⟩

/-- That function and the one-byte memory. -/
def fillFnStore : Store Empty := { funcs := [fillFnInst], mems := [oneByteMem] }

/-- `CALL_ADDR 0`. -/
def callFillCfg : Config Empty := ⟨fillFnStore, StoreFix.memFrame, [.callAddr 0]⟩

/-- Its successor: the callee's frame around a label around the body. -/
def callFillCfg' : Config Empty :=
  ⟨fillFnStore, StoreFix.memFrame, [.frame 0 (Frame.forCall StoreFn.storeFnModule [] [])
    [.label 0 [] (expression [.intConst .i32 0, .intConst .i32 7, .intConst .i32 1,
      .memoryFill])]]⟩

/-- **V2 calls the function.** -/
theorem step_callFillCfg (P : Profile) (host : HostSemantics Empty) :
    Step P host callFillCfg callFillCfg' :=
  .read (.callAddr (vs := []) (fi := fillFnInst) rfl rfl rfl)

theorem storeOkB_fillFnStore : StoreOkB fillFnStore := by
  intro a fi h
  match a, h with
  | 0, h =>
    obtain rfl := Option.some.inj h.symm
    exact ⟨_, rfl, by decide⟩

theorem storeSmall_fillFnStore : StoreSmall fillFnStore := by
  refine ⟨fun mi hmi => ?_, fun di hdi => by simp [fillFnStore] at hdi,
    fun ti hti => by simp [fillFnStore] at hti,
    fun ei hei => by simp [fillFnStore] at hei⟩
  simp only [fillFnStore, List.mem_singleton] at hmi
  subst hmi
  decide

set_option maxHeartbeats 4000000 in
/-- **`callFillCfg` is `Good20B`.** -/
theorem good20B_callFillCfg (P : Profile) : Good20B Empty.elim P callFillCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨eraseS fillFnStore, StoreFix.memFrame, callFillCfg.code.map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  plain := Whole.plain20_invoke [] 0
  ok := by decide
  store := storeOkB_fillFnStore
  small := storeSmall_fillFnStore

/-- **`callFillCfg` is not `Good20F`**: its function's body is not `okD`. -/
theorem not_good20F_callFillCfg (P : Profile) : ¬ Good20F Empty.elim P callFillCfg := by
  intro h
  obtain ⟨fn, hc, hb⟩ := h.store 0 fillFnInst rfl
  cases hc
  revert hb
  decide

/-- **Calling a function whose body holds `memory.fill` is a step of the script with the
`STORE` erratum.** -/
theorem sstep_callFillCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim callFillCfg)
      (configV Empty.elim callFillCfg') :=
  (fwd_good20B (good20B_callFillCfg P) (step_callFillCfg P fun _ _ _ _ => False)).2

/-- **Non-vacuity**: a configuration outside `Good20F` whose `memory.fill-succ` step, which
writes through `i32.store8`, is a step of `simEnv20T`; and every configuration it reaches is
`Good20B`. -/
theorem good20B_beyond_good20F (P : Profile) :
    ∃ c c' : Config Empty, Good20B Empty.elim P c ∧ ¬ Good20F Empty.elim P c ∧
      Step P (fun _ _ _ _ => False) c c' ∧
      SStepB (simEnv20T (storeB P)) (configV Empty.elim c) (configV Empty.elim c') ∧
      Good20B Empty.elim P c' :=
  ⟨_, _, good20B_fillCfg P, not_good20F_fillCfg P, step_fillCfg P _, sstep_fillCfg P,
    (fwd_good20B (good20B_fillCfg P) (step_fillCfg P fun _ _ _ _ => False)).1⟩

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
