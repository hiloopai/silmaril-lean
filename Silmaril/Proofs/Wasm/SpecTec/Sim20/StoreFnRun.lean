module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnNest
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepRun
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixNeed

/-!
# An invariant with stores inside the store's functions, preserved by steps

`Good20F hn P c` is an earlier `StoreDeep.Good20D` with stores admitted in the store's functions:

* `TypF`: the state with its function bodies deeply erased, and the deeply erased code, typed in
  `simEnv20`;
* the plain-tail invariant `Whole.Plain20`, the code `okD` in the frame's module, and a
  `StoreOkD` store (every function a Wasm function with an `okD` body).

Whole pages are no longer needed: no rule of the fragment reads them.

* **`fwd_good20F`**: every V2 step from a `Good20F` configuration is a step of
  `simEnv20T (storeB P)` between the images, and its successor is `Good20F`.
  **`good20F_steps`**, `runT_good20F`, `typed20T_of_good20F`.
* **`good20F_of_good20D`**: `Good20D` (and so `Good20M`, `Good20CS`, `Good20CI`) is included.
* **`good20F_invoke`**: at an invocation `val* (CALL_ADDR a)`, `Good20F` asks only for the
  erased state typed in `simEnv20` and `StoreOkD`.
* `callStoreCfg`: `CALL_ADDR 0` over a store whose one function is
  `i32.const 0; i32.const 0; i32.store`. It is `Good20F`; its state is **not** typed in
  `simEnv20` (`not_typed20_callStoreCfg`), so it is outside every earlier invariant; V2 calls the
  function (`step_callStoreCfg`), and the step is a step of `simEnv20T` through
  `Step_read/call_addr` with a body that holds a store (`sstep_callStoreCfg`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFn

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
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (okD eDA Good20D)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String}

/-- **The covered configurations with stores in the store's functions**, at profile `P`. -/
structure Good20F (hn : H → String) (P : Profile) (c : Config H) : Prop where
  typ : TypF (storeB P) hn c
  plain : Plain20 c.store c.frame c.code
  ok : c.code.all (okD c.frame.module) = true
  store : StoreOkD c.store

/-- **Every V2 step from a `Good20F` configuration is a step of the script with the `STORE`
erratum, and its successor is `Good20F`.** -/
theorem fwd_good20F {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hg : Good20F hn P c) (h : Step P host c c') :
    Good20F hn P c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hN := cover20F h hg.plain.tail hg.ok hg.store
  obtain ⟨ht', hst⟩ := fwd_nestF host hN hg.typ hg.ok hg.store
  obtain ⟨hok', hf, -, -⟩ := okF_step h hg.ok hg.store
  exact ⟨⟨ht', Whole.plain20_step h hg.plain, hok', storeOkD_of_funcs hg.store hf⟩, hst⟩

/-- **Every configuration of a run from a `Good20F` configuration is `Good20F`.** -/
theorem good20F_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20F hn P c) : Good20F hn P c' := by
  induction h with
  | refl => exact hg
  | tail _ h₂ ih => exact (fwd_good20F ih h₂).1

/-- **Every run from a `Good20F` configuration is a run of the script with the `STORE`
erratum** between the images. -/
theorem runT_good20F {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20F hn P c) :
    Relation.ReflTransGen (SStepB (simEnv20T (storeB P))) (configV hn c) (configV hn c') := by
  induction h with
  | refl => exact .refl
  | tail h₁ h₂ ih => exact .tail ih (fwd_good20F (good20F_steps h₁ hg) h₂).2

/-- **The image of a `Good20F` configuration is typed in `simEnv20T`.** -/
theorem typed20T_of_good20F {P : Profile} {c : Config H} (hg : Good20F hn P c) :
    Typed20 (simEnv20T (storeB P)) hn c :=
  Pure.typedV_closedCase20 (StoreGood.findTyp_config20T _) rfl
    (Whole.hasTyp_tup2G (hg.typ.stateT hg.store) (hg.typ.codeT hg.ok)) _ ⟨rfl, rfl, rfl⟩

/-! ## Inclusions and invocation -/

/-- **Every `Good20D` configuration is `Good20F`.** -/
theorem good20F_of_good20D {P : Profile} {c : Config H} (hg : Good20D hn P c) : Good20F hn P c :=
  ⟨typF_of_typD hg.typ hg.store, hg.plain, hg.ok, storeOkD_of_storeOkM hg.store⟩

/-- **At an invocation `val* (CALL_ADDR a)`, `Good20F` asks only for the erased state typed in
`simEnv20` and a `StoreOkD` store.** -/
theorem good20F_invoke {P : Profile} {s : Store H} {f : Frame} {args : List Val} {a : FuncAddr}
    (hz : TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) stateT (stateV hn (eraseS s) f))
    (hs : StoreOkD s) : Good20F hn P ⟨s, f, vals args ++ [.callAddr a]⟩ := by
  refine ⟨⟨hz, ?_⟩, Whole.plain20_invoke args a, by simp [List.all_append], hs⟩
  simp only [List.map_append, StoreDeep.map_eDA_vals, List.map_cons, List.map_nil,
    StoreDeep.eDA_callAddr]
  exact Whole.typedV_admins_append20_iff.2 ⟨Whole.typedV_admins_vals20 args,
    Whole.typedV_admins_callAddr20 a⟩

/-- **`Fwd20T` holds on `Good20F`**, with no hypothesis. -/
theorem fwd20T_good20F (hn : H → String) (host : HostSemantics H) :
    StoreAgree.Fwd20T hn host (storeB v2Profile) (Good20F hn v2Profile) :=
  fun _ _ hg h => .single (fwd_good20F hg h).2

/-- **The 1.0 → 2.0-script composite at `simEnv20T`, from a `Good20F` configuration.** -/
theorem composite10T20_good20F (hn : H → String) (src : V1.Execution.HostSemantics H)
    (tgt : HostSemantics H)
    (hosts : Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt)
    {a b : V1.Execution.Config H} {c : Config H} (hab : V1.Execution.Step src a b)
    (hs : Lime1.Execution.ToV2.Sim a.toLime c) (hg : Good20F hn v2Profile c) :
    ∃ c', Lime1.Execution.ToV2.Sim b.toLime c' ∧
      Relation.TransGen (SStepB (simEnv20T (storeB v2Profile))) (configV hn c) (configV hn c') :=
  StoreAgree.composite10T20 H hn src tgt _ _ hosts (fwd20T_good20F hn tgt) a b c hab hs
    fun _ h => good20F_steps h hg

/-! ## A call to a function that stores -/

/-- The function's module: one memory. -/
def storeFnModule : ModuleInst := { mems := [0] }

/-- `i32.const 0; i32.const 0; i32.store`, as a function of type `[] -> []`. -/
def storeFnInst : FuncInst Empty :=
  ⟨⟨[], []⟩, storeFnModule, .wasm ⟨⟨0⟩, [], StoreDeep.storeBody⟩⟩

/-- One storing function and one empty memory. -/
def storeFnStore : Store Empty := { funcs := [storeFnInst], mems := StoreAgree.memOnlyStore.mems }

/-- `CALL_ADDR 0`. -/
def callStoreCfg : Config Empty := ⟨storeFnStore, StoreFix.memFrame, [.callAddr 0]⟩

/-- Its successor: the callee's frame around a label around the body. -/
def callStoreCfg' : Config Empty :=
  ⟨storeFnStore, StoreFix.memFrame, [.frame 0 (Frame.forCall storeFnModule [] [])
    [.label 0 [] (expression StoreDeep.storeBody)]]⟩

/-- **V2 calls the function.** -/
theorem step_callStoreCfg (P : Profile) (host : HostSemantics Empty) :
    Step P host callStoreCfg callStoreCfg' :=
  .read (.callAddr (vs := []) (fi := storeFnInst) rfl rfl rfl)

theorem storeOkD_storeFnStore : StoreOkD storeFnStore := by
  intro a fi h
  match a, h with
  | 0, h =>
    obtain rfl := Option.some.inj h.symm
    exact ⟨_, rfl, by decide⟩

/-- **The store is not `StoreOkM`**: its function stores. -/
theorem not_storeOkM_storeFnStore : ¬ GoodMerge.StoreOkM storeFnStore := by
  intro h
  obtain ⟨fn, hc, hb⟩ := h 0 storeFnInst rfl
  cases hc
  revert hb
  decide

/-- **The state of `callStoreCfg` is not typed in `simEnv20`**, at any builtins, so it lies
outside every invariant of rounds 3–5 an earlier step. -/
theorem not_typed20_callStoreCfg (B : Builtins) :
    ¬ TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) stateT
      (stateV Empty.elim callStoreCfg.store callStoreCfg.frame) :=
  StoreFix.not_typedV_state_storeFn20 _
    ⟨0, storeFnInst, _, StoreFix.i32Store0, rfl, rfl, by simp [StoreDeep.storeBody], .int _ _ _⟩

set_option maxHeartbeats 4000000 in
/-- **It is `Good20F`**: the erased image is typed by evaluation. -/
theorem good20F_callStoreCfg (P : Profile) : Good20F Empty.elim P callStoreCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨eraseS storeFnStore, StoreFix.memFrame, callStoreCfg.code.map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  plain := Whole.plain20_invoke [] 0
  ok := by decide
  store := storeOkD_storeFnStore

/-- **Calling the function is a step of the script with the `STORE` erratum**, by
`Step_read/call_addr` fired in `simEnv20T` with a body that holds a store. -/
theorem sstep_callStoreCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim callStoreCfg)
      (configV Empty.elim callStoreCfg') :=
  (fwd_good20F (good20F_callStoreCfg P) (step_callStoreCfg P fun _ _ _ _ => False)).2

/-- **Non-vacuity**: a `Good20F` configuration whose state is untyped in `simEnv20` makes a V2
step that is a step of `simEnv20T`. -/
theorem good20F_beyond_simEnv20 (P : Profile) :
    ∃ c c' : Config Empty, Good20F Empty.elim P c ∧
      ¬ TypedV (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) stateT
        (stateV Empty.elim c.store c.frame) ∧
      Step P (fun _ _ _ _ => False) c c' ∧
      SStepB (simEnv20T (storeB P)) (configV Empty.elim c) (configV Empty.elim c') :=
  ⟨_, _, good20F_callStoreCfg P, not_typed20_callStoreCfg _, step_callStoreCfg P _,
    sstep_callStoreCfg P⟩

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
