module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreDeepNest

/-!
# An invariant with stores at every depth, preserved by steps

`Good20D hn P c` is round 5's `GoodMerge.Good20M` with scalar stores admitted inside block bodies,
`if` branches and label continuations, at any depth:

* `TypD`: the state typed in `simEnv20`, and the deeply erased code typed there;
* whole pages, the plain-tail invariant `Whole.Plain20`, a `StoreOkM` store (store-free functions);
* the code `okD` in the frame's module.

* **`fwd_good20D`**: every V2 step from a `Good20D` configuration is a step of
  `simEnv20T (storeB P)` between the images, and its successor is `Good20D`.
  **`good20D_steps`**, `runT_good20D`, `typed20T_of_good20D`.
* **`good20D_of_good20M`**: `Good20M` (and so `Good20CS`, `Good20CI` and round 3's `Good20C`) is
  included; on its code the deep and the shallow erasures agree.
* `good20D_invoke`, `fwd20T_good20D`, `composite10T20_good20D`.
* `blockStoreCfg`: `block [] (i32.const 0; i32.const 0; i32.store)` over one empty memory. It is
  `Good20D`, V2 enters the block (`step_blockStoreCfg`), and the step is a step of `simEnv20T`
  through `Step_read/block` with a body that holds a store (`sstep_blockStoreCfg`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreDeep

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Plain20 WholePages storeB typed20_iff)
open Silmaril.Wasm.SpecTec.Sim20.GoodMerge (okA StoreOkM Good20M)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String}

/-- **The covered configurations with stores at every depth**, at profile `P`. -/
structure Good20D (hn : H → String) (P : Profile) (c : Config H) : Prop where
  typ : TypD (storeB P) hn c
  whole : WholePages c.store
  plain : Plain20 c.store c.frame c.code
  ok : c.code.all (okD c.frame.module) = true
  store : StoreOkM c.store

/-- **Every V2 step from a `Good20D` configuration is a step of the script with the `STORE`
erratum, and its successor is `Good20D`.** -/
theorem fwd_good20D {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hg : Good20D hn P c) (h : Step P host c c') :
    Good20D hn P c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hN := cover20D h hg.plain.tail hg.ok hg.store
  obtain ⟨ht', hst⟩ := fwd_nestD host hN hg.typ hg.ok hg.whole hg.store
  obtain ⟨hok', hf, hw, -⟩ := okD_step h hg.ok hg.store
  exact ⟨⟨ht', hw hg.whole, Whole.plain20_step h hg.plain, hok',
    GoodMerge.storeOkM_of_funcs hg.store hf⟩, hst⟩

/-- **Every configuration of a run from a `Good20D` configuration is `Good20D`.** -/
theorem good20D_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20D hn P c) : Good20D hn P c' := by
  induction h with
  | refl => exact hg
  | tail _ h₂ ih => exact (fwd_good20D ih h₂).1

/-- **Every run from a `Good20D` configuration is a run of the script with the `STORE`
erratum** between the images. -/
theorem runT_good20D {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20D hn P c) :
    Relation.ReflTransGen (SStepB (simEnv20T (storeB P))) (configV hn c) (configV hn c') := by
  induction h with
  | refl => exact .refl
  | tail h₁ h₂ ih => exact .tail ih (fwd_good20D (good20D_steps h₁ hg) h₂).2

/-- **The image of a `Good20D` configuration is typed in `simEnv20T`.** -/
theorem typed20T_of_good20D {P : Profile} {c : Config H} (hg : Good20D hn P c) :
    Typed20 (simEnv20T (storeB P)) hn c :=
  Pure.typedV_closedCase20 (StoreGood.findTyp_config20T _) rfl
    (Whole.hasTyp_tup2G hg.typ.stateT (codeTD hg.typ hg.ok)) _ ⟨rfl, rfl, rfl⟩

/-! ## Inclusions -/

/-- **Every `Good20M` configuration is `Good20D`.** -/
theorem good20D_of_good20M {P : Profile} {c : Config H} (hg : Good20M hn P c) : Good20D hn P c :=
  ⟨⟨hg.typ.state, by rw [map_eDA_eq_eraseA hg.ok]; exact hg.typ.code⟩, hg.whole, hg.plain,
    all_okD_of_okA hg.ok, hg.store⟩

/-- **At an invocation**, `Good20D` asks for a typed image, whole pages and `StoreOkM`. -/
theorem good20D_invoke {P : Profile} {s : Store H} {f : Frame} {args : List Val} {a : FuncAddr}
    (ht : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) hn ⟨s, f, vals args ++ [.callAddr a]⟩)
    (hw : WholePages s) (hs : StoreOkM s) : Good20D hn P ⟨s, f, vals args ++ [.callAddr a]⟩ :=
  good20D_of_good20M (GoodMerge.good20M_invoke ht hw hs)

/-! ## The composite route -/

/-- **`Fwd20T` holds on `Good20D`**, with no hypothesis. -/
theorem fwd20T_good20D (hn : H → String) (host : HostSemantics H) :
    StoreAgree.Fwd20T hn host (storeB v2Profile) (Good20D hn v2Profile) :=
  fun _ _ hg h => .single (fwd_good20D hg h).2

/-- **The 1.0 → 2.0-script composite at `simEnv20T`, from a `Good20D` configuration.** -/
theorem composite10T20_good20D (hn : H → String) (src : V1.Execution.HostSemantics H)
    (tgt : HostSemantics H)
    (hosts : Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt)
    {a b : V1.Execution.Config H} {c : Config H} (hab : V1.Execution.Step src a b)
    (hs : Lime1.Execution.ToV2.Sim a.toLime c) (hg : Good20D hn v2Profile c) :
    ∃ c', Lime1.Execution.ToV2.Sim b.toLime c' ∧
      Relation.TransGen (SStepB (simEnv20T (storeB v2Profile))) (configV hn c) (configV hn c') :=
  StoreAgree.composite10T20 H hn src tgt _ _ hosts (fwd20T_good20D hn tgt) a b c hab hs
    fun _ h => good20D_steps h hg

/-! ## A block whose body holds a store -/

/-- The block's body, `i32.const 0; i32.const 0; i32.store`. -/
abbrev storeBody : List V2.Instr := [.intConst .i32 0, .intConst .i32 0, StoreFix.i32Store0]

/-- `block [] (i32.const 0; i32.const 0; i32.store)` over one empty memory. -/
def blockStoreCfg : Config Empty :=
  ⟨StoreAgree.memOnlyStore, StoreFix.memFrame, [.plain (.block (.result none) storeBody)]⟩

/-- Its successor: a label around the body. -/
def blockStoreCfg' : Config Empty :=
  ⟨StoreAgree.memOnlyStore, StoreFix.memFrame, [.label 0 [] (vals [] ++ expression storeBody)]⟩

/-- **V2 enters the block.** -/
theorem step_blockStoreCfg (P : Profile) (host : HostSemantics Empty) :
    Step P host blockStoreCfg blockStoreCfg' :=
  .read (.block (vs := []) (ft := ⟨[], []⟩) rfl rfl)

set_option maxHeartbeats 4000000 in
/-- **It is `Good20D`**: the erased image is typed by evaluation. -/
theorem good20D_blockStoreCfg (P : Profile) : Good20D Empty.elim P blockStoreCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
        ⟨StoreAgree.memOnlyStore, StoreFix.memFrame, blockStoreCfg.code.map eDA⟩ :=
      ⟨300, by with_unfolding_all rfl⟩
    exact ⟨(typed20_iff.1 h).1, (typed20_iff.1 h).2⟩
  whole := by
    intro mi hm
    simp [blockStoreCfg, StoreAgree.memOnlyStore] at hm
    subst hm
    rfl
  plain := Whole.plain20_vals_expr [] [.block (.result none) storeBody]
  ok := by decide
  store := by intro a fi h; simp [blockStoreCfg, StoreAgree.memOnlyStore, Store.funcInst?] at h

/-- **Entering the block is a step of the script with the `STORE` erratum**, by `Step_read/block`
fired in `simEnv20T` with a body that holds a store. -/
theorem sstep_blockStoreCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim blockStoreCfg)
      (configV Empty.elim blockStoreCfg') :=
  (fwd_good20D (good20D_blockStoreCfg P) (step_blockStoreCfg P fun _ _ _ _ => False)).2

end Silmaril.Wasm.SpecTec.Sim20.StoreDeep
