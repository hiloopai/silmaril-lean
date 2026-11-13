module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.GoodMergeNest

/-!
# One invariant for stores, `call_indirect`, the size and `table.get` reads and packed loads

`Good20M hn P c` merges round 5's `StoreGood.Good20CS` and `CallIndGood.Good20CI`, and admits
packed loads:

* `TypS`: the state typed in `simEnv20`, and the erased code typed there;
* whole pages, the plain-tail invariant `Whole.Plain20`, a `StoreOkM` store;
* the code `okA true` in the frame's module.

* **`fwd_good20M`**: every V2 step from a `Good20M` configuration is a step of
  `simEnv20T (storeB P)` between the images, and its successor is `Good20M`. **`good20M_steps`**:
  so is every configuration of a run; `runT_good20M`: every run is a run of `simEnv20T`.
* `typed20T_of_good20M`: the image is a typed `config` of `simEnv20T`.
* **`good20M_of_good20CS`**, **`good20M_of_good20CI`**: both invariants  are included.
* `good20M_invoke`: at an invocation `val* (CALL_ADDR a)`, a typed image, whole pages and
  `StoreOkM`.
* `fwd20T_good20M`, `composite10T20_good20M`: the composite route  from `Good20M`.
* `packCfg`: `i32.const 0; i32.load8_u` over one empty memory. It is `Good20M`, V2 traps
  (`step_packCfg`), and the trap is a step of `simEnv20T` (`sstep_packCfg`), through the packed
  load rule 24.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.GoodMerge

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Plain20 WholePages storeB)
open Silmaril.Wasm.SpecTec.Sim20.StoreGood (TypS Good20CS)
open Silmaril.Wasm.SpecTec.Sim20.CallIndGood (Good20CI)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String}

/-- **The merged covered configurations**, at profile `P`. -/
structure Good20M (hn : H → String) (P : Profile) (c : Config H) : Prop where
  typ : TypS (storeB P) hn c
  whole : WholePages c.store
  plain : Plain20 c.store c.frame c.code
  ok : c.code.all (okA true c.frame.module) = true
  store : StoreOkM c.store

/-- **Every V2 step from a `Good20M` configuration is a step of the script with the `STORE`
erratum, and its successor is `Good20M`.** -/
theorem fwd_good20M {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hg : Good20M hn P c) (h : Step P host c c') :
    Good20M hn P c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hN := cover20M h hg.plain.tail hg.ok hg.store
  obtain ⟨ht', hst⟩ := fwd_nestM host hN hg.typ hg.ok hg.whole hg.store
  obtain ⟨hok', hf, hw, -⟩ := okA_step h hg.ok hg.store
  exact ⟨⟨ht', hw hg.whole, Whole.plain20_step h hg.plain, hok', storeOkM_of_funcs hg.store hf⟩, hst⟩

/-- **Every configuration of a run from a `Good20M` configuration is `Good20M`.** -/
theorem good20M_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20M hn P c) : Good20M hn P c' := by
  induction h with
  | refl => exact hg
  | tail _ h₂ ih => exact (fwd_good20M ih h₂).1

/-- **Every run from a `Good20M` configuration is a run of the script with the `STORE`
erratum** between the images. -/
theorem runT_good20M {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20M hn P c) :
    Relation.ReflTransGen (SStepB (simEnv20T (storeB P))) (configV hn c) (configV hn c') := by
  induction h with
  | refl => exact .refl
  | tail h₁ h₂ ih => exact .tail ih (fwd_good20M (good20M_steps h₁ hg) h₂).2

/-- **The image of a `Good20M` configuration is typed in `simEnv20T`.** -/
theorem typed20T_of_good20M {P : Profile} {c : Config H} (hg : Good20M hn P c) :
    Typed20 (simEnv20T (storeB P)) hn c :=
  Pure.typedV_closedCase20 (StoreGood.findTyp_config20T _) rfl
    (Whole.hasTyp_tup2G hg.typ.stateT (codeTM hg.typ hg.ok)) _ ⟨rfl, rfl, rfl⟩

/-! ## Inclusions -/

/-- **Every `Good20CS` configuration is `Good20M`.** -/
theorem good20M_of_good20CS {P : Profile} {c : Config H} (hg : Good20CS hn P c) : Good20M hn P c :=
  ⟨hg.typ, hg.whole, hg.plain, all_okA_of_adminOkS _ hg.ok, storeOkM_of_storeOk hg.store⟩

/-- **Every `Good20CI` configuration is `Good20M`.** -/
theorem good20M_of_good20CI {P : Profile} {c : Config H} (hg : Good20CI hn P c) : Good20M hn P c :=
  have ha : c.code.all (okA false c.frame.module) = true := all_okA_of_adminOkI false hg.ok
  ⟨typS_of_typed20M hg.typed ha, hg.whole, hg.plain, all_okA_true_of_false ha,
    storeOkM_of_storeOkI hg.store⟩

/-- **At an invocation**, `Good20M` asks for a typed image, whole pages and `StoreOkM`. -/
theorem good20M_invoke {P : Profile} {s : Store H} {f : Frame} {args : List Val} {a : FuncAddr}
    (ht : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) hn ⟨s, f, vals args ++ [.callAddr a]⟩)
    (hw : WholePages s) (hs : StoreOkM s) : Good20M hn P ⟨s, f, vals args ++ [.callAddr a]⟩ :=
  have ha : (vals args ++ [Admin.callAddr a]).all (okA false f.module) = true := by
    simp [List.all_append]
  ⟨typS_of_typed20M ht ha, hw, Whole.plain20_invoke args a, all_okA_true_of_false ha, hs⟩

/-! ## The composite route -/

/-- **`Fwd20T` holds on `Good20M`**, with no hypothesis. -/
theorem fwd20T_good20M (hn : H → String) (host : HostSemantics H) :
    StoreAgree.Fwd20T hn host (storeB v2Profile) (Good20M hn v2Profile) :=
  fun _ _ hg h => .single (fwd_good20M hg h).2

/-- **The 1.0 → 2.0-script composite at `simEnv20T`, from a `Good20M` configuration.** -/
theorem composite10T20_good20M (hn : H → String) (src : V1.Execution.HostSemantics H)
    (tgt : HostSemantics H)
    (hosts : Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt)
    {a b : V1.Execution.Config H} {c : Config H} (hab : V1.Execution.Step src a b)
    (hs : Lime1.Execution.ToV2.Sim a.toLime c) (hg : Good20M hn v2Profile c) :
    ∃ c', Lime1.Execution.ToV2.Sim b.toLime c' ∧
      Relation.TransGen (SStepB (simEnv20T (storeB v2Profile))) (configV hn c) (configV hn c') :=
  StoreAgree.composite10T20 H hn src tgt _ _ hosts (fwd20T_good20M hn tgt) a b c hab hs
    fun _ h => good20M_steps h hg

/-! ## A configuration that runs a packed load -/

/-- `i32.load8_u` at `memarg 0 0`. -/
abbrev load8u : V2.Instr := .intLoad .i32 (some (.i8, .unsigned)) ⟨0, 0⟩

/-- `i32.const 0; i32.load8_u` over one empty memory. -/
def packCfg : Config Empty := ⟨StoreAgree.memOnlyStore, StoreFix.memFrame, [constI32 0, .plain load8u]⟩

/-- Its successor: the memory is empty, so the load traps. -/
def packCfg' : Config Empty := ⟨StoreAgree.memOnlyStore, StoreFix.memFrame, [.trap]⟩

/-- **V2 traps on it.** -/
theorem step_packCfg (P : Profile) (host : HostSemantics Empty) : Step P host packCfg packCfg' :=
  .read (.loadPackTrap (mi := ⟨⟨⟨0, none⟩⟩, ByteArray.empty⟩) rfl (by decide))

set_option maxHeartbeats 4000000 in
/-- **It is `Good20M`**: the image is typed by evaluation. -/
theorem good20M_packCfg (P : Profile) : Good20M Empty.elim P packCfg where
  typ := by
    have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim packCfg :=
      ⟨300, by with_unfolding_all rfl⟩
    exact typS_of_typed20M h (m := StoreFix.memFrame.module) (by decide)
  whole := by
    intro mi hm
    simp [packCfg, StoreAgree.memOnlyStore] at hm
    subst hm
    rfl
  plain := Whole.plain20_vals_expr [Whole.i32V 0] [load8u]
  ok := by decide
  store := by intro a fi h; simp [packCfg, StoreAgree.memOnlyStore, Store.funcInst?] at h

/-- **The trap is a step of the script with the `STORE` erratum**, by rule 24. -/
theorem sstep_packCfg (P : Profile) :
    SStepB (simEnv20T (storeB P)) (configV Empty.elim packCfg) (configV Empty.elim packCfg') :=
  (fwd_good20M (good20M_packCfg P) (step_packCfg P fun _ _ _ _ => False)).2

end Silmaril.Wasm.SpecTec.Sim20.GoodMerge
