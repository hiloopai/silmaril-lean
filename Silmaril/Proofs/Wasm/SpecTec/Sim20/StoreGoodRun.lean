module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreGoodNest
public import Silmaril.Wasm.SpecTec.Sim20.StoreRun.Thms

/-!
# A storing `Good20C` preserved by steps

`Good20CS hn P c` is round 3's `Whole.Good20C` with administrative scalar stores admitted:

* `TypS`: the state typed in `simEnv20` and the erased code typed there;
* whole pages, the plain-tail invariant `Whole.Plain20`, and a covered store (`Whole.StoreOk`:
  every function is a Wasm function with a store-free covered body);
* the code `adminOkS`: covered, with scalar stores (a pack size below the width) allowed as
  administrative instructions at any depth of labels and frames.

* **`fwd_good20CS`**: every V2 step from a `Good20CS` configuration is a step of
  `simEnv20T (storeB P)` between the images, and its successor is `Good20CS`
  (`cover20CS`, `fwd_nestS`, `adminOkS_step`, `Whole.plain20_step`).
* **`good20CS_steps`**: so is every configuration of a run.
* `typed20T_of_good20CS`: the image of a `Good20CS` configuration is typed in `simEnv20T`.
* `good20CS_of_good20C`: every `Good20C` configuration is `Good20CS`.
* `fwd20T_good20CS`: `StoreAgree.Fwd20T` holds on `Good20CS`, so `Task.composite10T20` applies to
  every V1 program whose `Lime1` image is simulated by a `Good20CS` configuration
  (`composite10T20_good20CS`).
* `good20CS_memStore`, `composite10T20_memStoreCS`: round 4's storing example is `Good20CS`, and
  its composite route follows from preservation, with no inversion of V2's `Step` on concrete
  code.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreGood

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Good20C Plain20 StoreOk WholePages storeB)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String}

/-- **The covered configurations with administrative stores**, at profile `P`. -/
structure Good20CS (hn : H → String) (P : Profile) (c : Config H) : Prop where
  typ : TypS (storeB P) hn c
  whole : WholePages c.store
  plain : Plain20 c.store c.frame c.code
  ok : c.code.all adminOkS = true
  store : StoreOk c.store

/-- **Every V2 step from a `Good20CS` configuration is a step of the script with the `STORE`
erratum, and its successor is `Good20CS`.** -/
theorem fwd_good20CS {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (hg : Good20CS hn P c) (h : Step P host c c') :
    Good20CS hn P c' ∧ SStepB (simEnv20T (storeB P)) (configV hn c) (configV hn c') := by
  have hN := cover20CS h hg.plain.tail hg.ok hg.store
  obtain ⟨ht', hst⟩ := fwd_nestS host hN hg.typ hg.ok hg.whole hg.store
  obtain ⟨hok', hf, hw⟩ := adminOkS_step h hg.ok hg.store
  exact ⟨⟨ht', hw hg.whole, Whole.plain20_step h hg.plain, hok', storeOk_of_funcs hg.store hf⟩, hst⟩

/-- **Every configuration of a run from a `Good20CS` configuration is `Good20CS`.** -/
theorem good20CS_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20CS hn P c) : Good20CS hn P c' := by
  induction h with
  | refl => exact hg
  | tail _ h₂ ih => exact (fwd_good20CS ih h₂).1

/-- **Every run from a `Good20CS` configuration is a run of the script with the `STORE`
erratum** between the images. -/
theorem runT_good20CS {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hg : Good20CS hn P c) :
    Relation.ReflTransGen (SStepB (simEnv20T (storeB P))) (configV hn c) (configV hn c') := by
  induction h with
  | refl => exact .refl
  | tail h₁ h₂ ih => exact .tail ih (fwd_good20CS (good20CS_steps h₁ hg) h₂).2

set_option maxRecDepth 8000000 in
/-- `config` in `simEnv20T`, as in `simEnv20`. -/
theorem findTyp_config20T (B : Builtins) : (simEnv20T B).findTyp? "config" = some ([], [.instD [] []
    (.variantT [.mk "%;%" (.tupT [.mk "state" (.varT "state" []),
      .mk "admininstr*" (.iterT (.varT "admininstr" []) .list)]) [] []])]) := by
  with_unfolding_all rfl

/-- **The image of a `Good20CS` configuration is typed in `simEnv20T`.** -/
theorem typed20T_of_good20CS {P : Profile} {c : Config H} (hg : Good20CS hn P c) :
    Typed20 (simEnv20T (storeB P)) hn c :=
  Pure.typedV_closedCase20 (findTyp_config20T _) rfl
    (Whole.hasTyp_tup2G hg.typ.stateT (hg.typ.codeT hg.ok)) _ ⟨rfl, rfl, rfl⟩

/-- **Every `Good20C` configuration is `Good20CS`.** -/
theorem good20CS_of_good20C {P : Profile} {c : Config H} (hg : Good20C hn P c) :
    Good20CS hn P c :=
  ⟨typS_of_typed20 hg.typed hg.ok, hg.whole, hg.plain, all_adminOkS_of_adminOk hg.ok, hg.store⟩

/-! ## The composite route -/

/-- **`Fwd20T` holds on `Good20CS`**, with no hypothesis. -/
theorem fwd20T_good20CS (hn : H → String) (host : HostSemantics H) :
    StoreAgree.Fwd20T hn host (storeB v2Profile) (Good20CS hn v2Profile) :=
  fun _ _ hg h => .single (fwd_good20CS hg h).2

/-- **The 1.0 → 2.0-script composite at `simEnv20T`, from a `Good20CS` configuration**: a V1 step
whose `Lime1` image is simulated by a `Good20CS` configuration is matched by a non-empty run of
the script with the `STORE` erratum. -/
theorem composite10T20_good20CS (hn : H → String) (src : V1.Execution.HostSemantics H)
    (tgt : HostSemantics H)
    (hosts : Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt)
    {a b : V1.Execution.Config H} {c : Config H} (hab : V1.Execution.Step src a b)
    (hs : Lime1.Execution.ToV2.Sim a.toLime c) (hg : Good20CS hn v2Profile c) :
    ∃ c', Lime1.Execution.ToV2.Sim b.toLime c' ∧
      Relation.TransGen (SStepB (simEnv20T (storeB v2Profile))) (configV hn c) (configV hn c') :=
  StoreAgree.composite10T20 H hn src tgt _ _ hosts (fwd20T_good20CS hn tgt) a b c hab hs
    fun _ h => good20CS_steps h hg

/-! ## Round 4's storing example -/

set_option maxHeartbeats 4000000 in
/-- The erased code of the example, `i32.const 0; i32.const 0; nop; nop`, is typed. -/
theorem typS_memStore (P : Profile) : TypS (storeB P) Empty.elim StoreAgree.memStoreCfg2 := by
  have h : Typed20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 (storeB P)) Empty.elim
      ⟨StoreAgree.memOnlyStore, StoreFix.memFrame,
        [constI32 0, .plain (.intConst .i32 0), .plain .nop, .plain .nop]⟩ :=
    ⟨300, by with_unfolding_all rfl⟩
  exact ⟨(Whole.typed20_iff.1 h).1, (Whole.typed20_iff.1 h).2⟩

/-- **Round 4's storing example is `Good20CS`.** -/
theorem good20CS_memStore (P : Profile) : Good20CS Empty.elim P StoreAgree.memStoreCfg2 where
  typ := typS_memStore P
  whole := by
    intro mi hm
    simp [StoreAgree.memStoreCfg2, StoreAgree.memOnlyStore] at hm
    subst hm
    rfl
  plain := Whole.plain20_vals_expr [Whole.i32V 0, Whole.i32V 0] [StoreFix.i32Store0, .nop]
  ok := by decide
  store := by
    intro a fi h
    simp [StoreAgree.memStoreCfg2, StoreAgree.memOnlyStore, Store.funcInst?] at h

/-- **The composite route on round 4's example, by preservation.** -/
theorem composite10T20_memStoreCS (src : V1.Execution.HostSemantics Empty)
    (tgt : HostSemantics Empty) :
    ∃ c', Lime1.Execution.ToV2.Sim StoreRun.v1Cfg'.toLime c' ∧
      Relation.TransGen (SStepB (simEnv20T (storeB v2Profile)))
        (configV Empty.elim StoreAgree.memStoreCfg2) (configV Empty.elim c') :=
  composite10T20_good20CS Empty.elim src tgt (StoreRun.hostCompatible_empty src tgt)
    (StoreRun.v1_step src) StoreRun.v1_sim (good20CS_memStore _)

end Silmaril.Wasm.SpecTec.Sim20.StoreGood
