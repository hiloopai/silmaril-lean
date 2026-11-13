module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreRunInv

/-!
# A `composite10T20` instance on a storing V1 program

* `goodStore_memStore`: the step-shape clause of `GoodStore20T` holds at `memStoreCfg2`
  (`step_memStoreCfg2_inv`), so `memStoreCfg2` is `GoodStore20T`;
* `good20C_memStore'`: its successor `trap; nop` is round 3's covered `Good20C` (typed image by
  evaluation, whole pages, plain tail, covered code and store);
* `runGood_memStore`: so every configuration reachable from `memStoreCfg2` is in
  `GoodT20 = Good20C ∨ GoodStore20T` (`Whole.good20C_steps` after the first step);
* `v1Cfg`, `v1Cfg'`, `v1_step`, `v1_sim`: the V1 program `i32.const 0; i32.const 0; i32.store; nop`
  over one empty memory steps to `trap; nop`, and its Lime image is simulated by `memStoreCfg2`;
* **`composite10T20_memStore`**: `StoreAgree.composite10T20` at these data, with
  `Fwd20T` from `ElseAgree.fwd20T_goodT20'` (no hypothesis). The V1 step is matched by a non-empty
  run of the corrected 2.0 script with the `STORE` erratum, `simEnv20T (storeB v2Profile)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreRun

open Silmaril.Wasm Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (memOnlyStore memStoreCfg2 memStoreCfg2')
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (memFrame i32Store0)

open Silmaril.Wasm.SpecTec.Sim20 in
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree in
/-- **The step-shape clause holds**: `memStoreCfg2` is `GoodStore20T`. -/
theorem goodStore_memStore (P : Profile) (host : HostSemantics Empty) :
    GoodStore20T Empty.elim P host memStoreCfg2 := fun c' h => by
  rw [step_memStoreCfg2_inv h]
  exact storeCtxOk20_memStore P

open Silmaril.Wasm.SpecTec.Sim20 in
open Silmaril.Wasm.SpecTec.Sim20.Whole in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The successor `trap; nop` is covered. -/
theorem good20C_memStore' (P : Profile) : Good20C Empty.elim P memStoreCfg2' where
  typed := ⟨300, by with_unfolding_all rfl⟩
  whole := by intro mi hm; simp [memStoreCfg2', memOnlyStore] at hm; subst hm; rfl
  plain := Plain20.trap [] [.nop]
  ok := by decide
  store := by intro a fi h; simp [memStoreCfg2', memOnlyStore, Store.funcInst?] at h

open Silmaril.Wasm.SpecTec.Sim20 in
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree in
/-- Every configuration reachable from the example is covered or a store under a context. -/
theorem runGood_memStore (host : HostSemantics Empty) :
    Silmaril.Wasm.SpecTec.Sim10.RunGood20 host
      (GoodT20 Empty.elim Silmaril.Wasm.Lime1.Execution.v2Profile host) memStoreCfg2 := by
  intro c₁ h
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c₂, h₁, h₂⟩
  · exact Or.inr (goodStore_memStore _ host)
  · rw [step_memStoreCfg2_inv h₁] at h₂
    exact Or.inl (Whole.good20C_steps h₂ (good20C_memStore' _))

/-! ## The V1 program -/

/-- One empty memory, in V1. -/
def v1Store : Silmaril.Wasm.V1.Execution.Store Empty := { memories := [⟨ByteArray.empty, none⟩] }

/-- A frame whose module has that memory. -/
def v1Frame : Silmaril.Wasm.Execution.Runtime.Frame := { module := { memories := [⟨0⟩] } }

/-- `i32.const 0; i32.const 0; i32.store; nop`, in V1. -/
def v1Cfg : Silmaril.Wasm.V1.Execution.Config Empty :=
  ⟨v1Store, v1Frame, [Silmaril.Wasm.V1.Execution.value ⟨.int .i32, 0⟩,
    Silmaril.Wasm.V1.Execution.value ⟨.int .i32, 0⟩, .source (.intStore .i32 none ⟨0, 0⟩),
    .source .nop]⟩

/-- Its successor: the store traps. -/
def v1Cfg' : Silmaril.Wasm.V1.Execution.Config Empty := ⟨v1Store, v1Frame, [.trap, .source .nop]⟩

/-- The V1 store traps. -/
theorem v1_step (src : Silmaril.Wasm.V1.Execution.HostSemantics Empty) :
    Silmaril.Wasm.V1.Execution.Step src v1Cfg v1Cfg' := by
  have h := Silmaril.Wasm.V1.Execution.Step.context (host := src)
    (Silmaril.Wasm.V1.Execution.Step.intStoreTrap v1Store v1Frame .i32 none ⟨0, 0⟩ 0 0 ⟨0⟩
      ⟨ByteArray.empty, none⟩ rfl (by decide)) [] [.source .nop]
  exact h

/-- `memStoreCfg2` simulates the Lime image of the V1 program. -/
theorem v1_sim : Silmaril.Wasm.Lime1.Execution.ToV2.Sim v1Cfg.toLime memStoreCfg2 := by
  refine ⟨rfl, ⟨fun mi hm => ?_, fun mi hm => ?_, fun mi hm => ?_, fun ti hm => ?_,
    fun ti hm => ?_⟩⟩
  all_goals
    first
    | (have hm' : mi ∈ [(⟨ByteArray.empty, none⟩ : Silmaril.Wasm.Execution.Runtime.MemInst)] := hm
       rw [List.mem_singleton] at hm'
       subst hm'
       decide)
    | (have hm' : ti ∈ ([] : List Silmaril.Wasm.Execution.Runtime.TableInst) := hm
       cases hm')

/-- No host function exists over `Empty`, so any two hosts are compatible. -/
theorem hostCompatible_empty (src : Silmaril.Wasm.V1.Execution.HostSemantics Empty)
    (tgt : HostSemantics Empty) :
    Silmaril.Wasm.Lime1.Execution.ToV2.HostCompatible
      (src.mapCode Silmaril.Wasm.V1.Func.toLime) tgt :=
  ⟨fun h => h.elim, fun h => h.elim⟩

open Silmaril.Wasm.SpecTec.Sim20 in
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree in
/-- **A `composite10T20` instance on a storing V1 program.** -/
theorem composite10T20_memStore (src : Silmaril.Wasm.V1.Execution.HostSemantics Empty)
    (tgt : HostSemantics Empty) :
    ∃ c', Silmaril.Wasm.Lime1.Execution.ToV2.Sim v1Cfg'.toLime c' ∧
      Relation.TransGen (Silmaril.Wasm.SpecTec.Sim.Round6.Reading.SStepB
        (StoreFix.simEnv20T (Whole.storeB Silmaril.Wasm.Lime1.Execution.v2Profile)))
        (configV Empty.elim memStoreCfg2) (configV Empty.elim c') :=
  composite10T20 Empty Empty.elim src tgt _ _ (hostCompatible_empty src tgt)
    (ElseAgree.fwd20T_goodT20' Empty.elim tgt) v1Cfg v1Cfg' memStoreCfg2 (v1_step src) v1_sim
    (runGood_memStore tgt)

end Silmaril.Wasm.SpecTec.Sim20.StoreRun
