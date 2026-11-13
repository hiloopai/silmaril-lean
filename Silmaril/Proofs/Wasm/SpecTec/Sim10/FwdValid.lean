module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.GSetRun

/-!
# The forward 1.0 run without the `GSetOk` hypothesis

an earlier `Task.wholeRunFwd10` assumed `GSetOk` at every configuration of the run. `GSetRun`
derives it from `CoreTyped10`, so the hypothesis can be dropped:

* **`Task.wholeRunFwd10C`** (frozen, proved by `wholeRunFwd10C`): from a configuration whose image is
  typed, whose code is `Plain10`, whose memories are aligned and which is `CoreTyped10`, every V1
  run is a run of the wasm-1.0 script between the images.
* **`Task.wholeRunFwd10Inv`** (frozen, proved by `wholeRunFwd10Inv`): the same from an invocation
  `val* (invoke a)` in the empty frame. The hypotheses are on the store and the arguments only:
  the image is typed (IL `config`), the Core image of the store is valid (`StoreOk`, Core 3.0's
  `Store_ok`), the arguments fit (`InvokeOk`, the premise of `$invoke`), and the store satisfies the
  simulation's `StoreWF`. `Plain10` holds at an invocation (`plain10_invoke`), and `MemsAligned10`
  follows from `StoreOk` (`memsAligned10_of_storeOk`: a valid memory has a whole number of pages,
  at most `2^16`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Valid

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10 Plain10 MemsAligned10 MemAligned10 wholeRunFwd10
  noHost10_of_typed typedV_state_of_typed10 plain10_invoke)

variable {H : Type}

/-! ## Alignment from Core validity -/

/-- **A memory whose Core image is valid is aligned.** -/
theorem memAligned10_of_ok {m : Execution.Runtime.MemInst}
    (h : Execution.Core.MemInstOk m.toCore) : MemAligned10 m := by
  obtain ⟨hv, hsz⟩ := h
  have hmin : (Fin.ofNat (2 ^ 64) (m.data.size / Execution.Memory.pageSize)).val ≤ 2 ^ 16 := hv.1
  have hsz' : m.data.size =
      (Fin.ofNat (2 ^ 64) (m.data.size / Execution.Memory.pageSize)).val *
        Execution.Memory.pageSize := hsz
  refine ⟨?_, ?_⟩
  · rw [hsz']
    exact Nat.mul_mod_left _ _
  · simp only [Execution.Memory.size]
    rw [hsz', Nat.mul_div_cancel _ (by decide)]
    omega

/-- **The memories of a store whose Core image is valid are aligned.** -/
theorem memsAligned10_of_storeOk {s : Store H}
    (hs : Execution.Core.StoreOk (coreStore10 s)) : MemsAligned10 s := by
  intro m hm
  apply memAligned10_of_ok
  apply hs.mems
  simp only [coreStore10, Execution.Runtime.Store.toCore, List.mem_map]
  exact ⟨m, hm, rfl⟩

/-! ## The run from a `CoreTyped10` configuration -/

/-- **The forward 1.0 half along a V1 run from a `CoreTyped10` configuration** (frozen; proved
below). -/
def Task.wholeRunFwd10C : Prop :=
  ∀ (H : Type) (hn : H → String) (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice)
    (c c' : Config H), Typed10 (simEnv10 (fwdB10 nd r)) hn c → Plain10 c.code →
    MemsAligned10 c.store → CoreTyped10 c → Steps host c c' →
      Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
        Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r))) (configV hn c) (configV hn c')

/-- **`Task.wholeRunFwd10C` holds**: an earlier run theorem, with `GSetOk` from `gsetOk_steps`. -/
theorem wholeRunFwd10C : Task.wholeRunFwd10C := by
  intro H hn host nd r c c' hc hpl hal hcore h
  have hnh := noHost10_of_typed (typedV_state_of_typed10 hc)
  exact wholeRunFwd10 H hn host nd r c c' hc hpl hal (fun d hd => gsetOk_steps hd hnh hcore) h

/-! ## The run from an invocation -/

/-- **The forward 1.0 half along every V1 run from an invocation** (frozen; proved below). -/
def Task.wholeRunFwd10Inv : Prop :=
  ∀ (H : Type) (hn : H → String) (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice)
    (s : Store H) (args : List Execution.Runtime.Value) (a : Execution.Runtime.FuncAddr)
    (c' : Config H),
    Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 s args a) →
    Execution.Core.StoreOk (coreStore10 s) →
    Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Execution.Runtime.Value.toCore) →
    Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime) →
    Steps host (invokeCfg10 s args a) c' →
      Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
        Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
          (configV hn (invokeCfg10 s args a)) (configV hn c')

/-- **`Task.wholeRunFwd10Inv` holds.** -/
theorem wholeRunFwd10Inv : Task.wholeRunFwd10Inv := by
  intro H hn host nd r s args a c' hc hs hinv hwf h
  exact wholeRunFwd10C H hn host nd r _ c' hc (plain10_invoke args a)
    (memsAligned10_of_storeOk hs) (coreTyped10_invoke hs hinv hwf) h

end Silmaril.Wasm.SpecTec.Sim10.Valid
