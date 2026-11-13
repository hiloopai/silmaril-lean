module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstGlob10

/-!
# Iterated V1 instantiation, reduced to one Core statement

`instantiation_core10G` needs Core `StoreOk` of the image of the store **before** the
instantiation, and gives only a valid Core store `S` **erasing** to the image of the store after
it (`ToCore.Store.erase`: segment instances dropped, module instances' segment addresses
dropped). To instantiate again, `StoreOk` of the image itself is needed.

* **`Task.storeOkErase10`**: a valid Core store erasing to the image of a V1 store makes that
  image valid. It is stated here and **proved** in `InstErase10` (`storeOkErase10`): erasure
  keeps every function, table, memory and global type, and the only typing premises it removes
  are those of segment instructions, which the image of 1.0 code never contains (`SegFree`).
* `erase_coreStore10`: erasure is the identity on images of V1 stores (proved).
* `Reach10 s`: `s` is reached from the empty store by V1 instantiations, each under
  `InstBoundsG` (globals allowed).
* **`reach10_ok`** (under `Task.storeOkErase10`): every reached store has no host function,
  `StoreOk10`, a valid Core image and the simulation's `StoreWF`.
* **`wholeRunFwd10InvR`**, **`wholeRunFwd10InvRT`** (under `Task.storeOkErase10`): round 4's
  `Task.wholeRunFwd10Inv` and its `simEnv10T` form at every reached store.
* `reach10_one`: unconditionally, one instantiation from the empty store is covered
  (`wholeRunFwd10InvG_empty`); `InstErase10` removes the Task
  hypothesis (`reach10_okU`, `wholeRunFwd10InvRU`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstG

open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps Instantiation)
open Silmaril.Wasm.Execution.Runtime (Value ExternVal)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10 NoHost10 plain10_invoke)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10 Silmaril.Wasm.SpecTec.Sim10.Valid
open Silmaril.Wasm.SpecTec.Sim10.Valid (memsAligned10_of_erase coreTyped10_invoke_erase
  invokeOk_erase storeOk_coreStore10_empty storeWF_empty10 storeOk10_instantiation)

local notation "erase" => Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase

/-- **Frozen target** (proved: `InstErase10.storeOkErase10`): a valid Core store erasing to the image of a V1 store makes the image
valid. See the module docstring for why it is expected and what is missing. -/
def Task.storeOkErase10 : Prop :=
  ∀ (H : Type) (s : Store H) (S : Execution.Core.Store H), Execution.Core.StoreOk S →
    erase S = coreStore10 s → Execution.Core.StoreOk (coreStore10 s)

variable {H : Type}

/-- **Erasure is the identity on images of V1 stores.** -/
theorem erase_coreStore10 (s : Store H) : erase (coreStore10 s) = coreStore10 s := by
  simp [Lime1.Execution.ToCore.Store.erase, coreStore10, Execution.Runtime.Store.toCore,
    Lime1.Execution.ToCore.ModuleInst.erase, Lime1.Execution.ToCore.GlobalInst.erase,
    Execution.Runtime.GlobalInst.toCore, Execution.Runtime.Value.toCore, List.map_map,
    Function.comp_def]
  intro fi _
  cases fi <;> rfl

/-- **Stores reached from the empty store by V1 instantiations** under `InstBoundsG`. -/
inductive Reach10 : Store H → Prop where
  | empty : Reach10 {}
  | inst {host : HostSemantics H} {before after : Store H} {m : V1.Module}
      {imports : List ExternVal} {module : Execution.Runtime.ModuleInst}
      {outcome : Execution.Runtime.Result} :
      Reach10 before → Instantiation host before m imports after module outcome →
      InstBoundsG (before.mapCode V1.Func.toLime) m.toLime → Reach10 after

/-- What a reached store satisfies. -/
structure ReachOk10 (s : Store H) : Prop where
  noHost : NoHost10 s
  storeOk10 : StoreOk10 s
  core : Execution.Core.StoreOk (coreStore10 s)
  wf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime)

/-- **Every reached store is fine**, under `Task.storeOkErase10`. -/
theorem reach10_ok (hT : Task.storeOkErase10) {s : Store H} (h : Reach10 s) : ReachOk10 s := by
  induction h with
  | empty =>
    exact ⟨storeOk10_empty.1, storeOk10_empty.2, storeOk_coreStore10_empty, storeWF_empty10⟩
  | inst _ hI hb ih =>
    obtain ⟨hnh, hs⟩ := storeOk10_instantiation hI ih.noHost ih.storeOk10
    obtain ⟨⟨S, hS, he⟩, hwf⟩ := instOk10_of_instantiationG hI ih.noHost ih.storeOk10 hb ih.core
    exact ⟨hnh, hs, hT H _ S hS he, hwf⟩

/-- **`Task.wholeRunFwd10Inv` at every reached store**, under `Task.storeOkErase10`. -/
theorem wholeRunFwd10InvR (hT : Task.storeOkErase10) {hn : H → String}
    {host' : HostSemantics H} {nd : Bool} {r : RelaxedChoice} {s : Store H} (hR : Reach10 s)
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  have ok := reach10_ok hT hR
  have he := erase_coreStore10 s
  exact wholeRunFwd10C H hn host' nd r _ c' hc (plain10_invoke args a)
    (memsAligned10_of_erase ok.core he)
    (coreTyped10_invoke_erase ok.core he (invokeOk_erase he hinv) ok.wf) h

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10InvRT (hT : Task.storeOkErase10) {hn : H → String}
    {host' : HostSemantics H} {nd : Bool} {r : RelaxedChoice} {s : Store H} (hR : Reach10 s)
    {args : List Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (h : Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') := by
  have ok := reach10_ok hT hR
  have he := erase_coreStore10 s
  exact wholeRunFwd10CT hc (plain10_invoke args a) (memsAligned10_of_erase ok.core he)
    (coreTyped10_invoke_erase ok.core he (invokeOk_erase he hinv) ok.wf) h

/-- One instantiation from the empty store is reached. -/
theorem reach10_one {host : HostSemantics H} {after : Store H} {m : V1.Module}
    {module : Execution.Runtime.ModuleInst} {outcome : Execution.Runtime.Result}
    (hI : Instantiation host {} m [] after module outcome) (hb : ModBoundsG m) : Reach10 after :=
  .inst .empty hI (boundsG_empty hb)

end Silmaril.Wasm.SpecTec.Sim10.InstG
