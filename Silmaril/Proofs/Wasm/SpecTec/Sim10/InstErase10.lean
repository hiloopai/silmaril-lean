module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.SegFree

/-!
# `Task.storeOkErase10` holds: iterated V1 instantiation, unconditionally

`InstIter10` reduced iterated instantiation to `Task.storeOkErase10`: a valid Core store `S`
erasing to the image of a V1 store makes the image valid. It holds:

* a typed global keeps its type under `GlobalInst.erase` (`globalInst_erase_eq`), so erasure
  keeps the globals of a valid store;
* reference, value and external-address typing move from `S` to `erase S`
  (`refOk_erase`, `valOk_erase`, `externAddrOk_erase`): erasure keeps every function type and
  every aggregate; immutable reachability moves back (`immutReachable_erase`);
* a typed module instance stays typed after erasure, at its context with no segments
  (`moduleInstOk_erase`);
* a function instance of `S` whose code is segment-free stays typed after erasure
  (`funcInstOk_erase`, through `SegFree.segs_FuncOk`), and the functions of the image of a V1
  store are segment-free (`segFree_coreStore10`);
* **`storeOk_erase`**, **`storeOkErase10`**: so `StoreOk (erase S)`, and the Task.

With it, **`reach10_okU`** and **`wholeRunFwd10InvRU`**/`wholeRunFwd10InvRTU`: round 4's
`Task.wholeRunFwd10Inv` at every store reached from the empty store by V1 instantiations under
`InstBoundsG` (globals allowed), with no Core hypothesis left.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstG

open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim10 Silmaril.Wasm.SpecTec.Sim10.Valid
open Silmaril.Wasm.Execution.Core (Store StoreOk RefOk ValOk FieldValOk ExternAddrOk
  ImmutReachable ModuleInstOk FuncInstOk GlobalInstOk FuncInst)
open Silmaril.Wasm.SpecTec.Sim10.SegFree (segFreeL withSegs segs_FuncOk segFreeL_toCore)

variable {H : Type}

local notation "erase" => Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase
local notation "eraseM" => Silmaril.Wasm.Lime1.Execution.ToCore.ModuleInst.erase

/-! ## Globals -/

/-- A typed global is unchanged by `GlobalInst.erase`. -/
theorem globalInst_erase_eq {S : Store H} {g : Silmaril.Wasm.Execution.Core.GlobalInst}
    (h : GlobalInstOk S g) : Lime1.Execution.ToCore.GlobalInst.erase g = g := by
  rcases g with ⟨⟨mu, t⟩, v⟩
  obtain ⟨-, hv⟩ := h
  cases v with
  | num n =>
    cases hv
    rfl
  | _ => rfl

/-- **Erasure keeps the globals of a valid store.** -/
theorem erase_globals {S : Store H} (hS : StoreOk S) : (erase S).globals = S.globals := by
  change S.globals.map Lime1.Execution.ToCore.GlobalInst.erase = S.globals
  conv => rhs; rw [← List.map_id S.globals]
  exact List.map_congr_left fun g hg => globalInst_erase_eq (hS.globals g hg)

/-! ## Typing moves to the erased store -/

theorem funcs_erase_get {S : Store H} {a : Nat} {fi : FuncInst H} (h : S.funcs[a]? = some fi) :
    (erase S).funcs[a]? = some { fi with module := eraseM fi.module } := by
  simp [Lime1.Execution.ToCore.Store.erase, h]

theorem refOk_erase {S : Store H} {r : Silmaril.Wasm.Execution.Core.Ref}
    {rt : Silmaril.Wasm.Validation.CRefType} (h : RefOk S r rt) : RefOk (erase S) r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | func h =>
    have h' := RefOk.func (s := erase S) (funcs_erase_get h)
    exact h'
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem valOk_erase {S : Store H} {v : Silmaril.Wasm.Execution.Core.Val}
    {t : Silmaril.Wasm.Validation.CValType} (h : ValOk S v t) : ValOk (erase S) v t := by
  cases h with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref h => exact .ref (refOk_erase h)

theorem fieldValOk_erase {S : Store H} {v : Silmaril.Wasm.Execution.Core.FieldVal}
    {t : Silmaril.Wasm.Validation.CStorageType} (h : FieldValOk S v t) :
    FieldValOk (erase S) v t := by
  cases h with
  | val h => exact .val (valOk_erase h)
  | pack p b => exact .pack p b

theorem externAddrOk_erase {S : Store H} (hS : StoreOk S)
    {xa : Silmaril.Wasm.Execution.Core.ExternAddr} {xt : Silmaril.Wasm.Validation.CExternType}
    (h : ExternAddrOk S xa xt) : ExternAddrOk (erase S) xa xt := by
  induction h with
  | tag h => exact .tag h
  | global h => exact .global (by rw [erase_globals hS]; exact h)
  | mem h => exact .mem h
  | table h => exact .table h
  | func h =>
    have h' := ExternAddrOk.func (s := erase S) (funcs_erase_get h)
    exact h'
  | sub _ hok hs ih => exact .sub ih hok hs

theorem immutReachable_erase {S : Store H} {a b : Silmaril.Wasm.Execution.Core.FieldVal}
    (h : ImmutReachable (erase S) a b) : ImmutReachable S a b := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs he hi hfv => exact .refStruct hs he hi hfv
  | refArray hs he hfv => exact .refArray hs he hfv
  | refExn hs hv => exact .refExn hs hv
  | refExtern r => exact .refExtern r

/-! ## Module and function instances -/

/-- **A typed module instance stays typed after erasure**, at its context without segments. -/
theorem moduleInstOk_erase {S : Store H} (hS : StoreOk S)
    {mi : Silmaril.Wasm.Execution.Core.ModuleInst} {C : Silmaril.Wasm.Validation.Context}
    (h : ModuleInstOk S mi C) : ModuleInstOk (erase S) (eraseM mi) (withSegs C [] []) := by
  cases h with
  | mk htypes htags hglobals hfuncs hmems htables _ _ hexports hdisjoint hexportAddrs hk =>
    exact .mk htypes (htags.imp fun _ _ h => externAddrOk_erase hS h)
      (hglobals.imp fun _ _ h => externAddrOk_erase hS h)
      (hfuncs.imp fun _ _ h => externAddrOk_erase hS h)
      (hmems.imp fun _ _ h => externAddrOk_erase hS h)
      (htables.imp fun _ _ h => externAddrOk_erase hS h) (fun _ h => absurd h List.not_mem_nil)
      .nil (fun xi hxi => let ⟨xt, h⟩ := hexports xi hxi; ⟨xt, externAddrOk_erase hS h⟩)
      hdisjoint hexportAddrs hk

/-- **A function instance with segment-free code stays typed after erasure.** -/
theorem funcInstOk_erase {S : Store H} (hS : StoreOk S) {fi : FuncInst H} (h : FuncInstOk S fi)
    (hsf : ∀ code, fi.code = .wasm code → segFreeL code.body = true) :
    FuncInstOk (erase S) { fi with module := eraseM fi.module } := by
  cases h with
  | wasm hdt hm hcode hf hs =>
    exact .wasm hdt (moduleInstOk_erase hS hm) hcode (segs_FuncOk hf [] [] (hsf _ hcode)) hs
  | host hdt he hcode => exact .host hdt he hcode

/-- **The functions of the image of a V1 store are segment-free.** -/
theorem segFree_coreStore10 {s : V1.Execution.Store H} {fi : FuncInst H}
    (h : fi ∈ (coreStore10 s).funcs) :
    ∀ code, fi.code = .wasm code → segFreeL code.body = true := by
  intro code hcode
  simp only [coreStore10, Execution.Runtime.Store.toCore, List.mem_map] at h
  obtain ⟨g, -, rfl⟩ := h
  cases g with
  | wasm t m c =>
    simp only [Execution.Runtime.FuncInst.toCore, Silmaril.Wasm.Execution.Core.FuncCode.wasm.injEq]
      at hcode
    subst hcode
    exact segFreeL_toCore c.body
  | host t hh => simp [Execution.Runtime.FuncInst.toCore] at hcode

/-! ## The store -/

theorem funcs_storeOk_erase {s : V1.Execution.Store H} {S : Store H} (hS : StoreOk S)
    (he : erase S = coreStore10 s) : ∀ fi' ∈ (erase S).funcs, FuncInstOk (erase S) fi' := by
  intro fi' h
  have hsf := segFree_coreStore10 (he ▸ h)
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 h
  exact funcInstOk_erase hS (hS.funcs fi hfi) hsf

theorem globals_storeOk_erase {S : Store H} (hS : StoreOk S) :
    ∀ gi ∈ (erase S).globals, GlobalInstOk (erase S) gi := by
  intro gi h
  rw [erase_globals hS] at h
  exact ⟨(hS.globals gi h).1, valOk_erase (hS.globals gi h).2⟩

/-- **A valid Core store erasing to the image of a V1 store makes the image valid.** -/
theorem storeOk_erase {s : V1.Execution.Store H} {S : Store H} (hS : StoreOk S)
    (he : erase S = coreStore10 s) : StoreOk (erase S) := by
  refine ⟨hS.tags, globals_storeOk_erase hS, hS.mems, fun ti h => ?_, funcs_storeOk_erase hS he,
    fun _ h => absurd h List.not_mem_nil, fun si h => ?_, fun ai h => ?_, fun e h => ?_,
    fun a ha hr => hS.acyclicStructs a ha (immutReachable_erase hr),
    fun a ha hr => hS.acyclicArrays a ha (immutReachable_erase hr),
    fun a ha hr => hS.acyclicExns a ha (immutReachable_erase hr),
    hS.structsClosed, hS.arraysClosed⟩
  · obtain ⟨h₁, h₂, h₃⟩ := hS.tables ti h
    exact ⟨h₁, h₂, fun r hr => refOk_erase (h₃ r hr)⟩
  · obtain ⟨fs, hE, hF⟩ := hS.structs si h
    exact ⟨fs, hE, hF.imp fun _ _ x => fieldValOk_erase x⟩
  · obtain ⟨ft, hE, hF⟩ := hS.arrays ai h
    exact ⟨ft, hE, fun fv hfv => fieldValOk_erase (hF fv hfv)⟩
  · obtain ⟨ti, ts, h₁, h₂, h₃⟩ := hS.exns e h
    exact ⟨ti, ts, h₁, h₂, h₃.imp fun _ _ x => valOk_erase x⟩

/-- **`Task.storeOkErase10` holds.** -/
theorem storeOkErase10 : Task.storeOkErase10 := fun _ _ _ hS he => he ▸ storeOk_erase hS he

/-! ## Iterated instantiation, unconditionally -/

/-- **Every store reached by V1 instantiations is fine.** -/
theorem reach10_okU {s : V1.Execution.Store H} (h : Reach10 s) : ReachOk10 s :=
  reach10_ok storeOkErase10 h

/-- **`Task.wholeRunFwd10Inv` at every store reached by V1 instantiations** (globals allowed,
from the empty store), with no Core hypothesis. -/
theorem wholeRunFwd10InvRU {hn : H → String} {host' : V1.Execution.HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {s : V1.Execution.Store H} (hR : Reach10 s)
    {args : List Execution.Runtime.Value} {a : Execution.Runtime.FuncAddr}
    {c' : V1.Execution.Config H}
    (hc : Typed10 (simEnv10 (Whole.fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value
      (args.map Execution.Runtime.Value.toCore))
    (h : V1.Execution.Steps host' (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (Whole.fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (Sim.Round6.Reading.SStepB (simEnv10 (Whole.fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') :=
  wholeRunFwd10InvR storeOkErase10 hR hc hinv h

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10InvRTU {hn : H → String} {host' : V1.Execution.HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {s : V1.Execution.Store H} (hR : Reach10 s)
    {args : List Execution.Runtime.Value} {a : Execution.Runtime.FuncAddr}
    {c' : V1.Execution.Config H}
    (hc : Typed10 (StoreFix.simEnv10T (Whole.fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value
      (args.map Execution.Runtime.Value.toCore))
    (h : V1.Execution.Steps host' (invokeCfg10 s args a) c') :
    Typed10 (StoreFix.simEnv10T (Whole.fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (Sim.Round6.Reading.SStepB (StoreFix.simEnv10T (Whole.fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') :=
  wholeRunFwd10InvRT storeOkErase10 hR hc hinv h

end Silmaril.Wasm.SpecTec.Sim10.InstG
