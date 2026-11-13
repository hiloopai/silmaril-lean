module

public import Silmaril.Raw.Wasm.Versions.V2.ToCore.Sim.Common

@[expose] public section

/-! # Step simulation: the state-changing and context rules of `Step`

One lemma per constructor of `Silmaril.Wasm.V2.Execution.Step` other than
`Step.pure` and `Step.read` (those dispatch to `Sim/Pure.lean` and
`Sim/Read.lean`).

## Which rules are lock-step

All of them, in the sense that one 2.0 step is one Core 3.0 step:

| 2.0 | Core 3.0 |
| --- | --- |
| `ctxt-instrs`, `ctxt-label`, `ctxt-frame` | the same three, lifted to `TransGen` |
| `local.set`, `global.set` | `Step.variable` |
| `table.set-*`, `table.grow-*`, `elem.drop` | `Step.table` |
| `store-*`, `vstore*`, `memory.grow-*`, `data.drop` | `Step.memory` |
| `callAddrHost`, `callAddrHostDiv` (deviation 3 of `Step.lean`) | `Step.callRefHost`, `Step.callRefHostDiv` |

The host rules are the only ones that need `HostCompatible`; the `Diverges`
rule steps to itself on both sides, which is what makes `Diverges.toCore`
work.

## Three things the Core side needs that the 2.0 rule does not state

1. **The address.** `Sim/Common.lean`'s `bridge_table` and friends produce the
   Core lookup only up to an *existential* address, while every rule here writes
   the store at the address its own premise names. `bridgeTable`, `bridgeMem`,
   `bridgeGlobal`, `bridgeElem` and `bridgeData` below are the address-aware
   forms, and `toCore_setTableInst`, … are the matching update lemmas: a 2.0
   store update maps to the corresponding Core update at the *same* address.
   Core's `setGlobal`, `setElem` and `setData` use `List.modify` where 2.0 uses
   `List.set`; `modify_eq_set` reconciles the two at an allocated address.

2. **`StoreWF`.** `Sim` carries `ConfigWF`, so every rule that writes the store
   must re-establish it. Writing a table entry or a memory range preserves the
   length/size bounds; `$growtable`'s own premise gives `|refs| + n < 2^32`.
   `memory.grow` is the one case that needs more than its own premises:
   `$growmemory` (`5-runtime-aux:126-131`) bounds the result in *pages* while
   `StoreWF` bounds it in *bytes*, so re-establishing `|mi'.BYTES| <= 2^32`
   needs `|mi.BYTES| % 64Ki = 0`. That is exactly `StoreWF`'s third conjunct
   (`V2/ToCore/Runtime.lean`), so `state_memoryGrowSucceed` reads it off
   `sim_wf` rather than taking it as a hypothesis, and `memGrow_align` carries
   it forward to the grown memory.

3. **`Admin.norm`.** `Sim` relates the Core code to the image of the 2.0 code
   only *up to* normalisation, so the two host rules must step from an
   un-normalised `CALL_REF`: `.callRefType d` is **not** `Rigid`, and
   `catchUp` therefore cannot be used on it. `norm_eq_callRefType` says the Core
   code holds either `CALL_REF_TYPE d` or a source `CALL_REF y`, and Core's
   `Step/call_ref-hostfunc-*` accepts both through `Admin.IsCallRef`.

## `Step/ctxt-instrs` and the frame's module

`state_ctxtInstrs` leaves the trailing code `rest` untouched, so the Core image
of `rest` must still be correct *after* the inner step — both after the store
changes (`listToCore_storeExt`, using `StoreExt` and `Admin.listWF`) and after
the frame changes. The latter needs `cf'.module.types = cf.module.types`, which
is `cstep_module`: no Core 3.0 reduction ever changes the current frame's module
instance (`Step/local.set` rewrites only `LOCALS`).

## `Step/local.set`

`Step/local.set` (`8-reduction:380`) is `$with_local(z, x, val)`, and SpecTec's
array update is **partial** (`5-runtime-aux:104`), so `Step.localSet` carries
`hx : x.toNat < |f.LOCALS|` — exactly the premise Core 3.0's
`VariableStep.localSet` carries (`Execution/Core/Step/Variable.lean:26`), where
locals are `Option Val`. `state_localSet` passes it straight through. Without it
the simulation would be **false**: Lean's `List.set` is the identity out of
range, so the 2.0 machine would step where the Core machine is stuck.
-/

namespace Silmaril.Wasm.V2.Execution.ToCoreSim

open Silmaril.Wasm.Numerics (Profile V128)
open Silmaril.Wasm.Execution.Memory (Bytes readBytes pageSize)
open Silmaril.Wasm.V2.Execution.ToCore

variable {H : Type} {P : Profile} {tgt : CHostSemantics H} {s : Store H} {f : Frame}

/-! ## Shared machinery for the rules that write the store -/

/-! ## The address-aware store/frame bridge -/

theorem bridgeTable {cs : CStore H} {cf : CFrame} {x : TableIdx} {a : TableAddr}
    {ti : TableInst} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (ha : f.module.tableAddr? x = some a)
    (ht : s.tableInst? a = some ti) : cs.table? cf x = some (a, ti.toCore) := by
  simp only [ModuleInst.tableAddr?] at ha
  simp only [Store.tableInst?] at ht
  simp [Silmaril.Wasm.Execution.Core.Store.table?, erase_module_tables hfr, ha,
    erase_tables hst, List.getElem?_map, ht]

theorem bridgeMem {cs : CStore H} {cf : CFrame} {x : MemIdx} {a : MemAddr}
    {mi : MemInst} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (ha : f.module.memAddr? x = some a)
    (hm : s.memInst? a = some mi) : cs.mem? cf x = some (a, mi.toCore) := by
  simp only [ModuleInst.memAddr?] at ha
  simp only [Store.memInst?] at hm
  simp [Silmaril.Wasm.Execution.Core.Store.mem?, erase_module_mems hfr, ha,
    erase_mems hst, List.getElem?_map, hm]

theorem bridgeGlobal {cs : CStore H} {cf : CFrame} {x : GlobalIdx} {a : GlobalAddr}
    {gi : GlobalInst} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (ha : f.module.globalAddr? x = some a)
    (hg : s.globalInst? a = some gi) : cs.global? cf x = some (a, gi.toCore) := by
  simp only [ModuleInst.globalAddr?] at ha
  simp only [Store.globalInst?] at hg
  simp [Silmaril.Wasm.Execution.Core.Store.global?, erase_module_globals hfr, ha,
    erase_globals hst, List.getElem?_map, hg]

theorem bridgeElem {cs : CStore H} {cf : CFrame} {x : ElemIdx} {a : ElemAddr}
    {ei : ElemInst} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (ha : f.module.elemAddr? x = some a)
    (he : s.elemInst? a = some ei) : cs.elem? cf x = some (a, ei.toCore) := by
  simp only [ModuleInst.elemAddr?] at ha
  simp only [Store.elemInst?] at he
  simp [Silmaril.Wasm.Execution.Core.Store.elem?, erase_module_elems hfr, ha,
    erase_elems hst, List.getElem?_map, he]

theorem bridgeData {cs : CStore H} {cf : CFrame} {x : DataIdx} {a : DataAddr}
    {di : DataInst} (hst : s.toCore = some (ToCore.Store.erase cs))
    (hfr : f.toCore = ToCore.Frame.erase cf) (ha : f.module.dataAddr? x = some a)
    (hd : s.dataInst? a = some di) : cs.data? cf x = some (a, di.toCore) := by
  simp only [ModuleInst.dataAddr?] at ha
  simp only [Store.dataInst?] at hd
  simp [Silmaril.Wasm.Execution.Core.Store.data?, erase_module_datas hfr, ha,
    erase_datas hst, List.getElem?_map, hd]

/-! ## Store updates transfer -/

/-- The generic shape: a 2.0 store update whose image agrees component by
component with a Core 3.0 store update, leaving the function instances alone. -/
theorem toCore_update {s' : Store H} {cs cs' : CStore H}
    (h : s.toCore = some (ToCore.Store.erase cs))
    (hfu : s'.funcs = s.funcs) (hcfu : cs'.funcs = cs.funcs)
    (hg : cs'.globals = s'.globals.map GlobalInst.toCore)
    (hm : cs'.mems = s'.mems.map MemInst.toCore)
    (ht : cs'.tables = s'.tables.map TableInst.toCore)
    (hd : cs'.datas = s'.datas.map DataInst.toCore)
    (he : cs'.elems = s'.elems.map ElemInst.toCore) :
    s'.toCore = some (ToCore.Store.erase cs') := by
  simp only [Store.toCore, Option.map_eq_some_iff] at h ⊢
  obtain ⟨fs, hfs, hE⟩ := h
  refine ⟨fs, by rw [hfu]; exact hfs, ?_⟩
  have hfunc : (ToCore.Store.erase cs).funcs = fs := by rw [← hE]
  simp only [ToCore.Store.erase] at hfunc ⊢
  rw [hg, hm, ht, hd, he, hcfu, hfunc]


/-! ## Concrete store updates -/

theorem modify_eq_set {α : Type} {l : List α} {a : Nat} {x : α} (h : l[a]? = some x)
    (g : α → α) : l.modify a g = l.set a (g x) := by
  obtain ⟨hlt, hx⟩ := List.getElem?_eq_some_iff.mp h
  refine List.ext_getElem? fun j => ?_
  rw [List.getElem?_modify, List.getElem?_set]
  by_cases hj : a = j
  · subst hj; simp [hlt, hx]
  · simp [hj]

theorem toCore_setTableInst {cs : CStore H} {a : TableAddr} {ti : TableInst}
    (h : s.toCore = some (ToCore.Store.erase cs)) :
    (s.setTableInst a ti).toCore = some (ToCore.Store.erase (cs.setTable a ti.toCore)) := by
  refine toCore_update h rfl rfl ?_ ?_ ?_ ?_ ?_
  · show cs.globals = s.globals.map GlobalInst.toCore; exact erase_globals h
  · show cs.mems = s.mems.map MemInst.toCore; exact erase_mems h
  · show cs.tables.set a ti.toCore = (s.tables.set a ti).map TableInst.toCore
    rw [erase_tables h, List.map_set]
  · show cs.datas = s.datas.map DataInst.toCore; exact erase_datas h
  · show cs.elems = s.elems.map ElemInst.toCore; exact erase_elems h

theorem toCore_setMemInst {cs : CStore H} {a : MemAddr} {mi : MemInst}
    (h : s.toCore = some (ToCore.Store.erase cs)) :
    (s.setMemInst a mi).toCore = some (ToCore.Store.erase (cs.setMem a mi.toCore)) := by
  refine toCore_update h rfl rfl ?_ ?_ ?_ ?_ ?_
  · show cs.globals = s.globals.map GlobalInst.toCore; exact erase_globals h
  · show cs.mems.set a mi.toCore = (s.mems.set a mi).map MemInst.toCore
    rw [erase_mems h, List.map_set]
  · show cs.tables = s.tables.map TableInst.toCore; exact erase_tables h
  · show cs.datas = s.datas.map DataInst.toCore; exact erase_datas h
  · show cs.elems = s.elems.map ElemInst.toCore; exact erase_elems h

theorem toCore_setGlobalInst {cs : CStore H} {a : GlobalAddr} {gi : GlobalInst} {v : Val}
    (h : s.toCore = some (ToCore.Store.erase cs)) (hg : s.globalInst? a = some gi) :
    (s.setGlobalInst a { gi with value := v }).toCore =
      some (ToCore.Store.erase (cs.setGlobal a v.toCore)) := by
  have hcg : cs.globals[a]? = some gi.toCore := by
    rw [erase_globals h, List.getElem?_map, show s.globals[a]? = some gi from hg]; rfl
  refine toCore_update h rfl rfl ?_ ?_ ?_ ?_ ?_
  · show cs.globals.modify a _ = (s.globals.set a { gi with value := v }).map GlobalInst.toCore
    rw [modify_eq_set hcg, erase_globals h, List.map_set]
    rfl
  · show cs.mems = s.mems.map MemInst.toCore; exact erase_mems h
  · show cs.tables = s.tables.map TableInst.toCore; exact erase_tables h
  · show cs.datas = s.datas.map DataInst.toCore; exact erase_datas h
  · show cs.elems = s.elems.map ElemInst.toCore; exact erase_elems h

theorem toCore_setElemInst {cs : CStore H} {a : ElemAddr} {ei : ElemInst}
    (h : s.toCore = some (ToCore.Store.erase cs)) (he : s.elemInst? a = some ei) :
    (s.setElemInst a { ei with refs := [] }).toCore =
      some (ToCore.Store.erase (cs.setElem a [])) := by
  have hce : cs.elems[a]? = some ei.toCore := by
    rw [erase_elems h, List.getElem?_map, show s.elems[a]? = some ei from he]; rfl
  refine toCore_update h rfl rfl ?_ ?_ ?_ ?_ ?_
  · show cs.globals = s.globals.map GlobalInst.toCore; exact erase_globals h
  · show cs.mems = s.mems.map MemInst.toCore; exact erase_mems h
  · show cs.tables = s.tables.map TableInst.toCore; exact erase_tables h
  · show cs.datas = s.datas.map DataInst.toCore; exact erase_datas h
  · show cs.elems.modify a _ = (s.elems.set a { ei with refs := [] }).map ElemInst.toCore
    rw [modify_eq_set hce, erase_elems h, List.map_set]
    rfl

theorem toCore_setDataInst {cs : CStore H} {a : DataAddr} {di : DataInst}
    (h : s.toCore = some (ToCore.Store.erase cs)) (hd : s.dataInst? a = some di) :
    (s.setDataInst a ⟨ByteArray.empty⟩).toCore =
      some (ToCore.Store.erase (cs.setData a ByteArray.empty)) := by
  have hcd : cs.datas[a]? = some di.toCore := by
    rw [erase_datas h, List.getElem?_map, show s.datas[a]? = some di from hd]; rfl
  refine toCore_update h rfl rfl ?_ ?_ ?_ ?_ ?_
  · show cs.globals = s.globals.map GlobalInst.toCore; exact erase_globals h
  · show cs.mems = s.mems.map MemInst.toCore; exact erase_mems h
  · show cs.tables = s.tables.map TableInst.toCore; exact erase_tables h
  · show cs.datas.modify a _ = (s.datas.set a ⟨ByteArray.empty⟩).map DataInst.toCore
    rw [modify_eq_set hcd, erase_datas h, List.map_set]
    rfl
  · show cs.elems = s.elems.map ElemInst.toCore; exact erase_elems h

/-! ## Store well-formedness is preserved -/

theorem storeWF_setTableInst (hwf : StoreWF s) {a : TableAddr} {ti : TableInst}
    (hlen : ti.refs.length < 2 ^ 32) : StoreWF (s.setTableInst a ti) := by
  refine ⟨hwf.1, hwf.2.1, hwf.2.2.1, fun i t' hi => ?_⟩
  rw [show (s.setTableInst a ti).tables = s.tables.set a ti from rfl,
    List.getElem?_set] at hi
  split at hi
  · split at hi
    · cases hi; exact hlen
    · exact absurd hi (by simp)
  · exact hwf.2.2.2 i t' hi

theorem storeWF_setMemInst (hwf : StoreWF s) {a : MemAddr} {mi : MemInst}
    (hsz : mi.bytes.size ≤ 2 ^ 32)
    (halign : mi.bytes.size % Silmaril.Wasm.Execution.Memory.pageSize = 0) :
    StoreWF (s.setMemInst a mi) := by
  refine ⟨hwf.1, fun i m' hi => ?_, fun i m' hi => ?_, hwf.2.2.2⟩
  · rw [show (s.setMemInst a mi).mems = s.mems.set a mi from rfl, List.getElem?_set] at hi
    split at hi
    · split at hi
      · cases hi; exact hsz
      · exact absurd hi (by simp)
    · exact hwf.2.1 i m' hi
  rw [show (s.setMemInst a mi).mems = s.mems.set a mi from rfl, List.getElem?_set] at hi
  split at hi
  · split at hi
    · cases hi; exact halign
    · exact absurd hi (by simp)
  · exact hwf.2.2.1 i m' hi

theorem storeWF_setGlobalInst (hwf : StoreWF s) (a : GlobalAddr) (gi : GlobalInst) :
    StoreWF (s.setGlobalInst a gi) := hwf

theorem storeWF_setElemInst (hwf : StoreWF s) (a : ElemAddr) (ei : ElemInst) :
    StoreWF (s.setElemInst a ei) := hwf

theorem storeWF_setDataInst (hwf : StoreWF s) (a : DataAddr) (di : DataInst) :
    StoreWF (s.setDataInst a di) := hwf

/-! ## Frames -/

theorem toCore_setLocal {cf : CFrame} {x : LocalIdx} {v : Val}
    (hfr : f.toCore = ToCore.Frame.erase cf) :
    (f.setLocal x v).toCore = ToCore.Frame.erase (cf.setLocal x v.toCore) := by
  have hl := erase_locals hfr
  have hm : ToCore.ModuleInst.erase cf.module = f.module.toCore :=
    (congrArg (fun fr : CFrame => fr.module) hfr).symm
  show (⟨(f.locals.set x.toNat v).map (some ∘ Val.toCore), f.module.toCore⟩ : CFrame) = _
  show _ = (⟨cf.locals.set x.toNat (some v.toCore), ToCore.ModuleInst.erase cf.module⟩ : CFrame)
  rw [hm, hl, List.map_set]
  rfl

/-! ## Growth bounds -/

theorem tableGrow_length {ti ti' : TableInst} {n : Nat} {r : Ref}
    (hg : ti.grow? n r = some ti') : ti'.refs.length < 2 ^ 32 := by
  have hlen := TableInst.grow?_refs_length hg
  unfold TableInst.grow? at hg
  split at hg
  · rw [hlen]; omega
  · exact absurd hg (by simp)

theorem tableGrow_toCore {ti ti' : TableInst} {n : Nat} {r : Ref}
    (hg : ti.grow? n r = some ti') :
    (ti.toCore).grow? n r.toCore = some ti'.toCore := by
  unfold TableInst.grow? at hg
  split at hg
  · rename_i hc
    cases hg
    have hcond : (ti.toCore).refs.length + n ≤ 2 ^ (ti.toCore).type.address.width - 1 ∧
        ∀ j, (ti.toCore).type.limits.max = some j → (ti.toCore).refs.length + n ≤ j.val := by
      refine ⟨?_, ?_⟩
      · show (ti.refs.map Ref.toCore).length + n ≤ 2 ^ 32 - 1
        rw [List.length_map]; omega
      · intro j hj
        show (ti.refs.map Ref.toCore).length + n ≤ j.val
        rw [List.length_map]
        cases hmax : ti.type.limits.max with
        | none =>
          rw [show (ti.toCore).type.limits.max = none from by
            simp [TableInst.toCore, ToCore.tableToC, Limits.toCore, hmax]] at hj
          cases hj
        | some j₀ =>
          rw [show (ti.toCore).type.limits.max = some (widen32 j₀) from by
            simp [TableInst.toCore, ToCore.tableToC, Limits.toCore, hmax]] at hj
          cases hj
          simp only [hmax, Option.all_some, decide_eq_true_eq] at hc
          exact hc.2
    unfold Silmaril.Wasm.Execution.Core.TableInst.grow?
    simp only [ite_eq_left hcond]
    simp [TableInst.toCore, ToCore.tableToC, Limits.toCore, widen32, List.map_append,
      List.map_replicate, Fin.ext_iff]
    omega
  · exact absurd hg (by simp)

theorem memGrow_toCore {mi mi' : MemInst} {n : Nat} (hg : mi.grow? n = some mi') :
    (mi.toCore).grow? n = some mi'.toCore := by
  unfold MemInst.grow? at hg
  split at hg
  · rename_i hc
    cases hg
    have hcond : (mi.toCore).bytes.size / Silmaril.Wasm.Execution.Memory.pageSize + n ≤
          2 ^ ((mi.toCore).type.address.width - 16) ∧
        ∀ j, (mi.toCore).type.limits.max = some j →
          (mi.toCore).bytes.size / Silmaril.Wasm.Execution.Memory.pageSize + n ≤ j.val := by
      refine ⟨?_, ?_⟩
      · show mi.bytes.size / pageSize + n ≤ 2 ^ (32 - 16)
        exact hc.1
      · intro j hj
        show mi.bytes.size / pageSize + n ≤ j.val
        cases hmax : mi.type.limits.max with
        | none =>
          rw [show (mi.toCore).type.limits.max = none from by
            simp [MemInst.toCore, MemoryType.toCore, Limits.toCore, hmax]] at hj
          cases hj
        | some j₀ =>
          rw [show (mi.toCore).type.limits.max = some (widen32 j₀) from by
            simp [MemInst.toCore, MemoryType.toCore, Limits.toCore, hmax]] at hj
          cases hj
          simp only [hmax, Option.all_some, decide_eq_true_eq] at hc
          exact hc.2
    unfold Silmaril.Wasm.Execution.Core.MemInst.grow?
    simp only [ite_eq_left hcond]
    simp [MemInst.toCore, MemoryType.toCore, Limits.toCore, widen32, Fin.ext_iff]
    omega
  · exact absurd hg (by simp)

/-! ## Stability under a store extension -/

theorem funcDefType_storeExt {s s' : Store H} (hext : StoreExt s s') {a : FuncAddr}
    (h : a < s.funcs.length) : s'.funcDefType a = s.funcDefType a := by
  simp only [Store.funcDefType, ListExt.map_getElem? hext (g := FuncType.toDefType) h]

mutual
theorem WF_storeExt {s s' : Store H} (hext : StoreExt s s') :
    (a : Admin) → Admin.WF s a → Admin.WF s' a
  | .plain _, _ => by simp
  | .refFuncAddr _, _ => by simp
  | .refHostAddr _, _ => by simp
  | .callAddr b, h => by
      simp only [WF_callAddr] at h ⊢
      exact ListExt.lt hext h
  | .label _ _ body, h => by
      simp only [WF_label] at h ⊢
      exact listWF_storeExt hext body h
  | .frame _ fr body, h => by
      simp only [WF_frame] at h ⊢
      exact ⟨StoreExt.modWF hext h.1, listWF_storeExt hext body h.2⟩
  | .trap, _ => by simp

theorem listWF_storeExt {s s' : Store H} (hext : StoreExt s s') :
    (l : List Admin) → Admin.listWF s l → Admin.listWF s' l
  | [], _ => by simp
  | a :: as, h => by
      simp only [listWF_cons'] at h ⊢
      exact ⟨WF_storeExt hext a h.1, listWF_storeExt hext as h.2⟩
end

mutual
theorem toCore_storeExt {s s' : Store H} (hext : StoreExt s s') :
    (a : Admin) → Admin.WF s a → Admin.toCore s' a = Admin.toCore s a
  | .plain _, _ => rfl
  | .refFuncAddr _, _ => rfl
  | .refHostAddr _, _ => rfl
  | .callAddr b, h => by
      simp only [WF_callAddr] at h
      simp only [Admin.callAddr_toCore, funcDefType_storeExt hext h]
  | .label _ _ body, h => by
      simp only [WF_label] at h
      simp only [Admin.label_toCore, listToCore_storeExt hext body h]
  | .frame _ _ body, h => by
      simp only [WF_frame] at h
      simp only [Admin.frame_toCore, listToCore_storeExt hext body h.2]
  | .trap, _ => rfl

theorem listToCore_storeExt {s s' : Store H} (hext : StoreExt s s') :
    (l : List Admin) → Admin.listWF s l → Admin.listToCore s' l = Admin.listToCore s l
  | [], _ => rfl
  | a :: as, h => by
      simp only [listWF_cons'] at h
      simp only [Admin.listToCore_cons, toCore_storeExt hext a h.1,
        listToCore_storeExt hext as h.2]
end

theorem toCore_ne_nil {s : Store H} {a : Admin} {l : List CAdmin}
    (h : Admin.toCore s a = some l) : l ≠ [] := by
  rintro rfl
  cases a <;>
    simp [Admin.toCore, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h

theorem listToCore_ne_nil {s : Store H} {l : List Admin} {L : List CAdmin}
    (hne : l ≠ []) (h : Admin.listToCore s l = some L) : L ≠ [] := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a as =>
    simp only [Admin.listToCore_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, -, rfl⟩ := h
    simp only [ne_eq, List.append_eq_nil_iff, not_and]
    exact fun h0 => absurd h0 (toCore_ne_nil hx)

/-! ## Core 3.0 reduction never changes the current module instance -/

theorem cstep_module {host : CHostSemantics H} {a b : CConfig H}
    (h : Silmaril.Wasm.Execution.Core.Step P host a b) : b.frame.module = a.frame.module := by
  induction h with
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | «variable» h => cases h <;> rfl
  | table h => cases h <;> rfl
  | memory h => cases h <;> rfl
  | reference h => cases h <;> rfl
  | aggregate h => cases h <;> rfl
  | _ => rfl

theorem cplus_module {tgt : CHostSemantics H} {a b : CConfig H} (h : CPlus P tgt a b) :
    b.frame.module = a.frame.module := by
  induction h with
  | single h => exact cstep_module h
  | tail _ h ih => exact (cstep_module h).trans ih

theorem listToCore_append_inv {s : Store H} :
    (l₁ : List Admin) → {l₂ : List Admin} → {L : List CAdmin} →
      Admin.listToCore s (l₁ ++ l₂) = some L →
      ∃ L₁ L₂, Admin.listToCore s l₁ = some L₁ ∧ Admin.listToCore s l₂ = some L₂ ∧
        L = L₁ ++ L₂
  | [], _, L, h => ⟨[], L, rfl, by simpa using h, by simp⟩
  | a :: as, l₂, L, h => by
      simp only [List.cons_append, Admin.listToCore_cons, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at h
      obtain ⟨u, hu, v, hv, rfl⟩ := h
      obtain ⟨V₁, V₂, h₁, h₂, rfl⟩ := listToCore_append_inv as hv
      exact ⟨u ++ V₁, V₂, by simp [Admin.listToCore_cons, hu, h₁], h₂, by simp⟩

/-! ## Context rules (`8-reduction:161-169`) -/

theorem state_ctxtInstrs {s' : Store H} {f' : Frame} {vs : List Val}
    {is is' rest : List Admin}
    (ih : ∀ c : CConfig H, Sim ⟨s, f, is⟩ c → Target P tgt ⟨s', f', is'⟩ c)
    (hext : StoreExt s s') (hne : vs ≠ [] ∨ rest ≠ []) {c : CConfig H}
    (hs : Sim ⟨s, f, vals vs ++ is ++ rest⟩ c) :
    Target P tgt ⟨s', f', vals vs ++ is' ++ rest⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hwfs, hwfm, hwfc⟩ := sim_wf hs
  simp only [listWF_append] at hwfc
  obtain ⟨⟨-, hwfi⟩, hwfr⟩ := hwfc
  -- the image of the redex splits
  obtain ⟨VI, R, hVI, hR, hsplit⟩ := listToCore_append_inv _ (sim_code hs)
  obtain ⟨V, I, hV, hI, rfl⟩ := listToCore_append_inv _ hVI
  rw [values_toCore] at hV
  cases hV
  -- so does the Core code
  obtain ⟨m₁, m₂, rfl, hm₁, hm₂⟩ := List.map_eq_append_iff.mp hsplit
  obtain ⟨l₁, l₂, rfl, hl₁, hl₂⟩ := List.map_eq_append_iff.mp hm₁
  -- the inner simulation
  have hsub : Sim ⟨s, f, is⟩ ⟨cs, cf, l₂⟩ :=
    simMkNorm (sim_store hs) (sim_frame hs) (by rw [hI, hl₂]) ⟨hwfs, hwfm, hwfi⟩
  obtain ⟨⟨cs₁, cf₁, l₂'⟩, hstep, hs'⟩ := ih _ hsub
  have hmod : cf₁.module = cf.module := cplus_module hstep
  have hneC : (vs.map Val.toCore) ≠ [] ∨ m₂ ≠ [] := by
    rcases hne with hv | hr
    · exact Or.inl (by simpa using hv)
    · refine Or.inr fun h0 => listToCore_ne_nil hr hR ?_
      rw [← hm₂, h0, List.map_nil]
  refine ⟨⟨cs₁, cf₁, cvals (vs.map Val.toCore) ++ l₂' ++ m₂⟩, ?_, ?_⟩
  · have hcatch := catchUpVals (P := P) (tgt := tgt) (cs := cs) (cf := cf)
      (vs.map Val.toCore) l₁ (l₂ ++ m₂) hl₁
    rw [← List.append_assoc, ← List.append_assoc] at hcatch
    refine Relation.TransGen.trans_right hcatch ?_
    have := Relation.TransGen.lift
      (fun x : CConfig H =>
        (⟨x.store, x.frame, cvals (vs.map Val.toCore) ++ x.code ++ m₂⟩ : CConfig H))
      (fun a b hab => by
        rcases a with ⟨sa, fa, ia⟩
        rcases b with ⟨sb, fb, ib⟩
        exact Silmaril.Wasm.Execution.Core.Step.ctxtInstrs hab hneC) _ _ hstep
    exact this
  · refine simMkNorm (sim_store hs') (sim_frame hs') ?_ ⟨(sim_wf hs').1, (sim_wf hs').2.1, ?_⟩
    · have hrest : Admin.listToCore s' rest = some R := by
        rw [listToCore_storeExt hext rest hwfr, hR]
      have hm₂' : m₂.map (ToCore.Admin.norm cf₁.module) = R := by
        rw [ToCore.Admin.map_norm_congr m₂ (by rw [hmod]), hm₂]
      rw [List.map_append, List.map_append, map_norm_cvals, hm₂']
      exact Admin.listToCore_append s' (Admin.listToCore_append s' (values_toCore s' vs)
        (sim_code hs')) hrest
    · simp only [listWF_append]
      exact ⟨⟨listWF_vals s' vs, (sim_wf hs').2.2⟩, listWF_storeExt hext rest hwfr⟩

theorem state_ctxtLabel {s' : Store H} {f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin}
    (ih : ∀ c : CConfig H, Sim ⟨s, f, is⟩ c → Target P tgt ⟨s', f', is'⟩ c) {c : CConfig H}
    (hs : Sim ⟨s, f, [.label n cont is]⟩ c) :
    Target P tgt ⟨s', f', [.label n cont is']⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨k, b, B, rfl, hk, hB, hb⟩ := sim_label hs
  have hwfin : Admin.listWF s is := by simpa using (sim_wf hs).2.2
  have hsub : Sim ⟨s, f, is⟩ ⟨cs, cf, b⟩ :=
    simMkNorm (sim_store hs) (sim_frame hs) (by rw [hB, hb])
      ⟨(sim_wf hs).1, (sim_wf hs).2.1, hwfin⟩
  obtain ⟨c', hstep, hs'⟩ := ih _ hsub
  obtain ⟨cs', cf', b'⟩ := c'
  refine ⟨⟨cs', cf', [.label n k b']⟩, ?_, ?_⟩
  · refine Relation.TransGen.lift
      (fun x : CConfig H => (⟨x.store, x.frame, [.label n k x.code]⟩ : CConfig H)) ?_ _ _ hstep
    rintro ⟨sa, fa, ia⟩ ⟨sb, fb, ib⟩ hab
    exact Silmaril.Wasm.Execution.Core.Step.ctxtLabel hab
  · refine simMkNorm (sim_store hs') (sim_frame hs') ?_
      ⟨(sim_wf hs').1, (sim_wf hs').2.1, by simpa using (sim_wf hs').2.2⟩
    simp [Admin.listToCore_cons, Admin.label_toCore, hk, sim_code hs']

theorem state_ctxtFrame {s' : Store H} {fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : ∀ c : CConfig H, Sim ⟨s, fi, is⟩ c → Target P tgt ⟨s', fi', is'⟩ c)
    (hext : StoreExt s s') {c : CConfig H} (hs : Sim ⟨s, f, [.frame n fi is]⟩ c) :
    Target P tgt ⟨s', f, [.frame n fi' is']⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨fc, b, B, rfl, hfc, hB, hb⟩ := sim_frame_adm hs
  have hwfin : ModWF s fi.module ∧ Admin.listWF s is := by simpa using (sim_wf hs).2.2
  have hsub : Sim ⟨s, fi, is⟩ ⟨cs, fc, b⟩ :=
    simMkNorm (sim_store hs) hfc.symm (by rw [hB, hb])
      ⟨(sim_wf hs).1, hwfin.1, hwfin.2⟩
  obtain ⟨c', hstep, hs'⟩ := ih _ hsub
  obtain ⟨cs', fc', b'⟩ := c'
  refine ⟨⟨cs', cf, [.frame n fc' b']⟩, ?_, ?_⟩
  · refine Relation.TransGen.lift
      (fun x : CConfig H => (⟨x.store, cf, [.frame n x.frame x.code]⟩ : CConfig H)) ?_ _ _ hstep
    rintro ⟨sa, fa, ia⟩ ⟨sb, fb, ib⟩ hab
    exact Silmaril.Wasm.Execution.Core.Step.ctxtFrame hab
  · refine simMkNorm (sim_store hs') (sim_frame hs) ?_
      ⟨(sim_wf hs').1, StoreExt.modWF hext (sim_wf hs).2.1, ?_⟩
    · simp [Admin.listToCore_cons, Admin.frame_toCore, sim_code hs', sim_frame hs']
    · simpa using ⟨(sim_wf hs').2.1, (sim_wf hs').2.2⟩

/-! ## Local and global instructions (`8-reduction:380-392`) -/

theorem state_localSet {x : LocalIdx} {v : Val} (hx : x.toNat < f.locals.length)
    {c : CConfig H} (hs : Sim ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ c) :
    Target P tgt ⟨s, f.setLocal x v, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hxc : x.toNat < cf.locals.length := by
    rw [erase_locals (sim_frame hs), List.length_map]; exact hx
  exact finish hs (vs := [v.toCore]) (R := [.plain (.localSet x)]) (by v2img) (by v2rigid)
    (by simp) (Relation.TransGen.single (.variable (.localSet hxc)))
    (sim_store hs) (toCore_setLocal (sim_frame hs))
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩

theorem state_globalSet {x : GlobalIdx} {v : Val} {a : GlobalAddr} {gi : GlobalInst}
    (ha : f.module.globalAddr? x = some a) (hg : s.globalInst? a = some gi) {c : CConfig H}
    (hs : Sim ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩ c) :
    Target P tgt ⟨s.setGlobalInst a { gi with value := v }, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hga := bridgeGlobal (sim_store hs) (sim_frame hs) ha hg
  exact finish hs (vs := [v.toCore]) (R := [.plain (.globalSet x)]) (by v2img) (by v2rigid)
    (by simp) (Relation.TransGen.single (.variable (.globalSet hga)))
    (toCore_setGlobalInst (sim_store hs) hg) (sim_frame hs)
    ⟨storeWF_setGlobalInst (sim_wf hs).1 _ _, (sim_wf hs).2.1, by simp⟩

/-! ## Element and data segments (`8-reduction:483, 663`) -/

theorem state_elemDrop {x : ElemIdx} {a : ElemAddr} {ei : ElemInst}
    (ha : f.module.elemAddr? x = some a) (he : s.elemInst? a = some ei) {c : CConfig H}
    (hs : Sim ⟨s, f, [.plain (.elemDrop x)]⟩ c) :
    Target P tgt ⟨s.setElemInst a { ei with refs := [] }, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hea := bridgeElem (sim_store hs) (sim_frame hs) ha he
  exact finish hs (vs := []) (R := [.plain (.elemDrop x)]) (by v2img) (by v2rigid)
    (by simp) (Relation.TransGen.single (.table (.elemDrop hea)))
    (toCore_setElemInst (sim_store hs) he) (sim_frame hs)
    ⟨storeWF_setElemInst (sim_wf hs).1 _ _, (sim_wf hs).2.1, by simp⟩

theorem state_dataDrop {x : DataIdx} {a : DataAddr} {di : DataInst}
    (ha : f.module.dataAddr? x = some a) (hd : s.dataInst? a = some di) {c : CConfig H}
    (hs : Sim ⟨s, f, [.plain (.dataDrop x)]⟩ c) :
    Target P tgt ⟨s.setDataInst a ⟨ByteArray.empty⟩, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hda := bridgeData (sim_store hs) (sim_frame hs) ha hd
  exact finish hs (vs := []) (R := [.plain (.dataDrop x)]) (by v2img) (by v2rigid)
    (by simp) (Relation.TransGen.single (.memory (.dataDrop hda)))
    (toCore_setDataInst (sim_store hs) hd) (sim_frame hs)
    ⟨storeWF_setDataInst (sim_wf hs).1 _ _, (sim_wf hs).2.1, by simp⟩

theorem tableGrow_none {ti : TableInst} {n : Nat} {r : Ref} (hg : ti.grow? n r = none) :
    (ti.toCore).grow? n r.toCore = none := by
  have hlen : (ti.toCore).refs.length = ti.refs.length := List.length_map ..
  have hnc : ¬ ((ti.toCore).refs.length + n ≤ 2 ^ (ti.toCore).type.address.width - 1 ∧
      ∀ j, (ti.toCore).type.limits.max = some j → (ti.toCore).refs.length + n ≤ j.val) := by
    intro hcond
    unfold TableInst.grow? at hg
    split at hg
    · exact absurd hg (by simp)
    · rename_i hc
      refine hc ⟨?_, ?_⟩
      · have h1 := hcond.1
        rw [hlen, show (ti.toCore).type.address.width = 32 from rfl] at h1
        omega
      · cases hmax : ti.type.limits.max with
        | none => simp
        | some j₀ =>
          have h2 := hcond.2 (widen32 j₀)
            (by simp [TableInst.toCore, ToCore.tableToC, Limits.toCore, hmax])
          rw [hlen] at h2
          simpa [widen32] using h2
  unfold Silmaril.Wasm.Execution.Core.TableInst.grow?
  simp only [ite_eq_right hnc]

theorem memGrow_none {mi : MemInst} {n : Nat} (hg : mi.grow? n = none) :
    (mi.toCore).grow? n = none := by
  have hnc : ¬ ((mi.toCore).bytes.size / Silmaril.Wasm.Execution.Memory.pageSize + n ≤
        2 ^ ((mi.toCore).type.address.width - 16) ∧
      ∀ j, (mi.toCore).type.limits.max = some j →
        (mi.toCore).bytes.size / Silmaril.Wasm.Execution.Memory.pageSize + n ≤ j.val) := by
    intro hcond
    unfold MemInst.grow? at hg
    split at hg
    · exact absurd hg (by simp)
    · rename_i hc
      refine hc ⟨hcond.1, ?_⟩
      cases hmax : mi.type.limits.max with
      | none => simp
      | some j₀ =>
        have h2 := hcond.2 (widen32 j₀)
          (by simp [MemInst.toCore, MemoryType.toCore, Limits.toCore, hmax])
        simpa [widen32, MemInst.toCore] using h2
  unfold Silmaril.Wasm.Execution.Core.MemInst.grow?
  simp only [ite_eq_right hnc]

theorem setRef_toCore (ti : TableInst) (i : Nat) (r : Ref) :
    (ti.setRef i r).toCore = { ti.toCore with refs := (ti.toCore).refs.set i r.toCore } := by
  simp [TableInst.setRef, TableInst.toCore, List.map_set]

/-! ## Table instructions (`8-reduction:406-425`) -/

theorem state_tableSetTrap {x : TableIdx} {i : BitVec 32} {r : Ref} {a : TableAddr}
    {ti : TableInst} (ha : f.module.tableAddr? x = some a) (ht : s.tableInst? a = some ti)
    (h : ti.refs.length ≤ i.toNat) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, aref r, .plain (.tableSet x)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hta := bridgeTable (sim_store hs) (sim_frame hs) ha ht
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, .ref r.toCore])
    (R := [.plain (.tableSet x)]) (L' := [.trap]) (by v2img) (by v2rigid) (by v2img) (by simp)
    (.table (.setOob (a := .i32) hta (by simp only [TableInst.toCore, List.length_map]; exact h)))

theorem state_tableSetVal {x : TableIdx} {i : BitVec 32} {r : Ref} {a : TableAddr}
    {ti : TableInst} (ha : f.module.tableAddr? x = some a) (ht : s.tableInst? a = some ti)
    (h : i.toNat < ti.refs.length) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, aref r, .plain (.tableSet x)]⟩ c) :
    Target P tgt ⟨s.setTableInst a (ti.setRef i.toNat r), f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hta := bridgeTable (sim_store hs) (sim_frame hs) ha ht
  have hlen : (ti.setRef i.toNat r).refs.length < 2 ^ 32 := by
    simpa [TableInst.setRef] using (sim_wf hs).1.2.2.2 a ti ht
  have hstep : CStep P tgt
      ⟨cs, cf, cvals [.num ⟨.int .i32, i⟩, .ref r.toCore] ++ [.plain (.tableSet x)]⟩
      ⟨cs.setTable a (ti.setRef i.toNat r).toCore, cf, []⟩ := by
    rw [setRef_toCore]
    refine .table (.setVal (a := .i32) hta ?_)
    simp only [TableInst.toCore, List.length_map]; exact h
  exact finish hs (by v2img) (by v2rigid) (by simp) (Relation.TransGen.single hstep)
    (toCore_setTableInst (sim_store hs)) (sim_frame hs)
    ⟨storeWF_setTableInst (sim_wf hs).1 hlen, (sim_wf hs).2.1, by simp⟩

theorem state_tableGrowSucceed {x : TableIdx} {n : BitVec 32} {r : Ref} {a : TableAddr}
    {ti ti' : TableInst} (ha : f.module.tableAddr? x = some a) (ht : s.tableInst? a = some ti)
    (hg : ti.grow? n.toNat r = some ti')
    (hp : P.growMaySucceed .table a ti.refs.length n.toNat) {c : CConfig H}
    (hs : Sim ⟨s, f, [aref r, constI32 n, .plain (.tableGrow x)]⟩ c) :
    Target P tgt ⟨s.setTableInst a ti', f, [constI32 (BitVec.ofNat 32 ti.refs.length)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hta := bridgeTable (sim_store hs) (sim_frame hs) ha ht
  have h0 : (ti.toCore).refs.length = ti.refs.length := List.length_map ..
  have hstep : CStep P tgt
      ⟨cs, cf, cvals [.ref r.toCore, .num ⟨.int .i32, n⟩] ++ [.plain (.tableGrow x)]⟩
      ⟨cs.setTable a ti'.toCore, cf,
        [.plain (.intConst .i32 (BitVec.ofNat 32 ti.refs.length))]⟩ := by
    have hcore := Silmaril.Wasm.Execution.Core.TableStep.growSucceed (P := P) (a := .i32)
      (n := n) (f := cf) hta (tableGrow_toCore hg) (by rw [h0]; exact hp)
    rw [h0] at hcore
    exact .table hcore
  exact finish hs (by v2img) (by v2rigid) (by v2img) (Relation.TransGen.single hstep)
    (toCore_setTableInst (sim_store hs)) (sim_frame hs)
    ⟨storeWF_setTableInst (sim_wf hs).1 (tableGrow_length hg), (sim_wf hs).2.1, by simp⟩

theorem state_tableGrowFail {x : TableIdx} {n : BitVec 32} {r : Ref} {a : TableAddr}
    {ti : TableInst} (ha : f.module.tableAddr? x = some a) (ht : s.tableInst? a = some ti)
    (hp : P.growMayFail .table a ti.refs.length n.toNat ∨ ti.grow? n.toNat r = none)
    {c : CConfig H} (hs : Sim ⟨s, f, [aref r, constI32 n, .plain (.tableGrow x)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 (BitVec.allOnes 32)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hta := bridgeTable (sim_store hs) (sim_frame hs) ha ht
  have h0 : (ti.toCore).refs.length = ti.refs.length := List.length_map ..
  have hpc : P.growMayFail .table a (ti.toCore).refs.length n.toNat ∨
      (ti.toCore).grow? n.toNat r.toCore = none := by
    rw [h0]
    exact hp.imp id tableGrow_none
  exact finishSame hs (vs := [.ref r.toCore, .num ⟨.int .i32, n⟩])
    (R := [.plain (.tableGrow x)]) (L' := [.plain (.intConst .i32 (BitVec.allOnes 32))])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.table (.growFail (a := .i32) hta hpc))

/-! ## Memory stores (`8-reduction:559-593`) -/

theorem store_of_writeBytes {mi mi' : MemInst} {i count : Nat} {w : BitVec (8 * count)}
    (h : mi.writeBytes? i count
      (Silmaril.Wasm.Execution.Memory.encodeLE count w.toNat) = some mi') :
    Silmaril.Wasm.Execution.Memory.store mi.bytes i w = some mi'.bytes ∧
      mi'.toCore = { mi.toCore with bytes := mi'.bytes } := by
  unfold MemInst.writeBytes? at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    exact ⟨hb, rfl⟩
  · exact absurd h (by simp)

theorem storeWF_memInst {a : MemAddr} {mi mi' : MemInst}
    (hwf : StoreWF s) (hm : s.memInst? a = some mi) (hsz : mi'.bytes.size = mi.bytes.size) :
    StoreWF (s.setMemInst a mi') :=
  storeWF_setMemInst hwf (by rw [hsz]; exact hwf.2.1 a mi hm)
    (by rw [hsz]; exact hwf.2.2.1 a mi hm)

theorem state_storeIntTrap {t : IntType} {ao : MemArg} {i : BitVec 32} {cv : BitVec t.width}
    {a : MemAddr} {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
    (hm : s.memInst? a = some mi) (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.intConst t cv), .plain (.intStore t none ao)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, .num ⟨.int t, cv⟩])
    (R := [.plain (.intStore t none ⟨0⟩ ao.toCore)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.storeIntOob (a := .i32) hma h))

theorem state_storeIntVal {t : IntType} {ao : MemArg} {i : BitVec 32} {cv : BitVec t.width}
    {a : MemAddr} {mi mi' : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
    (hm : s.memInst? a = some mi)
    (hw : mi.writeBytes? (effAddr i.toNat ao) (t.width / 8) (nbytes (.int t) cv) = some mi')
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.intConst t cv), .plain (.intStore t none ao)]⟩ c) :
    Target P tgt ⟨s.setMemInst a mi', f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  have hcv : (cv.setWidth (8 * (t.width / 8))).toNat = cv.toNat := by
    rw [BitVec.toNat_setWidth]
    cases t
    · exact Nat.mod_eq_of_lt (show cv.toNat < 2 ^ 32 from cv.isLt)
    · exact Nat.mod_eq_of_lt (show cv.toNat < 2 ^ 64 from cv.isLt)
  have hbs : nbytes (.int t) cv = Silmaril.Wasm.Execution.Memory.encodeLE (t.width / 8)
      ((cv.setWidth (8 * (t.width / 8))).toNat) := by
    rw [hcv]; rfl
  rw [hbs] at hw
  obtain ⟨hstore, htc⟩ := store_of_writeBytes hw
  have hsz : mi'.bytes.size = mi.bytes.size :=
    Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hstore
  have hstep : CStep P tgt
      ⟨cs, cf, cvals [.num ⟨.int .i32, i⟩, .num ⟨.int t, cv⟩] ++
        [.plain (.intStore t none ⟨0⟩ ao.toCore)]⟩
      ⟨cs.setMem a mi'.toCore, cf, []⟩ := by
    rw [htc]
    exact .memory (.storeIntVal (a := .i32) hma hstore)
  exact finish hs (by v2img) (by v2rigid) (by simp) (Relation.TransGen.single hstep)
    (toCore_setMemInst (sim_store hs)) (sim_frame hs)
    ⟨storeWF_memInst (sim_wf hs).1 hm hsz, (sim_wf hs).2.1, by simp⟩

theorem toNat_setWidth_self {W : Nat} (h : 8 * (W / 8) = W) (x : BitVec W) :
    (x.setWidth (8 * (W / 8))).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, h, Nat.mod_eq_of_lt x.isLt]

theorem state_storeFloatTrap {t : FloatType} {ao : MemArg} {i : BitVec 32}
    {cv : BitVec t.width} {a : MemAddr} {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
    (hm : s.memInst? a = some mi) (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.floatConst t cv), .plain (.floatStore t ao)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, .num ⟨.float t, cv⟩])
    (R := [.plain (.floatStore t ⟨0⟩ ao.toCore)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.storeFloatOob (a := .i32) hma h))

theorem state_storeFloatVal {t : FloatType} {ao : MemArg} {i : BitVec 32} {cv : BitVec t.width}
    {a : MemAddr} {mi mi' : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
    (hm : s.memInst? a = some mi)
    (hw : mi.writeBytes? (effAddr i.toNat ao) (t.width / 8) (fbytes t cv) = some mi')
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.floatConst t cv), .plain (.floatStore t ao)]⟩ c) :
    Target P tgt ⟨s.setMemInst a mi', f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  have hbs : fbytes t cv = Silmaril.Wasm.Execution.Memory.encodeLE (t.width / 8)
      ((cv.setWidth (8 * (t.width / 8))).toNat) := by
    rw [toNat_setWidth_self (by cases t <;> rfl)]; rfl
  rw [hbs] at hw
  obtain ⟨hstore, htc⟩ := store_of_writeBytes hw
  have hsz : mi'.bytes.size = mi.bytes.size :=
    Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hstore
  have hstep : CStep P tgt
      ⟨cs, cf, cvals [.num ⟨.int .i32, i⟩, .num ⟨.float t, cv⟩] ++
        [.plain (.floatStore t ⟨0⟩ ao.toCore)]⟩
      ⟨cs.setMem a mi'.toCore, cf, []⟩ := by
    rw [htc]
    exact .memory (.storeFloatVal (a := .i32) hma hstore)
  exact finish hs (by v2img) (by v2rigid) (by simp) (Relation.TransGen.single hstep)
    (toCore_setMemInst (sim_store hs)) (sim_frame hs)
    ⟨storeWF_memInst (sim_wf hs).1 hm hsz, (sim_wf hs).2.1, by simp⟩

theorem state_storePackTrap {t : IntType} {sz : PackSize} {ao : MemArg} {i : BitVec 32}
    {cv : BitVec t.width} {a : MemAddr} {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
    (hm : s.memInst? a = some mi) (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8)
    {c : CConfig H}
    (hs : Sim ⟨s, f,
      [constI32 i, .plain (.intConst t cv), .plain (.intStore t (some sz) ao)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, .num ⟨.int t, cv⟩])
    (R := [.plain (.intStore t (some sz) ⟨0⟩ ao.toCore)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.storePackOob (a := .i32) hma h))

theorem state_storePackVal {t : IntType} {sz : PackSize} {ao : MemArg} {i : BitVec 32}
    {cv : BitVec t.width} {a : MemAddr} {mi mi' : MemInst}
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hw : mi.writeBytes? (effAddr i.toNat ao) (sz.width / 8)
      (ibytes sz.width (cv.setWidth sz.width)) = some mi') {c : CConfig H}
    (hs : Sim ⟨s, f,
      [constI32 i, .plain (.intConst t cv), .plain (.intStore t (some sz) ao)]⟩ c) :
    Target P tgt ⟨s.setMemInst a mi', f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  have hbs : ibytes sz.width (cv.setWidth sz.width) =
      Silmaril.Wasm.Execution.Memory.encodeLE (sz.width / 8)
        ((cv.setWidth (8 * (sz.width / 8))).toNat) := by
    rw [show 8 * (sz.width / 8) = sz.width from by cases sz <;> rfl]; rfl
  rw [hbs] at hw
  obtain ⟨hstore, htc⟩ := store_of_writeBytes hw
  have hsz : mi'.bytes.size = mi.bytes.size :=
    Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hstore
  have hstep : CStep P tgt
      ⟨cs, cf, cvals [.num ⟨.int .i32, i⟩, .num ⟨.int t, cv⟩] ++
        [.plain (.intStore t (some sz) ⟨0⟩ ao.toCore)]⟩
      ⟨cs.setMem a mi'.toCore, cf, []⟩ := by
    rw [htc]
    exact .memory (.storePackVal (a := .i32) hma hstore)
  exact finish hs (by v2img) (by v2rigid) (by simp) (Relation.TransGen.single hstep)
    (toCore_setMemInst (sim_store hs)) (sim_frame hs)
    ⟨storeWF_memInst (sim_wf hs).1 hm hsz, (sim_wf hs).2.1, by simp⟩

theorem state_vecStoreOob {ao : MemArg} {i : BitVec 32} {cv : V128} {a : MemAddr}
    {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (h : mi.bytes.size < effAddr i.toNat ao + 16) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, vconst cv, .plain (.vecStore ao)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, .vec cv])
    (R := [.plain (.vecStore ⟨0⟩ ao.toCore)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.vecStoreOob (a := .i32) hma h))

theorem state_vecStoreVal {ao : MemArg} {i : BitVec 32} {cv : V128} {a : MemAddr}
    {mi mi' : MemInst} (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hw : mi.writeBytes? (effAddr i.toNat ao) 16 (vbytes cv) = some mi') {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, vconst cv, .plain (.vecStore ao)]⟩ c) :
    Target P tgt ⟨s.setMemInst a mi', f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  have hbs : vbytes cv = Silmaril.Wasm.Execution.Memory.encodeLE 16 cv.toNat := rfl
  rw [hbs] at hw
  obtain ⟨hstore, htc⟩ := store_of_writeBytes hw
  have hsz : mi'.bytes.size = mi.bytes.size :=
    Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hstore
  have hstep : CStep P tgt
      ⟨cs, cf, cvals [.num ⟨.int .i32, i⟩, .vec cv] ++ [.plain (.vecStore ⟨0⟩ ao.toCore)]⟩
      ⟨cs.setMem a mi'.toCore, cf, []⟩ := by
    rw [htc]
    exact .memory (.vecStoreVal (a := .i32) hma hstore)
  exact finish hs (by v2img) (by v2rigid) (by simp) (Relation.TransGen.single hstep)
    (toCore_setMemInst (sim_store hs)) (sim_frame hs)
    ⟨storeWF_memInst (sim_wf hs).1 hm hsz, (sim_wf hs).2.1, by simp⟩

theorem state_vecStoreLaneOob {sz : PackSize} {ao : MemArg} {j : LaneIdx} {i : BitVec 32}
    {cv : V128} {a : MemAddr} {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
    (hm : s.memInst? a = some mi) (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, vconst cv, .plain (.vecStoreLane sz ao j)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, .vec cv])
    (R := [.plain (.vecStoreLane sz ⟨0⟩ ao.toCore j)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.vecStoreLaneOob (a := .i32) hma h))

theorem state_vecStoreLaneVal {sz : PackSize} {ao : MemArg} {j : LaneIdx} {i : BitVec 32}
    {cv : V128} {a : MemAddr} {mi mi' : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
    (hm : s.memInst? a = some mi) (_hj : j.val < 128 / sz.width)
    (hw : mi.writeBytes? (effAddr i.toNat ao) (sz.width / 8)
      (ibytes sz.width ((Numerics.lanes sz.width (128 / sz.width) cv).getD j.val 0)) = some mi')
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, vconst cv, .plain (.vecStoreLane sz ao j)]⟩ c) :
    Target P tgt ⟨s.setMemInst a mi', f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  have hbs : ibytes sz.width ((Numerics.lanes sz.width (128 / sz.width) cv).getD j.val 0) =
      Silmaril.Wasm.Execution.Memory.encodeLE (sz.width / 8)
        ((((Numerics.lanes sz.width (128 / sz.width) cv).getD j.val 0).setWidth
          (8 * (sz.width / 8))).toNat) := by
    rw [toNat_setWidth_self (by cases sz <;> rfl)]; rfl
  rw [hbs] at hw
  obtain ⟨hstore, htc⟩ := store_of_writeBytes hw
  have hsz : mi'.bytes.size = mi.bytes.size :=
    Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hstore
  have hstep : CStep P tgt
      ⟨cs, cf, cvals [.num ⟨.int .i32, i⟩, .vec cv] ++
        [.plain (.vecStoreLane sz ⟨0⟩ ao.toCore j)]⟩
      ⟨cs.setMem a mi'.toCore, cf, []⟩ := by
    rw [htc]
    exact .memory (.vecStoreLaneVal (a := .i32) hma hstore)
  exact finish hs (by v2img) (by v2rigid) (by simp) (Relation.TransGen.single hstep)
    (toCore_setMemInst (sim_store hs)) (sim_frame hs)
    ⟨storeWF_memInst (sim_wf hs).1 hm hsz, (sim_wf hs).2.1, by simp⟩

/-! ## Memory growth (`8-reduction:600-605`) -/

theorem memGrow_size_le {mi mi' : MemInst} {n : Nat}
    (halign : mi.bytes.size % pageSize = 0) (hg : mi.grow? n = some mi') :
    mi'.bytes.size ≤ 2 ^ 32 := by
  have hsz := MemInst.grow?_size hg
  have hmin := (MemInst.grow?_min hg).2
  have hdvd : mi.bytes.size / pageSize * pageSize = mi.bytes.size :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero halign)
  have h1 : mi'.bytes.size = (mi.bytes.size / pageSize + n) * pageSize := by
    rw [hsz, Nat.add_mul, hdvd]
  rw [h1]
  calc (mi.bytes.size / pageSize + n) * pageSize ≤ 2 ^ 16 * pageSize :=
        Nat.mul_le_mul_right _ hmin
    _ = 2 ^ 32 := by norm_num [Silmaril.Wasm.Execution.Memory.pageSize]

/-- Growth preserves page alignment: `$growmemory` appends `0^(n * 64 * $Ki)`
(`5-runtime-aux:131`), a whole number of pages. -/
theorem memGrow_align {mi mi' : MemInst} {n : Nat}
    (halign : mi.bytes.size % pageSize = 0) (hg : mi.grow? n = some mi') :
    mi'.bytes.size % pageSize = 0 := by
  rw [MemInst.grow?_size hg, Nat.add_mul_mod_self_right]
  exact halign

/-- `Step/memory.grow-succeed` (`8-reduction:600`). No page-alignment hypothesis
is needed: `ConfigWF` already carries it, because `StoreWF`
(`V2/ToCore/Runtime.lean`) records that every memory instance holds a whole
number of pages. -/
theorem state_memoryGrowSucceed {n : BitVec 32} {a : MemAddr} {mi mi' : MemInst}
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hg : mi.grow? n.toNat = some mi') (hp : P.growMaySucceed .memory a mi.pages n.toNat)
    {c : CConfig H} (hs : Sim ⟨s, f, [constI32 n, .plain .memoryGrow]⟩ c) :
    Target P tgt ⟨s.setMemInst a mi', f, [constI32 (BitVec.ofNat 32 mi.pages)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have halign : mi.bytes.size % pageSize = 0 := (sim_wf hs).1.2.2.1 _ _ hm
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  have hstep : CStep P tgt
      ⟨cs, cf, cvals [.num ⟨.int .i32, n⟩] ++ [.plain (.memoryGrow ⟨0⟩)]⟩
      ⟨cs.setMem a mi'.toCore, cf, [.plain (.intConst .i32 (BitVec.ofNat 32 mi.pages))]⟩ :=
    .memory (.growSucceed (a := .i32) hma (memGrow_toCore hg) hp)
  exact finish hs (by v2img) (by v2rigid) (by v2img) (Relation.TransGen.single hstep)
    (toCore_setMemInst (sim_store hs)) (sim_frame hs)
    ⟨storeWF_setMemInst (sim_wf hs).1 (memGrow_size_le halign hg) (memGrow_align halign hg),
      (sim_wf hs).2.1, by simp⟩

theorem state_memoryGrowFail {n : BitVec 32} {a : MemAddr} {mi : MemInst}
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hp : P.growMayFail .memory a mi.pages n.toNat ∨ mi.grow? n.toNat = none) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 n, .plain .memoryGrow]⟩ c) :
    Target P tgt ⟨s, f, [constI32 (BitVec.allOnes 32)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have hma := bridgeMem (sim_store hs) (sim_frame hs) ha hm
  have hpc : P.growMayFail .memory a (mi.toCore).pages n.toNat ∨
      (mi.toCore).grow? n.toNat = none := hp.imp id memGrow_none
  exact finishSame hs (vs := [.num ⟨.int .i32, n⟩]) (R := [.plain (.memoryGrow ⟨0⟩)])
    (L' := [.plain (.intConst .i32 (BitVec.allOnes 32))])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.growFail (a := .i32) hma hpc))

/-! ## Host functions (deviation 3 of `V2/Execution/Step.lean`) -/

theorem mapM_funcInst_getElem {l : List (FuncInst H)} {fs : List (ToCore.CFuncInst H)}
    (h : l.mapM FuncInst.toCore = some fs) (a : Nat) :
    fs[a]? = (l[a]?).bind FuncInst.toCore := by
  induction l generalizing fs a with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | cons b l ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨cb, hcb, cs, hcs, rfl⟩ := h
    cases a with
    | zero => simp [hcb]
    | succ a => simpa using ih hcs a

theorem bridgeHostFunc {cs : CStore H} {a : FuncAddr} {fi : FuncInst H} {hh : H}
    (hst : s.toCore = some (ToCore.Store.erase cs)) (hf : s.funcInst? a = some fi)
    (hcode : fi.code = .host hh) :
    ∃ ci : ToCore.CFuncInst H, cs.funcs[a]? = some ci ∧ ci.type = fi.type.toDefType ∧
      ci.code = .host hh := by
  simp only [Store.toCore, Option.map_eq_some_iff] at hst
  obtain ⟨fs, hfs, hE⟩ := hst
  have hfuncs : fs = cs.funcs.map
      (fun x => { x with module := ToCore.ModuleInst.erase x.module }) :=
    congrArg Silmaril.Wasm.Execution.Core.Store.funcs hE
  have hgetfs : fs[a]? = some ⟨fi.type.toDefType, fi.module.toCore, .host hh⟩ := by
    rw [mapM_funcInst_getElem hfs a, show s.funcs[a]? = some fi from hf]
    simp only [Option.bind_some]
    unfold FuncInst.toCore
    rw [hcode]
  rw [hfuncs, List.getElem?_map, Option.map_eq_some_iff] at hgetfs
  obtain ⟨ci, hci, hcieq⟩ := hgetfs
  exact ⟨ci, hci, congrArg Silmaril.Wasm.Execution.Core.FuncInst.type hcieq,
    congrArg Silmaril.Wasm.Execution.Core.FuncInst.code hcieq⟩

theorem listToCore_result (s : Store H) (r : Result) :
    Admin.listToCore s r.toAdmin = some ((Result.toCore r).toAdmin) := by
  cases r with
  | values ws =>
    simp [Result.toAdmin, Result.toCore, Silmaril.Wasm.Execution.Core.Result.toAdmin]
  | trap => rfl

theorem listWF_result (s : Store H) (r : Result) : Admin.listWF s r.toAdmin := by
  cases r <;> simp [Result.toAdmin]

theorem callAddr_image (s : Store H) (vs : List Val) (a : FuncAddr) :
    Admin.listToCore s (vals vs ++ [.callAddr a]) =
      some (cvals (vs.map Val.toCore) ++ [.ref (.func a)] ++
        [.callRefType (s.funcDefType a)]) := by
  rw [List.append_assoc]
  exact Admin.listToCore_append s (values_toCore s vs) (by simp)

theorem state_callAddrHost {src : HostSemantics H} (hosts : HostCompatible src tgt)
    {s' : Store H} {a : FuncAddr} {vs : List Val} {fi : FuncInst H} {h : H} {r : Result}
    (hf : s.funcInst? a = some fi) (hcode : fi.code = .host h)
    (hk : vs.length = fi.type.params.length) (hhost : src h s vs (.returned s' r))
    {c : CConfig H} (hs : Sim ⟨s, f, vals vs ++ [.callAddr a]⟩ c) :
    Target P tgt ⟨s', f, r.toAdmin⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have himg := sim_code hs
  rw [callAddr_image] at himg
  obtain ⟨t, ht, hcatch⟩ := catchUpSplit (P := P) (tgt := tgt) (cs := cs) (cf := cf)
    (vs := vs.map Val.toCore) (R := [.ref (.func a)])
    (T := [.callRefType (s.funcDefType a)])
    (by intro y hy; simp only [List.mem_singleton] at hy; subst hy
        exact Rigid.val (v := .ref (.func a)) (by simp))
    (Option.some.inj himg).symm
  rcases t with _ | ⟨x, t'⟩
  · simp at ht
  · simp only [List.map_cons, List.cons.injEq] at ht
    obtain ⟨hx, ht'⟩ := ht
    rw [List.map_eq_nil_iff.mp ht'] at hcatch
    have hxcall : Silmaril.Wasm.Execution.Core.Admin.IsCallRef x := by
      rcases norm_eq_callRefType hx with rfl | ⟨y, rfl, -⟩ <;> trivial
    obtain ⟨ci, hci, hcit, hcic⟩ := bridgeHostFunc (sim_store hs) hf hcode
    have he : Silmaril.Wasm.Validation.Expand ci.type
        (.func (Silmaril.Wasm.Validation.Ty.ofList (fi.type.params.map ValType.toC))
          (Silmaril.Wasm.Validation.Ty.ofList (fi.type.results.map ValType.toC))) := by
      rw [hcit]
      exact Silmaril.Wasm.Validation.Expand.iff.mpr (FuncType.toDefType_expand _)
    obtain ⟨outC, htgt, hout⟩ := hosts.2 h s vs _ cs hhost (sim_store hs)
    cases outC with
    | diverged => simp [HostOutcomeSim] at hout
    | returned sC rC =>
      simp only [HostOutcomeSim] at hout
      obtain ⟨hsC, rfl⟩ := hout
      obtain ⟨hwf', hext⟩ := hosts.1 h s vs s' r hhost (sim_wf hs).1
      have hcore : CStep P tgt
          ⟨cs, cf, cvals (vs.map Val.toCore) ++ [.ref (.func a)] ++ [x]⟩
          ⟨sC, cf, (Result.toCore r).toAdmin⟩ := by
        rw [List.append_assoc]
        exact .callRefHost hxcall hci he
          (by simp [Silmaril.Wasm.Validation.Ty.length_ofList, hk]) hcic htgt
      have hnorm : ((Result.toCore r).toAdmin).map (ToCore.Admin.norm cf.module) =
          (Result.toCore r).toAdmin := by
        cases r <;> simp [Result.toCore, Silmaril.Wasm.Execution.Core.Result.toAdmin]
      exact finishFrom (Relation.TransGen.trans_right hcatch
          (Relation.TransGen.single hcore)) (by rw [listToCore_result, hnorm]) hsC
        (sim_frame hs) ⟨hwf', StoreExt.modWF hext (sim_wf hs).2.1, listWF_result s' r⟩

theorem state_callAddrHostDiv {src : HostSemantics H} (hosts : HostCompatible src tgt)
    {a : FuncAddr} {vs : List Val} {fi : FuncInst H} {h : H}
    (hf : s.funcInst? a = some fi) (hcode : fi.code = .host h)
    (hk : vs.length = fi.type.params.length) (hhost : src h s vs .diverged)
    {c : CConfig H} (hs : Sim ⟨s, f, vals vs ++ [.callAddr a]⟩ c) :
    Target P tgt ⟨s, f, vals vs ++ [.callAddr a]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have himg := sim_code hs
  rw [callAddr_image] at himg
  obtain ⟨t, ht, hcatch⟩ := catchUpSplit (P := P) (tgt := tgt) (cs := cs) (cf := cf)
    (vs := vs.map Val.toCore) (R := [.ref (.func a)])
    (T := [.callRefType (s.funcDefType a)])
    (by intro y hy; simp only [List.mem_singleton] at hy; subst hy
        exact Rigid.val (v := .ref (.func a)) (by simp))
    (Option.some.inj himg).symm
  rcases t with _ | ⟨x, t'⟩
  · simp at ht
  · simp only [List.map_cons, List.cons.injEq] at ht
    obtain ⟨hx, ht'⟩ := ht
    rw [List.map_eq_nil_iff.mp ht'] at hcatch
    have hxcall : Silmaril.Wasm.Execution.Core.Admin.IsCallRef x := by
      rcases norm_eq_callRefType hx with rfl | ⟨y, rfl, -⟩ <;> trivial
    obtain ⟨ci, hci, hcit, hcic⟩ := bridgeHostFunc (sim_store hs) hf hcode
    have he : Silmaril.Wasm.Validation.Expand ci.type
        (.func (Silmaril.Wasm.Validation.Ty.ofList (fi.type.params.map ValType.toC))
          (Silmaril.Wasm.Validation.Ty.ofList (fi.type.results.map ValType.toC))) := by
      rw [hcit]
      exact Silmaril.Wasm.Validation.Expand.iff.mpr (FuncType.toDefType_expand _)
    obtain ⟨outC, htgt, hout⟩ := hosts.2 h s vs _ cs hhost (sim_store hs)
    cases outC with
    | returned sC rC => simp [HostOutcomeSim] at hout
    | diverged =>
      have hcore : CStep P tgt
          ⟨cs, cf, cvals (vs.map Val.toCore) ++ [.ref (.func a)] ++ [x]⟩
          ⟨cs, cf, cvals (vs.map Val.toCore) ++ [.ref (.func a)] ++ [x]⟩ := by
        rw [List.append_assoc]
        exact .callRefHostDiv hxcall hci he
          (by simp [Silmaril.Wasm.Validation.Ty.length_ofList, hk]) hcic htgt
      refine finishFrom (Relation.TransGen.trans_right hcatch
        (Relation.TransGen.single hcore)) ?_ (sim_store hs) (sim_frame hs) (sim_wf hs)
      rw [callAddr_image]
      simp [hx]

end Silmaril.Wasm.V2.Execution.ToCoreSim
