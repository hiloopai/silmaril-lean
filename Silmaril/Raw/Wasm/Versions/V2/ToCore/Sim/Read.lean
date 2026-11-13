module

public import Silmaril.Raw.Wasm.Versions.V2.ToCore.Sim.Common

@[expose] public section

/-! # Step simulation: the `Step_read` rules (`8-reduction:7`)

One lemma per constructor of `Silmaril.Wasm.V2.Execution.ReadStep`, named after
it.

## Which rules are lock-step

**All of them except `call` and `call_indirect-call`.** Core 3.0 kept every
`Step_read` rule of 2.0 in the same shape:

| 2.0 | Core 3.0 | steps |
| --- | --- | --- |
| `block`, `loop` | `Step.block`, `Step.loop` | 1 |
| `call_addr` (Wasm code) | `Step.callRefFunc` | 1 |
| `ref.func`, `local.get`, `global.get` | `Step.reference`, `Step.variable` | 1 |
| `table.get-*`, `table.size`, `table.fill-*`, `table.copy-*`, `table.init-*` | `Step.table` | 1 |
| `load-*`, `vload*`, `memory.size`, `memory.fill-*`, `memory.copy-*`, `memory.init-*` | `Step.memory` | 1 |

In particular **2.0's bulk table and memory rules are lock-step with Core 3.0's**
(`table.fill/copy/init`, `memory.fill/copy/init`): both machines reduce one
element or byte per step and emit the same residual instruction sequence, so
there is nothing like the loop induction `Lime1/ToCore/Sim/Memory{Bulk,Copy,Fill}`
needs for `Lime1`'s *atomic* bulk operations.

The two exceptions are the calls.

* **`Step_read/call`** (`8-reduction:119`) produces the administrative
  `CALL_ADDR a`, which Core 3.0 deleted. Core's `Step_read/call` produces
  `(REF.FUNC_ADDR a) (CALL_REF dt)` with `dt` read from the store, which is
  exactly `Admin.toCore`'s image of `CALL_ADDR a`
  (`Store.funcDefType`), so this is still **one** Core step — but it needs
  `ModWF` to know that `a` is allocated, and `Store.toCore_funcs_type` to know
  that the annotation agrees.
* **`Step_read/call_indirect-call`** (`8-reduction:122`) resolves the table and
  the type in one step. Core 3.0's `Step_pure/call_indirect` expands to
  `TABLE.GET x; REF.CAST (ref null $y); CALL_REF y`, so the Core machine needs
  **three** steps to reach the image of `CALL_ADDR a`, and
  `Step_read/call_indirect-trap` needs one, two or three depending on which of
  the three premises fails. These are the only rules of this file that are not
  lock-step.

## The store/frame bridge

What every rule here needs first is the *bridge* of `Sim/Common.lean`: that
`(⟨s, f⟩ : State H).table? x = some ti` implies `cs.table? cf x = some (a,
ti.toCore)`, and its analogues `bridge_mem`, `bridge_global`, `bridge_elem`,
`bridge_data` and `bridge_local`. Those are proved. `read_localGet`,
`read_globalGet`, `read_tableGetTrap` and `read_tableGetVal` show the resulting
pattern — `bridge_*`, then `finishSame` with the Core family constructor — and
the remaining rules of this file follow it.
-/

namespace Silmaril.Wasm.V2.Execution.ToCoreSim

open Silmaril.Wasm.Numerics (Profile V128)
open Silmaril.Wasm.Execution.Memory (Bytes readBytes pageSize)
open Silmaril.Wasm.V2.Execution.ToCore

variable {H : Type} {P : Profile} {tgt : CHostSemantics H} {s : Store H} {f : Frame}

/-- `$extend__(n, $size(Inn), sx, c)`, the loaded value of
`Step_read/load-pack-val` (`8-reduction:501`). Named so that the `match` does not
appear under a hypothesis binder in `read_loadPackVal`'s statement. -/
abbrev packExtend (t : IntType) (sz : PackSize) (sx : Signedness) (c : BitVec sz.width) :
    BitVec t.width :=
  match sx with
  | .signed => c.signExtend t.width
  | .unsigned => c.setWidth t.width

/-- `(CONST I32 c)` in Core 3.0, under a name that does not clash with 2.0's
`constI32`. Definitionally `aconst I32 c`, which is what the Core table and
memory rules emit. -/
abbrev cconstI32 (c : BitVec 32) : CAdmin := .plain (.intConst .i32 c)

/-! ## Local bridges

Small facts about the runtime embedding that the rules below use over and over:
the images of a table, an element segment, a memory and a data segment have the
same length/contents, a 2.0 `memarg` has the same effective address, and the
four vector load shapes have the same access width. -/

/-- `$ibytes_`-decoding a byte range is `Execution.Memory.load`. -/
theorem load_of_readBytes {mem : Bytes} {start k : Nat} {cv : BitVec (8 * k)}
    (h : readBytes mem start k = some (ibytes (8 * k) cv)) :
    Silmaril.Wasm.Execution.Memory.load mem start k = some cv := by
  rw [load_eq_invIbytes, h, Option.map_some, invIbytes_ibytes ⟨k, rfl⟩]

/-- Core 3.0's effective address on the image of a 2.0 `memarg`. -/
theorem effAddr_toCore (i : Nat) (ao : MemArg) :
    Silmaril.Wasm.Execution.Core.effAddr i ao.toCore = effAddr i ao := rfl

/-- The four vector load shapes keep their access width. -/
theorem accessWidth_toCoreOpt (op : Option VecLoadOp) :
    (VecLoadOp.toCoreOpt op).accessWidth = VecLoadOp.accessWidth op := by
  rcases op with _ | o
  · rfl
  · cases o <;> rfl

/-- The four vector load shapes assemble their lanes the same way. -/
theorem vecLoadResult_toCoreOpt (op : Option VecLoadOp)
    (cv : BitVec (VecLoadOp.accessWidth op)) :
    Silmaril.Wasm.Execution.Core.vecLoadResult (VecLoadOp.toCoreOpt op) cv
      = vecLoadResult op cv := by
  rcases op with _ | o
  · rfl
  · cases o <;> rfl

theorem table_toCore_length (ti : TableInst) :
    (TableInst.toCore ti).refs.length = ti.refs.length := by simp [TableInst.toCore]

theorem elem_toCore_length (ei : ElemInst) :
    (ElemInst.toCore ei).refs.length = ei.refs.length := by simp [ElemInst.toCore]

theorem table_toCore_getElem? {ti : TableInst} {k : Nat} {r : Ref} (h : ti.refs[k]? = some r) :
    (TableInst.toCore ti).refs[k]? = some r.toCore := by
  simp [TableInst.toCore, List.getElem?_map, h]

theorem elem_toCore_getElem? {ei : ElemInst} {k : Nat} {r : Ref} (h : ei.refs[k]? = some r) :
    (ElemInst.toCore ei).refs[k]? = some r.toCore := by
  simp [ElemInst.toCore, List.getElem?_map, h]

/-- `$inv_signed_` round trip for the sizes that `table.size`/`memory.size`
return. -/
theorem ofNat_toNat32 (n : BitVec 32) : BitVec.ofNat 32 n.toNat = n := by simp

/-- The types of a Core frame's module instance, on the 2.0 image. -/
theorem erase_module_types {f : Frame} {cf : CFrame} (h : f.toCore = ToCore.Frame.erase cf) :
    cf.module.types = f.module.types.map FuncType.toDefType :=
  (congrArg (fun fr : CFrame => fr.module.types) h).symm

/-- `$blocktype(z, bt)` transfers; only the two arities matter. -/
theorem bridge_blockType {f : Frame} {cf : CFrame} (hfr : f.toCore = ToCore.Frame.erase cf)
    {bt : BlockType} {ft : FuncType} (h : f.module.blockType? bt = some ft) :
    ∃ t₁ t₂ : List Silmaril.Wasm.Validation.CValType,
      cf.module.blockType? bt.toCore = some (t₁, t₂) ∧
        t₁.length = ft.params.length ∧ t₂.length = ft.results.length := by
  cases bt with
  | result t =>
    cases t with
    | none =>
      simp only [ModuleInst.blockType?, Option.some.injEq] at h
      subst h
      exact ⟨[], [], rfl, rfl, rfl⟩
    | some v =>
      simp only [ModuleInst.blockType?, Option.some.injEq] at h
      subst h
      exact ⟨[], [cf.module.instVal v.toCore], rfl, rfl, rfl⟩
  | typeIdx x =>
    simp only [ModuleInst.blockType?, ModuleInst.type?] at h
    refine ⟨ft.params.map ValType.toC, ft.results.map ValType.toC, ?_, by simp, by simp⟩
    simp [Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, erase_module_types hfr, h,
      Silmaril.Wasm.Validation.DefType.funcType?, FuncType.toDefType_expand, BlockType.toCore]

/-- `List.mapM` is pointwise on indices. -/
theorem mapM_getElem? {α β : Type*} {g : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM g = some l') {k : Nat} {a : α} (hk : l[k]? = some a) :
    ∃ b, l'[k]? = some b ∧ g a = some b := by
  induction l generalizing l' k with
  | nil => simp at hk
  | cons x xs ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact ⟨b, rfl, hb⟩
    | succ k =>
      obtain ⟨b', hb', hg'⟩ := ih hbs (by simpa using hk)
      exact ⟨b', by simpa using hb', hg'⟩

/-- `$func(z, a)` transfers: the Core store has a function instance at the same
address, and it is the image of the 2.0 one up to the tag erasure. -/
theorem bridge_func {s : Store H} {cs : CStore H}
    (hst : s.toCore = some (ToCore.Store.erase cs)) {a : FuncAddr} {fi : FuncInst H}
    (hf : s.funcInst? a = some fi) :
    ∃ ci : ToCore.CFuncInst H, cs.funcs[a]? = some ci ∧
      FuncInst.toCore fi = some { ci with module := ToCore.ModuleInst.erase ci.module } := by
  simp only [Store.toCore, Option.map_eq_some_iff] at hst
  obtain ⟨fs, hfs, hE⟩ := hst
  have hfuncs : fs = (ToCore.Store.erase cs).funcs := congrArg (fun S => S.funcs) hE
  simp only [Store.funcInst?] at hf
  obtain ⟨cb, hcb, hgb⟩ := mapM_getElem? hfs hf
  rw [hfuncs] at hcb
  simp only [ToCore.Store.erase, List.getElem?_map, Option.map_eq_some_iff] at hcb
  obtain ⟨ci, hci, hg⟩ := hcb
  exact ⟨ci, hci, by rw [hgb, ← hg]⟩

/-- The defined type recorded by the Core image of a store. -/
theorem bridge_funcs_type {s : Store H} {cs : CStore H}
    (hst : s.toCore = some (ToCore.Store.erase cs)) (a : FuncAddr) :
    (cs.funcs[a]?).map (fun fi => fi.type) = (s.funcs[a]?).map (fun fi => fi.type.toDefType) := by
  have h := Store.toCore_funcs_type hst a
  simpa [ToCore.Store.erase, List.getElem?_map, Option.map_map, Function.comp_def] using h

/-- `$func(z, a)` with its defined type. -/
theorem bridge_func_type {s : Store H} {cs : CStore H}
    (hst : s.toCore = some (ToCore.Store.erase cs)) {a : FuncAddr} {fi : FuncInst H}
    (hf : s.funcInst? a = some fi) :
    ∃ ci : ToCore.CFuncInst H, cs.funcs[a]? = some ci ∧
      ci.type = fi.type.toDefType := by
  obtain ⟨ci, hci, -⟩ := bridge_func hst hf
  refine ⟨ci, hci, ?_⟩
  have h := bridge_funcs_type hst a
  rw [hci, show s.funcs[a]? = some fi from hf] at h
  simpa using h

/-- The default value of a 2.0 local, in Core 3.0. -/
theorem defaultVal_toCore (σ : List Silmaril.Wasm.Validation.CTypeUse) (t : ValType) :
    Silmaril.Wasm.Execution.Core.defaultVal?
        ((Silmaril.Wasm.Validation.liftVal t.toCore).substAll σ)
      = some (Val.toCore (defaultVal t)) := by
  rcases t with nt | _ | r
  · cases nt <;> rfl
  · rfl
  · cases r <;> rfl

/-- `$frame` for a call transfers: the Core frame of `Step/call_ref-func` erases
to the image of 2.0's `Step_read/call_addr` frame. -/
theorem forCall_toCore {m : ModuleInst} {cm : CModuleInst}
    (hm : ToCore.ModuleInst.erase cm = m.toCore) (vs : List Val) (ls : List ValType) :
    ToCore.Frame.erase (Silmaril.Wasm.Execution.Core.Frame.forCall cm (vs.map Val.toCore)
      (ls.map ValType.toCore)) = (Frame.forCall m vs ls).toCore := by
  simp only [ToCore.Frame.erase, Silmaril.Wasm.Execution.Core.Frame.forCall, Frame.toCore,
    Frame.forCall, hm, List.map_append, List.map_map]
  refine congrArg (fun l => (⟨l, m.toCore⟩ : CFrame)) ?_
  refine congrArg₂ (· ++ ·) rfl ?_
  exact List.map_congr_left fun t _ => defaultVal_toCore _ t

/-- A code sequence whose image exists has an image for each of its suffixes. -/
theorem listToCore_append_isSome {s : Store H} {xs ys : List Admin} {L : List CAdmin}
    (h : Admin.listToCore s (xs ++ ys) = some L) : (Admin.listToCore s ys).isSome := by
  induction xs generalizing L with
  | nil => simp_all
  | cons a as ih =>
    simp only [List.cons_append, Admin.listToCore_cons, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨u, -, v, hv, -⟩ := h
    exact ih hv

/-! ## Block instructions (`8-reduction:61-74`) -/

theorem read_block {bt : BlockType} {body : List Instr} {vs : List Val} {ft : FuncType}
    (hbt : f.module.blockType? bt = some ft) (hk : vs.length = ft.params.length)
    {c : CConfig H} (hs : Sim ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩ c) :
    Target P tgt ⟨s, f, [.label ft.results.length [] (vals vs ++ expression body)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨t₁, t₂, hbt', h1, h2⟩ := bridge_blockType (sim_frame hs) hbt
  obtain ⟨cbody, hbody⟩ : ∃ cbody, Expr.toCore body = some cbody := by
    have hb := listToCore_append_isSome (ys := [.plain (.block bt body)]) (sim_code hs)
    rcases hc : Expr.toCore body with _ | cbody
    · simp [Instr.toCore, hc] at hb
    · exact ⟨cbody, rfl⟩
  have hbodyimg : Admin.listToCore s (expression body) = some (cbody.map ToCore.plainOrNull) := by
    simp [hbody]
  have hinner : Admin.listToCore s (vals vs ++ expression body)
      = some (cvals (vs.map Val.toCore) ++ cbody.map ToCore.plainOrNull) :=
    listToCore_vals_append s vs hbodyimg
  refine finishNormSame hs (vs := vs.map Val.toCore)
    (R := [.plain (.block bt.toCore cbody)])
    (L' := [.label t₂.length []
      (cvals (vs.map Val.toCore) ++ Silmaril.Wasm.Execution.Core.expression cbody)])
    (listToCore_vals_append s vs (by simp [Instr.toCore, hbody, ToCore.plainOrNull]))
    (by v2rigid) ?_ (by simp) ?_
  · simp only [Admin.listToCore_cons, Admin.listToCore_nil, Admin.label_toCore, hinner,
      Expr.toCore, Option.bind_some, Option.map_some, List.append_nil, List.map_cons,
      List.map_nil, ToCore.Admin.norm_label, List.map_append, map_norm_cvals,
      map_norm_expression hbody, h2]
  · exact .block hbt' (by simp [h1, hk])

theorem read_loop {bt : BlockType} {body : List Instr} {vs : List Val} {ft : FuncType}
    (hbt : f.module.blockType? bt = some ft) (hk : vs.length = ft.params.length)
    {c : CConfig H} (hs : Sim ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩ c) :
    Target P tgt ⟨s, f, [.label ft.params.length [.loop bt body] (vals vs ++ expression body)]⟩ c
    := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨t₁, t₂, hbt', h1, h2⟩ := bridge_blockType (sim_frame hs) hbt
  obtain ⟨cbody, hbody⟩ : ∃ cbody, Expr.toCore body = some cbody := by
    have hb := listToCore_append_isSome (ys := [.plain (.loop bt body)]) (sim_code hs)
    rcases hc : Expr.toCore body with _ | cbody
    · simp [Instr.toCore, hc] at hb
    · exact ⟨cbody, rfl⟩
  have hbodyimg : Admin.listToCore s (expression body) = some (cbody.map ToCore.plainOrNull) := by
    simp [hbody]
  have hinner : Admin.listToCore s (vals vs ++ expression body)
      = some (cvals (vs.map Val.toCore) ++ cbody.map ToCore.plainOrNull) :=
    listToCore_vals_append s vs hbodyimg
  refine finishNormSame hs (vs := vs.map Val.toCore)
    (R := [.plain (.loop bt.toCore cbody)])
    (L' := [.label t₁.length [.loop bt.toCore cbody]
      (cvals (vs.map Val.toCore) ++ Silmaril.Wasm.Execution.Core.expression cbody)])
    (listToCore_vals_append s vs (by simp [Instr.toCore, hbody, ToCore.plainOrNull]))
    (by v2rigid) ?_ (by simp) ?_
  · simp only [Admin.listToCore_cons, Admin.listToCore_nil, Admin.label_toCore, hinner,
      Expr.toCore, Instr.toCore, hbody, Option.bind_some, Option.map_some, List.append_nil,
      List.map_cons, List.map_nil, ToCore.Admin.norm_label, List.map_append, map_norm_cvals,
      map_norm_expression hbody, h1]
  · exact .loop hbt' (by simp [h1, hk])

/-! ## Function instructions (`8-reduction:117-135`) -/

theorem read_call {x : FuncIdx} {a : FuncAddr} (hx : f.module.funcAddr? x = some a)
    {c : CConfig H} (hs : Sim ⟨s, f, [.plain (.call x)]⟩ c) :
    Target P tgt ⟨s, f, [.callAddr a]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  have ha : a < s.funcs.length := (sim_wf hs).2.1 a (List.mem_of_getElem? hx)
  obtain ⟨fL, hfL⟩ : ∃ fL, s.funcs[a]? = some fL := ⟨_, List.getElem?_eq_getElem ha⟩
  have hty := bridge_funcs_type (sim_store hs) a
  rw [hfL] at hty
  obtain ⟨ci, hci⟩ : ∃ ci, cs.funcs[a]? = some ci := by
    cases hc : cs.funcs[a]? with
    | none => rw [hc] at hty; simp at hty
    | some ci => exact ⟨ci, rfl⟩
  rw [hci] at hty
  simp only [Option.map_some, Option.some.injEq] at hty
  have hdt : s.funcDefType a = ci.type := by simp [Store.funcDefType, hfL, hty]
  refine finishSame hs (vs := []) (R := [.plain (.call x)])
    (L' := [.ref (.func a), .callRefType (s.funcDefType a)])
    (by v2img) (by v2rigid) (by v2img) (by simp [ha]) ?_
  rw [hdt]
  exact .call (by rw [erase_module_funcs (sim_frame hs)]; exact hx) hci

/-! ### `call_indirect`

Core 3.0 has no `CALL_ADDR`: `Step_pure/call_indirect` expands to
`TABLE.GET x; REF.CAST (ref null $y); CALL_REF y`, so one 2.0 step is three
Core steps. The cast is what decides between `call_indirect-call` and
`call_indirect-trap`, and `V2.FuncType.toDefType_sub_iff` is what makes the
decision agree with 2.0's type comparison. -/

section CallIndirect

open Silmaril.Wasm.Validation

/-- One Core step under a single value. -/
theorem cstep_prefix {cs cs' : CStore H} {cf cf' : CFrame} (v : CVal)
    {is is' : List CAdmin} (h : CStep P tgt ⟨cs, cf, is⟩ ⟨cs', cf', is'⟩) :
    CStep P tgt ⟨cs, cf, v.toAdmin :: is⟩ ⟨cs', cf', v.toAdmin :: is'⟩ := by
  have h' := Silmaril.Wasm.Execution.Core.Step.ctxtInstrs (P := P) (host := tgt) (vs := [v])
    (rest := ([] : List CAdmin)) h (.inl (by simp))
  simpa [Silmaril.Wasm.Execution.Core.vals] using h'

/-- One Core step with trailing code. -/
theorem cstep_suffix {cs cs' : CStore H} {cf cf' : CFrame} {is is' rest : List CAdmin}
    (hr : rest ≠ []) (h : CStep P tgt ⟨cs, cf, is⟩ ⟨cs', cf', is'⟩) :
    CStep P tgt ⟨cs, cf, is ++ rest⟩ ⟨cs', cf', is' ++ rest⟩ := by
  have h' := Silmaril.Wasm.Execution.Core.Step.ctxtInstrs (P := P) (host := tgt)
    (vs := ([] : List CVal)) (rest := rest) h (.inr hr)
  simpa [Silmaril.Wasm.Execution.Core.vals] using h'

/-- `TRAP` swallows its trailing code. -/
theorem ctrap_rest {cs : CStore H} {cf : CFrame} {rest : List CAdmin} (hr : rest ≠ []) :
    CStep P tgt ⟨cs, cf, .trap :: rest⟩ ⟨cs, cf, [.trap]⟩ := by
  have h' := Silmaril.Wasm.Execution.Core.Step.trapInstrs (P := P) (host := tgt) (s := cs)
    (f := cf) (vs := ([] : List CVal)) (rest := rest) (.inr hr)
  simpa [Silmaril.Wasm.Execution.Core.vals] using h'

/-- `$inst_reftype(f.MODULE, (REF NULL (_IDX y)))` when `y` names a type. -/
theorem instRef_typeIdx {m : CModuleInst} {y : TypeIdx} {d : DefType}
    (h : m.types[y.toNat]? = some d) :
    m.instRef ⟨true, .typeIdx y⟩ = .ref true (.use (.dt d)) := by
  simp [Silmaril.Wasm.Execution.Core.ModuleInst.instRef, liftRef, liftHeap, liftTypeIdx,
    Ty.substAll, Ty.subst, Subst.all, h]

/-- `$inst_reftype(f.MODULE, (REF NULL (_IDX y)))` when `y` names nothing. -/
theorem instRef_typeIdx_none {m : CModuleInst} {y : TypeIdx}
    (h : m.types[y.toNat]? = none) :
    m.instRef ⟨true, .typeIdx y⟩ = .ref true (.use (.idx y.toNat)) := by
  simp [Silmaril.Wasm.Execution.Core.ModuleInst.instRef, liftRef, liftHeap, liftTypeIdx,
    Ty.substAll, Ty.subst, Subst.all, h]

/-- Every 2.0 value type is a Core 3.0 value type. -/
theorem tyOk_toC (Δ : TypeCtx) (t : ValType) : TyOk Δ t.toC := by
  rcases t with nt | vt | r
  · exact TyOk.num nt
  · exact TyOk.vec vt
  · cases r <;> exact TyOk.refv (TyOk.ref (TyOk.abs _))

theorem tyOk_ofList_toC (Δ : TypeCtx) (ts : List ValType) :
    TyOk Δ (Ty.ofList (ts.map ValType.toC)) := by
  induction ts with
  | nil => exact TyOk.nil
  | cons t ts ih => exact TyOk.cons (tyOk_toC Δ t) ih

/-- The defined type of a 2.0 function type is a Core 3.0 defined type. -/
theorem tyOk_toDefType (t : FuncType) : TyOk ({} : TypeCtx) t.toDefType := by
  unfold FuncType.toDefType
  simp only [liftRec, FuncType.toCoreRec, List.map_cons, List.map_nil, liftSub, liftComp,
    FuncType.toCore, liftResult_toCore]
  refine TyOk.defn (GroupOk2.cons (SubOk2.noSuper (TyOk.func ?_ ?_)) GroupOk2.nil)
    (by simp [Ty.length])
  · exact tyOk_ofList_toC _ _
  · exact tyOk_ofList_toC _ _

theorem tyOk_ref_toDefType (n : Bool) (t : FuncType) :
    TyOk ({} : TypeCtx) (Ty.ref n (.use (.dt t.toDefType)) : CRefType) :=
  TyOk.ref (TyOk.use (TyOk.dt (tyOk_toDefType t)))

/-- `(ref null (_IDX y))` with `y` out of range is not even a type, so nothing
has it. -/
theorem not_tyOk_idx {n : Nat} :
    ¬ TyOk ({} : TypeCtx) (Ty.ref true (.use (.idx n)) : CRefType) := by
  intro h
  cases h with
  | ref hh =>
    cases hh with
    | use hu =>
      cases hu with
      | idx hx => simp at hx

/-- The cast of `call_indirect` fails when the type index is out of range. -/
theorem not_refOk_idx {cs : CStore H} {r : CRef} {n : Nat}
    (hr : ∀ rt₀, Silmaril.Wasm.Execution.Core.Ref.type? cs r = some rt₀ →
      rt₀ ≠ (Ty.ref true (.use (.idx n)) : CRefType)) :
    ¬ Silmaril.Wasm.Execution.Core.RefOk cs r (Ty.ref true (.use (.idx n))) := by
  intro hok
  obtain ⟨rt₀, e, hrt, -⟩ := hok.principal
  rcases hrt with hrt | ⟨hok', -⟩
  · exact hr rt₀ e hrt.symm
  · exact not_tyOk_idx hok'

/-- The cast of `call_indirect` fails on a host reference. -/
theorem not_refOk_extern {cs : CStore H} {r : CRef} {t : FuncType} :
    ¬ Silmaril.Wasm.Execution.Core.RefOk cs (.extern r)
      (Ty.ref true (.use (.dt t.toDefType))) := by
  intro hok
  obtain ⟨rt₀, e, hsub, -⟩ :=
    (Silmaril.Wasm.Execution.Core.RefOk.iff_principal _ _ _ (tyOk_ref_toDefType true t)).mp hok
  simp only [Silmaril.Wasm.Execution.Core.Ref.type?, Option.some.injEq] at e
  subst e
  have hc := Sub.check_complete TypeCtx.ok_empty rfl hsub
    (TyOk.ref (TyOk.abs _)) (tyOk_ref_toDefType true t)
  simp [Sub.check, Sub.checkK, TypeCtx.checkRef, TypeCtx.checkHeap, botTop] at hc

/-- The cast of `call_indirect` fails on an unallocated function address. -/
theorem not_refOk_funcNone {cs : CStore H} {a : Nat} {t : FuncType}
    (hf : cs.funcs[a]? = none) :
    ¬ Silmaril.Wasm.Execution.Core.RefOk cs (.func a)
      (Ty.ref true (.use (.dt t.toDefType))) := by
  intro hok
  obtain ⟨rt₀, e, -, -⟩ :=
    (Silmaril.Wasm.Execution.Core.RefOk.iff_principal _ _ _ (tyOk_ref_toDefType true t)).mp hok
  simp [Silmaril.Wasm.Execution.Core.Ref.type?, hf] at e

/-- The cast of `call_indirect` fails on a function of the wrong type: on the
2.0 image, Core 3.0 subtyping of defined types is equality
(`FuncType.toDefType_sub_iff`). -/
theorem not_refOk_func {cs : CStore H} {a : Nat} {ci : ToCore.CFuncInst H}
    (hf : cs.funcs[a]? = some ci) {t₁ t₂ : FuncType} (ht : ci.type = t₁.toDefType)
    (hne : t₁ ≠ t₂) :
    ¬ Silmaril.Wasm.Execution.Core.RefOk cs (.func a)
      (Ty.ref true (.use (.dt t₂.toDefType))) := by
  intro hok
  obtain ⟨rt₀, e, hsub, -⟩ :=
    (Silmaril.Wasm.Execution.Core.RefOk.iff_principal _ _ _ (tyOk_ref_toDefType true t₂)).mp hok
  simp only [Silmaril.Wasm.Execution.Core.Ref.type?, hf, Option.map_some, Option.some.injEq,
    ht] at e
  subst e
  have hc := Sub.check_complete TypeCtx.ok_empty rfl hsub
    (tyOk_ref_toDefType false t₁) (tyOk_ref_toDefType true t₂)
  simp only [Sub.check, Sub.checkK, TypeCtx.checkRef, TypeCtx.checkHeap, Ty.defHeap,
    TypeCtx.resolve, Bool.not_false, Bool.true_or, Bool.true_and] at hc
  exact hne ((FuncType.toDefType_sub_iff _ _ _).mp (TypeCtx.checkDef_sound hc))

theorem read_callIndirectCall {x : TableIdx} {y : TypeIdx} {i : BitVec 32} {ti : TableInst}
    {a : FuncAddr} {fi : FuncInst H} (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (hr : ti.refs[i.toNat]? = some (.funcAddr a)) (hf : s.funcInst? a = some fi)
    (hy : (⟨s, f⟩ : State H).type? y = some fi.type) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩ c) :
    Target P tgt ⟨s, f, [.callAddr a]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨ta, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  obtain ⟨ci, hci, hcitype⟩ := bridge_func_type (sim_store hs) hf
  have hcl : cl = [cconstI32 i, .plain (.callIndirect x y)] := by
    refine ToCore.map_norm_eq_of_rigid (m := cf.module) (by v2rigid) ?_
    have hc := sim_code hs
    rw [show Admin.listToCore s [constI32 i, .plain (.callIndirect x y)]
        = some ([cconstI32 i, .plain (.callIndirect x y)] : List CAdmin) from by v2img] at hc
    exact (Option.some.inj hc).symm
  have hcfy : cf.module.types[y.toNat]? = some fi.type.toDefType := by
    rw [erase_module_types (sim_frame hs)]
    simp only [State.type?, ModuleInst.type?] at hy
    simp [hy]
  have hok : Silmaril.Wasm.Execution.Core.RefOk cs (.func a)
      (cf.module.instRef ⟨true, .typeIdx y⟩) := by
    rw [instRef_typeIdx hcfy]
    have h1 := Silmaril.Wasm.Execution.Core.RefOk.func hci
    rw [hcitype] at h1
    exact .sub h1 (tyOk_ref_toDefType true fi.type)
      (Sub.refNull (Sub.defDef ((FuncType.toDefType_sub_iff _ _ _).mpr rfl)))
  refine finishFrom (P := P) (cs' := cs) (cf' := cf)
    (L' := [.ref (.func a), .plain (.callRef y)]) ?_ ?_ (sim_store hs) (sim_frame hs) ?_
  · rw [hcl]
    refine .head (cstep_prefix (.num ⟨.int .i32, i⟩) .callIndirect) ?_
    refine .head (cstep_suffix (by simp)
      (.table (.getVal (a := .i32) hta (table_toCore_getElem? hr)))) ?_
    exact .single (cstep_suffix (rest := [.plain (.callRef y)]) (by simp)
      (.reference (.castSucceed hok)))
  · simp only [Admin.listToCore_cons, Admin.listToCore_nil, Admin.callAddr_toCore,
      Option.bind_some, Option.map_some, List.append_nil, List.map_cons, List.map_nil,
      ToCore.Admin.norm_ref, ToCore.Admin.norm_plain, ToCore.normPlain_callRef, hcfy,
      Option.getD_some, Store.funcDefType, show s.funcs[a]? = some fi from hf]
  · exact ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp [(List.getElem?_eq_some_iff.mp hf).1]⟩

theorem read_callIndirectTrap {x : TableIdx} {y : TypeIdx} {i : BitVec 32} {ti : TableInst}
    (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (h : ¬ ∃ (a : FuncAddr) (fi : FuncInst H), ti.refs[i.toNat]? = some (.funcAddr a) ∧
      s.funcInst? a = some fi ∧ (⟨s, f⟩ : State H).type? y = some fi.type)
    {c : CConfig H} (hs : Sim ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨ta, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  have hcl : cl = [cconstI32 i, .plain (.callIndirect x y)] := by
    refine ToCore.map_norm_eq_of_rigid (m := cf.module) (by v2rigid) ?_
    have hc := sim_code hs
    rw [show Admin.listToCore s [constI32 i, .plain (.callIndirect x y)]
        = some ([cconstI32 i, .plain (.callIndirect x y)] : List CAdmin) from by v2img] at hc
    exact (Option.some.inj hc).symm
  have htypes : cf.module.types[y.toNat]?
      = (f.module.types[y.toNat]?).map FuncType.toDefType := by
    rw [erase_module_types (sim_frame hs)]; simp
  refine ⟨⟨cs, cf, [.trap]⟩, ?_, simMk (sim_store hs) (sim_frame hs) (by simp)
    ⟨(sim_wf hs).1, (sim_wf hs).2.1, by simp⟩⟩
  rw [hcl]
  refine .head (cstep_prefix (.num ⟨.int .i32, i⟩) .callIndirect) ?_
  rcases hr : ti.refs[i.toNat]? with _ | r
  · refine .head (cstep_suffix (by simp) (.table (.getOob (a := .i32) hta ?_))) ?_
    · simp only [table_toCore_length]
      exact List.getElem?_eq_none_iff.mp hr
    · exact .single (ctrap_rest (by simp))
  · refine .head (cstep_suffix (by simp)
      (.table (.getVal (a := .i32) hta (table_toCore_getElem? hr)))) ?_
    have hfail : ∀ rc : CRef, ¬ Silmaril.Wasm.Execution.Core.RefOk cs rc
        (cf.module.instRef ⟨true, .typeIdx y⟩) →
        CPlus P tgt ⟨cs, cf, [.ref rc] ++ [.plain (.refCast ⟨true, .typeIdx y⟩),
          .plain (.callRef y)]⟩ ⟨cs, cf, [.trap]⟩ := by
      intro rc hno
      refine .head (cstep_suffix (rest := [.plain (.callRef y)]) (by simp)
        (.reference (.castFail hno))) ?_
      exact .single (ctrap_rest (by simp))
    rcases r with rt | fa | ha
    · by_cases hok : Silmaril.Wasm.Execution.Core.RefOk cs (.null : CRef)
        (cf.module.instRef ⟨true, .typeIdx y⟩)
      · refine .head (cstep_suffix (rest := [.plain (.callRef y)]) (by simp)
          (.reference (.castSucceed hok))) ?_
        exact .single (.callRefNull (c := .plain (.callRef y)) trivial)
      · exact hfail _ hok
    · refine hfail (.func fa) ?_
      cases hft : f.module.types[y.toNat]? with
      | none =>
        rw [instRef_typeIdx_none (by rw [htypes, hft]; rfl)]
        refine not_refOk_idx ?_
        rintro rt₀ e rfl
        simp [Silmaril.Wasm.Execution.Core.Ref.type?, Ty.defHeap] at e
      | some ft =>
        rw [instRef_typeIdx (show cf.module.types[y.toNat]? = some ft.toDefType by
          rw [htypes, hft]; rfl)]
        cases hfa : s.funcInst? fa with
        | none =>
          refine not_refOk_funcNone ?_
          have hb := bridge_funcs_type (sim_store hs) fa
          simp only [Store.funcInst?] at hfa
          rw [hfa] at hb
          simpa using hb
        | some fi' =>
          obtain ⟨ci, hci, hcitype⟩ := bridge_func_type (sim_store hs) hfa
          refine not_refOk_func hci hcitype ?_
          intro hEq
          exact h ⟨fa, fi', hr, hfa, by simp [State.type?, ModuleInst.type?, hft, hEq]⟩
    · refine hfail (.extern (.host ha)) ?_
      cases hft : f.module.types[y.toNat]? with
      | none =>
        rw [instRef_typeIdx_none (by rw [htypes, hft]; rfl)]
        refine not_refOk_idx ?_
        rintro rt₀ e rfl
        simp [Silmaril.Wasm.Execution.Core.Ref.type?] at e
      | some ft =>
        rw [instRef_typeIdx (show cf.module.types[y.toNat]? = some ft.toDefType by
          rw [htypes, hft]; rfl)]
        exact not_refOk_extern

end CallIndirect

theorem read_callAddr {a : FuncAddr} {vs : List Val} {fi : FuncInst H} {fn : Func}
    (hf : s.funcInst? a = some fi) (hcode : fi.code = .wasm fn)
    (hk : vs.length = fi.type.params.length) {c : CConfig H}
    (hs : Sim ⟨s, f, vals vs ++ [.callAddr a]⟩ c) :
    Target P tgt ⟨s, f, [.frame fi.type.results.length (Frame.forCall fi.module vs fn.locals)
      [.label fi.type.results.length [] (expression fn.body)]]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨ci, hci, himg⟩ := bridge_func (sim_store hs) hf
  rw [FuncInst.toCore, hcode] at himg
  simp only [Option.map_eq_some_iff] at himg
  obtain ⟨cfn, hcfn, he⟩ := himg
  have hcitype : ci.type = fi.type.toDefType := (congrArg (fun z => z.type) he).symm
  have hcimod : ToCore.ModuleInst.erase ci.module = fi.module.toCore :=
    (congrArg (fun z => z.module) he).symm
  have hcicode : ci.code = .wasm cfn := (congrArg (fun z => z.code) he).symm
  have hbefore : Admin.listToCore s (vals vs ++ [.callAddr a])
      = some (cvals (vs.map Val.toCore) ++ [.ref (.func a)] ++
        [.callRefType (s.funcDefType a)]) := by
    simpa using listToCore_vals_append s vs (rest := [.callAddr a]) (by simp)
  have hmap : cl.map (ToCore.Admin.norm cf.module)
      = cvals (vs.map Val.toCore) ++ [.ref (.func a)] ++
        [.callRefType (s.funcDefType a)] := by
    have h := sim_code hs
    rw [hbefore] at h
    exact (Option.some.inj h).symm
  obtain ⟨t, ht, hsteps⟩ := catchUpSplit (P := P) (tgt := tgt) (cs := cs) (cf := cf)
    (by v2rigid) hmap
  obtain ⟨cx, rfl⟩ : ∃ cx, t = [cx] := by
    rcases t with _ | ⟨cx, t'⟩
    · simp at ht
    · rcases t' with _ | ⟨cy, t''⟩
      · exact ⟨cx, rfl⟩
      · simp at ht
  have hcx : (cx : CAdmin).IsCallRef := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at ht
    rcases ToCore.norm_eq_callRefType ht with rfl | ⟨y, rfl, -⟩ <;> trivial
  have hassoc : cvals (vs.map Val.toCore) ++ [(.ref (.func a) : CAdmin)] ++ [cx]
      = cvals (vs.map Val.toCore) ++ [.ref (.func a), cx] := by simp
  rw [hassoc] at hsteps
  have hexp : Silmaril.Wasm.Validation.Expand ci.type
      (.func (Silmaril.Wasm.Validation.Ty.ofList (fi.type.params.map ValType.toC))
        (Silmaril.Wasm.Validation.Ty.ofList (fi.type.results.map ValType.toC))) := by
    rw [hcitype]
    exact Silmaril.Wasm.Validation.Expand.iff.mpr (FuncType.toDefType_expand _)
  have hstep : CStep P tgt ⟨cs, cf, cvals (vs.map Val.toCore) ++ [.ref (.func a), cx]⟩
      ⟨cs, cf, [.frame fi.type.results.length
        (Silmaril.Wasm.Execution.Core.Frame.forCall ci.module (vs.map Val.toCore) cfn.locals)
        [.label fi.type.results.length []
          (Silmaril.Wasm.Execution.Core.expression cfn.body)]]⟩ := by
    have h := Silmaril.Wasm.Execution.Core.Step.callRefFunc (P := P) (host := tgt)
      (f := cf) (vs := vs.map Val.toCore) hcx hci hexp
      (by simp [Silmaril.Wasm.Validation.Ty.length_ofList, hk]) hcicode
    simpa [Silmaril.Wasm.Validation.Ty.length_ofList] using h
  refine finishFrom (Relation.TransGen.trans_right hsteps (Relation.TransGen.single hstep))
    ?_ (sim_store hs) (sim_frame hs) ?_
  · have hbodyimg : Admin.listToCore s (expression fn.body)
        = some (cfn.body.map ToCore.plainOrNull) := by
      rw [Func.toCore] at hcfn
      simp only [Option.map_eq_some_iff] at hcfn
      obtain ⟨cb, hcb, rfl⟩ := hcfn
      simp [hcb]
    have hfr : (Frame.forCall fi.module vs fn.locals).toCore
        = ToCore.Frame.erase (Silmaril.Wasm.Execution.Core.Frame.forCall ci.module
          (vs.map Val.toCore) cfn.locals) := by
      have hl : cfn.locals = fn.locals.map ValType.toCore := by
        rw [Func.toCore] at hcfn
        simp only [Option.map_eq_some_iff] at hcfn
        obtain ⟨cb, hcb, rfl⟩ := hcfn
        rfl
      rw [hl, forCall_toCore hcimod]
    have hbody' : Expr.toCore fn.body = some cfn.body := by
      rw [Func.toCore] at hcfn
      simp only [Option.map_eq_some_iff] at hcfn
      obtain ⟨cb, hcb, rfl⟩ := hcfn
      exact hcb
    simp only [Admin.listToCore_cons, Admin.listToCore_nil, Admin.frame_toCore,
      Admin.label_toCore, hbodyimg, Expr.toCore, Option.bind_some, Option.map_some,
      List.append_nil, List.map_cons, List.map_nil, ToCore.Admin.norm_frame,
      ToCore.Admin.norm_label, map_norm_expression hbody', hfr]
  · refine ⟨(sim_wf hs).1, (sim_wf hs).2.1, ?_⟩
    simp only [listWF_cons', listWF_nil', WF_frame, WF_label, and_true]
    exact ⟨(sim_wf hs).1.1 _ _ hf, listWF_expression s fn.body⟩

/-! ## Reference, local and global instructions (`8-reduction:210-390`) -/

theorem read_refFunc {x : FuncIdx} {a : FuncAddr} (hx : f.module.funcAddr? x = some a)
    {c : CConfig H} (hs : Sim ⟨s, f, [.plain (.refFunc x)]⟩ c) :
    Target P tgt ⟨s, f, [.refFuncAddr a]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  refine finishSame hs (vs := []) (R := [.plain (.refFunc x)]) (L' := [.ref (.func a)])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  exact .reference (.refFunc (by rw [erase_module_funcs (sim_frame hs)]; exact hx))

theorem read_localGet {x : LocalIdx} {v : Val} (h : (⟨s, f⟩ : State H).local? x = some v)
    {c : CConfig H} (hs : Sim ⟨s, f, [.plain (.localGet x)]⟩ c) :
    Target P tgt ⟨s, f, [v.toAdmin]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  exact finishSame hs (vs := []) (R := [.plain (.localGet x)])
    (L' := [(Val.toCore v).toAdmin]) (by v2img) (by v2rigid) (by v2img) (by simp)
    (.variable (.localGet (bridge_local (sim_frame hs) h)))

theorem read_globalGet {x : GlobalIdx} {gi : GlobalInst}
    (h : (⟨s, f⟩ : State H).global? x = some gi) {c : CConfig H}
    (hs : Sim ⟨s, f, [.plain (.globalGet x)]⟩ c) :
    Target P tgt ⟨s, f, [gi.value.toAdmin]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨a, hga⟩ := bridge_global (sim_store hs) (sim_frame hs) h
  exact finishSame hs (vs := []) (R := [.plain (.globalGet x)])
    (L' := [(Val.toCore gi.value).toAdmin]) (by v2img) (by v2rigid) (by v2img) (by simp)
    (.variable (.globalGet hga))

/-! ## Table instructions (`8-reduction:396-480`) -/

theorem read_tableGetTrap {x : TableIdx} {i : BitVec 32} {ti : TableInst}
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (h : ti.refs.length ≤ i.toNat)
    {c : CConfig H} (hs : Sim ⟨s, f, [constI32 i, .plain (.tableGet x)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨a, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  refine finishSame hs (vs := [.num ⟨.int .i32, i⟩]) (R := [.plain (.tableGet x)])
    (L' := [.trap]) (by v2img) (by v2rigid) (by v2img) (by simp)
    (.table (.getOob (a := .i32) hta ?_))
  simp only [TableInst.toCore, List.length_map]
  exact h

theorem read_tableGetVal {x : TableIdx} {i : BitVec 32} {ti : TableInst} {r : Ref}
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hr : ti.refs[i.toNat]? = some r)
    {c : CConfig H} (hs : Sim ⟨s, f, [constI32 i, .plain (.tableGet x)]⟩ c) :
    Target P tgt ⟨s, f, [aref r]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨a, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  refine finishSame hs (vs := [.num ⟨.int .i32, i⟩]) (R := [.plain (.tableGet x)])
    (L' := [.ref r.toCore]) (by v2img) (by v2rigid) (by v2img) (by simp)
    (.table (.getVal (a := .i32) hta ?_))
  simp only [TableInst.toCore, List.getElem?_map]
  exact congrArg (Option.map Ref.toCore) hr

theorem read_tableSize {x : TableIdx} {ti : TableInst} {n : BitVec 32}
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hn : ti.refs.length = n.toNat)
    {c : CConfig H} (hs : Sim ⟨s, f, [.plain (.tableSize x)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 n]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨a, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  refine finishSame hs (vs := []) (R := [.plain (.tableSize x)])
    (L' := [cconstI32 n]) (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  have hL : ([cconstI32 n] : List CAdmin)
      = [cconstI32 (BitVec.ofNat 32 (TableInst.toCore ti).refs.length)] := by
    rw [table_toCore_length, hn, ofNat_toNat32]
  rw [hL]
  exact .table (.size hta)

theorem read_tableFillTrap {x : TableIdx} {i n : BitVec 32} {v : Val} {ti : TableInst}
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (h : ti.refs.length < i.toNat + n.toNat)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain (.tableFill x)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨a, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  refine finishSame hs (vs := [.num ⟨.int .i32, i⟩, Val.toCore v, .num ⟨.int .i32, n⟩])
    (R := [.plain (.tableFill x)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  exact .table (.fillOob (a := .i32) hta (by simp only [table_toCore_length]; exact h))

theorem read_tableFillZero {x : TableIdx} {i : BitVec 32} {v : Val} {ti : TableInst}
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (h : i.toNat ≤ ti.refs.length)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, v.toAdmin, constI32 0, .plain (.tableFill x)]⟩ c) :
    Target P tgt ⟨s, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨a, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  refine finishSame hs (vs := [.num ⟨.int .i32, i⟩, Val.toCore v, .num ⟨.int .i32, 0⟩])
    (R := [.plain (.tableFill x)]) (L' := [])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  exact .table (.fillZero (a := .i32) hta (by simp only [table_toCore_length]; exact h))

theorem read_tableFillSucc {x : TableIdx} {i n : BitVec 32} {v : Val} {ti : TableInst}
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (h : i.toNat + n.toNat ≤ ti.refs.length)
    (hn : n ≠ 0) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain (.tableFill x)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 i, v.toAdmin, .plain (.tableSet x),
      constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain (.tableFill x)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨a, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  refine finishSame hs (vs := [.num ⟨.int .i32, i⟩, Val.toCore v, .num ⟨.int .i32, n⟩])
    (R := [.plain (.tableFill x)])
    (L' := [cconstI32 i, (Val.toCore v).toAdmin, .plain (.tableSet x),
      cconstI32 (i + 1), (Val.toCore v).toAdmin,
      cconstI32 (n - 1), .plain (.tableFill x)])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  exact .table (.fillSucc (a := .i32) hta (by simp only [table_toCore_length]; exact h) hn)

theorem read_tableCopyTrap {x y : TableIdx} {j i n : BitVec 32} {tx ty : TableInst}
    (hx : (⟨s, f⟩ : State H).table? x = some tx) (hy : (⟨s, f⟩ : State H).table? y = some ty)
    (h : ty.refs.length < i.toNat + n.toNat ∨ tx.refs.length < j.toNat + n.toNat)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨ax, htx⟩ := bridge_table (sim_store hs) (sim_frame hs) hx
  obtain ⟨ay, hty⟩ := bridge_table (sim_store hs) (sim_frame hs) hy
  refine finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩])
    (R := [.plain (.tableCopy x y)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  refine .table (.copyOob (a₁ := .i32) (a₂ := .i32) (a' := .i32) htx hty ?_)
  simp only [table_toCore_length]
  exact h.symm

theorem read_tableCopyZero {x y : TableIdx} {j i : BitVec 32} {tx ty : TableInst}
    (hx : (⟨s, f⟩ : State H).table? x = some tx) (hy : (⟨s, f⟩ : State H).table? y = some ty)
    (h : i.toNat ≤ ty.refs.length ∧ j.toNat ≤ tx.refs.length) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 0, .plain (.tableCopy x y)]⟩ c) :
    Target P tgt ⟨s, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨ax, htx⟩ := bridge_table (sim_store hs) (sim_frame hs) hx
  obtain ⟨ay, hty⟩ := bridge_table (sim_store hs) (sim_frame hs) hy
  refine finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, 0⟩])
    (R := [.plain (.tableCopy x y)]) (L' := [])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  refine .table (.copyZero (a₁ := .i32) (a₂ := .i32) (a' := .i32) htx hty ?_)
  simp only [table_toCore_length]
  exact h.symm

theorem read_tableCopyLe {x y : TableIdx} {j i n : BitVec 32} {tx ty : TableInst}
    (hx : (⟨s, f⟩ : State H).table? x = some tx) (hy : (⟨s, f⟩ : State H).table? y = some ty)
    (h : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length)
    (hn : n ≠ 0) (hle : j.toNat ≤ i.toNat) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 j, constI32 i, .plain (.tableGet y), .plain (.tableSet x),
      constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.tableCopy x y)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨ax, htx⟩ := bridge_table (sim_store hs) (sim_frame hs) hx
  obtain ⟨ay, hty⟩ := bridge_table (sim_store hs) (sim_frame hs) hy
  refine finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩])
    (R := [.plain (.tableCopy x y)])
    (L' := [cconstI32 j, cconstI32 i, .plain (.tableGet y),
      .plain (.tableSet x), cconstI32 (j + 1), cconstI32 (i + 1),
      cconstI32 (n - 1), .plain (.tableCopy x y)])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  refine .table (.copyLe (a₁ := .i32) (a₂ := .i32) (a' := .i32) htx hty ?_ hn hle)
  simp only [table_toCore_length]
  exact h.symm

theorem read_tableCopyGt {x y : TableIdx} {j i n : BitVec 32} {tx ty : TableInst}
    (hx : (⟨s, f⟩ : State H).table? x = some tx) (hy : (⟨s, f⟩ : State H).table? y = some ty)
    (h : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length)
    (hn : n ≠ 0) (hgt : i.toNat < j.toNat) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 (j + n - 1), constI32 (i + n - 1), .plain (.tableGet y),
      .plain (.tableSet x), constI32 j, constI32 i, constI32 (n - 1),
      .plain (.tableCopy x y)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨ax, htx⟩ := bridge_table (sim_store hs) (sim_frame hs) hx
  obtain ⟨ay, hty⟩ := bridge_table (sim_store hs) (sim_frame hs) hy
  refine finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩])
    (R := [.plain (.tableCopy x y)])
    (L' := [cconstI32 (j + n - 1), cconstI32 (i + n - 1),
      .plain (.tableGet y), .plain (.tableSet x), cconstI32 j,
      cconstI32 i, cconstI32 (n - 1), .plain (.tableCopy x y)])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  have hL : ([cconstI32 (j + n - 1), cconstI32 (i + n - 1),
      .plain (.tableGet y), .plain (.tableSet x), cconstI32 j,
      cconstI32 i, cconstI32 (n - 1),
      .plain (.tableCopy x y)] : List CAdmin)
      = [cconstI32 (j + BitVec.ofNat 32 n.toNat - 1),
        cconstI32 (i + BitVec.ofNat 32 n.toNat - 1),
        .plain (.tableGet y), .plain (.tableSet x), cconstI32 j,
        cconstI32 i, cconstI32 (n - 1),
        .plain (.tableCopy x y)] := by
    rw [ofNat_toNat32]
  rw [hL]
  refine .table (.copyGt (a₁ := .i32) (a₂ := .i32) (a' := .i32) htx hty ?_ hn hgt)
  simp only [table_toCore_length]
  exact h.symm

theorem read_tableInitTrap {x : TableIdx} {y : ElemIdx} {j i n : BitVec 32} {ti : TableInst}
    {ei : ElemInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (he : (⟨s, f⟩ : State H).elem? y = some ei)
    (h : ei.refs.length < i.toNat + n.toNat ∨ ti.refs.length < j.toNat + n.toNat)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableInit x y)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨at_, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  obtain ⟨ae, hea⟩ := bridge_elem (sim_store hs) (sim_frame hs) he
  refine finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩])
    (R := [.plain (.tableInit x y)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  refine .table (.initOob (a := .i32) hta hea ?_)
  simp only [table_toCore_length, elem_toCore_length]
  exact h.symm

theorem read_tableInitZero {x : TableIdx} {y : ElemIdx} {j i : BitVec 32} {ti : TableInst}
    {ei : ElemInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (he : (⟨s, f⟩ : State H).elem? y = some ei)
    (h : i.toNat ≤ ei.refs.length ∧ j.toNat ≤ ti.refs.length) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 0, .plain (.tableInit x y)]⟩ c) :
    Target P tgt ⟨s, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨at_, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  obtain ⟨ae, hea⟩ := bridge_elem (sim_store hs) (sim_frame hs) he
  refine finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, 0⟩])
    (R := [.plain (.tableInit x y)]) (L' := [])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  refine .table (.initZero (a := .i32) hta hea ?_)
  simp only [table_toCore_length, elem_toCore_length]
  exact h.symm

theorem read_tableInitSucc {x : TableIdx} {y : ElemIdx} {j i n : BitVec 32} {ti : TableInst}
    {ei : ElemInst} {r : Ref} (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (he : (⟨s, f⟩ : State H).elem? y = some ei)
    (h : i.toNat + n.toNat ≤ ei.refs.length ∧ j.toNat + n.toNat ≤ ti.refs.length)
    (hn : n ≠ 0) (hr : ei.refs[i.toNat]? = some r) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableInit x y)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 j, aref r, .plain (.tableSet x),
      constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.tableInit x y)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨at_, hta⟩ := bridge_table (sim_store hs) (sim_frame hs) ht
  obtain ⟨ae, hea⟩ := bridge_elem (sim_store hs) (sim_frame hs) he
  refine finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩])
    (R := [.plain (.tableInit x y)])
    (L' := [cconstI32 j, .ref r.toCore, .plain (.tableSet x),
      cconstI32 (j + 1), cconstI32 (i + 1),
      cconstI32 (n - 1), .plain (.tableInit x y)])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  refine .table (.initSucc (a := .i32) hta hea ?_ hn (elem_toCore_getElem? hr))
  simp only [table_toCore_length, elem_toCore_length]
  exact h.symm

/-! ## Memory loads (`8-reduction:487-556`) -/

theorem read_loadIntTrap {t : IntType} {ao : MemArg} {i : BitVec 32} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.intLoad t none ao)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩])
    (R := [.plain (.intLoad t none ⟨0⟩ ao.toCore)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.loadIntOob (a := .i32) (x := ⟨0⟩) hma h))

theorem read_loadIntVal {t : IntType} {ao : MemArg} {i : BitVec 32} {mi : MemInst}
    {cv : BitVec t.width} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hb : readBytes mi.bytes (effAddr i.toNat ao) (t.width / 8) = some (nbytes (.int t) cv))
    {c : CConfig H} (hs : Sim ⟨s, f, [constI32 i, .plain (.intLoad t none ao)]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.intConst t cv)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  have hstep : CStep P tgt ⟨cs, cf, [cconstI32 i,
      .plain (.intLoad t none ⟨0⟩ ao.toCore)]⟩ ⟨cs, cf, [.plain (.intConst t cv)]⟩ := by
    cases t <;>
      (rw [← BitVec.setWidth_eq cv]
       exact .memory (.loadIntVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb)))
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩])
    (R := [.plain (.intLoad t none ⟨0⟩ ao.toCore)]) (L' := [.plain (.intConst t cv)])
    (by v2img) (by v2rigid) (by v2img) (by simp) hstep

theorem read_loadFloatTrap {t : FloatType} {ao : MemArg} {i : BitVec 32} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (h : mi.bytes.size < effAddr i.toNat ao + t.width / 8) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.floatLoad t ao)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩])
    (R := [.plain (.floatLoad t ⟨0⟩ ao.toCore)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.loadFloatOob (a := .i32) (x := ⟨0⟩) hma h))

theorem read_loadFloatVal {t : FloatType} {ao : MemArg} {i : BitVec 32} {mi : MemInst}
    {cv : BitVec t.width} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hb : readBytes mi.bytes (effAddr i.toNat ao) (t.width / 8) = some (fbytes t cv))
    {c : CConfig H} (hs : Sim ⟨s, f, [constI32 i, .plain (.floatLoad t ao)]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.floatConst t cv)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  have hstep : CStep P tgt ⟨cs, cf, [cconstI32 i,
      .plain (.floatLoad t ⟨0⟩ ao.toCore)]⟩ ⟨cs, cf, [.plain (.floatConst t cv)]⟩ := by
    cases t <;>
      (rw [← BitVec.setWidth_eq cv]
       exact .memory (.loadFloatVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb)))
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩])
    (R := [.plain (.floatLoad t ⟨0⟩ ao.toCore)]) (L' := [.plain (.floatConst t cv)])
    (by v2img) (by v2rigid) (by v2img) (by simp) hstep

theorem read_loadPackTrap {t : IntType} {sz : PackSize} {sx : Signedness} {ao : MemArg}
    {i : BitVec 32} {mi : MemInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩])
    (R := [.plain (.intLoad t (some (sz, sx)) ⟨0⟩ ao.toCore)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.loadPackOob (a := .i32) (x := ⟨0⟩) hma h))

theorem read_loadPackVal {t : IntType} {sz : PackSize} {sx : Signedness} {ao : MemArg}
    {i : BitVec 32} {mi : MemInst} {cv : BitVec sz.width}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hb : readBytes mi.bytes (effAddr i.toNat ao) (sz.width / 8) = some (ibytes sz.width cv))
    {c : CConfig H} (hs : Sim ⟨s, f, [constI32 i, .plain (.intLoad t (some (sz, sx)) ao)]⟩ c) :
    Target P tgt ⟨s, f, [.plain (.intConst t (packExtend t sz sx cv))]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  have hstep : CStep P tgt ⟨cs, cf, [cconstI32 i,
      .plain (.intLoad t (some (sz, sx)) ⟨0⟩ ao.toCore)]⟩
      ⟨cs, cf, [.plain (.intConst t (packExtend t sz sx cv))]⟩ := by
    cases sz <;>
      exact .memory (.loadPackVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb))
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩])
    (R := [.plain (.intLoad t (some (sz, sx)) ⟨0⟩ ao.toCore)])
    (L' := [.plain (.intConst t (packExtend t sz sx cv))])
    (by v2img) (by v2rigid) (by v2img) (by simp) hstep

theorem read_vecLoadOob {op : Option VecLoadOp} {ao : MemArg} {i : BitVec 32} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (h : mi.bytes.size < effAddr i.toNat ao + VecLoadOp.accessWidth op / 8) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.vecLoad op ao)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  refine finishSame hs (vs := [.num ⟨.int .i32, i⟩])
    (R := [.plain (.vecLoad (VecLoadOp.toCoreOpt op) ⟨0⟩ ao.toCore)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  refine .memory (.vecLoadOob (a := .i32) (x := ⟨0⟩) hma ?_)
  rw [accessWidth_toCoreOpt]
  exact h

theorem read_vecLoadVal {op : Option VecLoadOp} {ao : MemArg} {i : BitVec 32} {mi : MemInst}
    {cv : BitVec (VecLoadOp.accessWidth op)} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hb : readBytes mi.bytes (effAddr i.toNat ao) (VecLoadOp.accessWidth op / 8)
      = some (ibytes (VecLoadOp.accessWidth op) cv)) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, .plain (.vecLoad op ao)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (vecLoadResult op cv)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  have hstep : CStep P tgt ⟨cs, cf, [cconstI32 i,
      .plain (.vecLoad (VecLoadOp.toCoreOpt op) ⟨0⟩ ao.toCore)]⟩
      ⟨cs, cf, [.plain (.vecConst (vecLoadResult op cv))]⟩ := by
    rw [← vecLoadResult_toCoreOpt op cv]
    -- `Nat` division does not reduce under a free variable, so the sign and the
    -- packed size of the shape have to be case-split as well.
    rcases op with _ | o
    · exact .memory (.vecLoadVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb))
    · cases o with
      | shape8x8 sx =>
        cases sx <;>
          exact .memory (.vecLoadVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb))
      | shape16x4 sx =>
        cases sx <;>
          exact .memory (.vecLoadVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb))
      | shape32x2 sx =>
        cases sx <;>
          exact .memory (.vecLoadVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb))
      | splat sz =>
        cases sz <;>
          exact .memory (.vecLoadVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb))
      | zero32 =>
        exact .memory (.vecLoadVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb))
      | zero64 =>
        exact .memory (.vecLoadVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb))
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩])
    (R := [.plain (.vecLoad (VecLoadOp.toCoreOpt op) ⟨0⟩ ao.toCore)])
    (L' := [.plain (.vecConst (vecLoadResult op cv))])
    (by v2img) (by v2rigid) (by v2img) (by simp) hstep

theorem read_vecLoadLaneOob {sz : PackSize} {ao : MemArg} {j : LaneIdx} {i : BitVec 32}
    {c₁ : V128} {mi : MemInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, vconst c₁, .plain (.vecLoadLane sz ao j)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, .vec c₁])
    (R := [.plain (.vecLoadLane sz ⟨0⟩ ao.toCore j)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.vecLoadLaneOob (a := .i32) (x := ⟨0⟩) hma h))

theorem read_vecLoadLaneVal {sz : PackSize} {ao : MemArg} {j : LaneIdx} {i : BitVec 32}
    {c₁ : V128} {mi : MemInst} {k : BitVec sz.width}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) (hj : j.val < 128 / sz.width)
    (hb : readBytes mi.bytes (effAddr i.toNat ao) (sz.width / 8) = some (ibytes sz.width k))
    {c : CConfig H} (hs : Sim ⟨s, f, [constI32 i, vconst c₁, .plain (.vecLoadLane sz ao j)]⟩ c) :
    Target P tgt ⟨s, f, [vconst (Numerics.invLanes sz.width
      ((Numerics.lanes sz.width (128 / sz.width) c₁).set j.val k))]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  have hstep : CStep P tgt ⟨cs, cf, [cconstI32 i, .plain (.vecConst c₁),
      .plain (.vecLoadLane sz ⟨0⟩ ao.toCore j)]⟩
      ⟨cs, cf, [.plain (.vecConst (Numerics.invLanes sz.width
        ((Numerics.lanes sz.width (128 / sz.width) c₁).set j.val k)))]⟩ := by
    cases sz <;>
      (rw [← BitVec.setWidth_eq k]
       exact .memory (.vecLoadLaneVal (a := .i32) (x := ⟨0⟩) hma (load_of_readBytes hb)))
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, .vec c₁])
    (R := [.plain (.vecLoadLane sz ⟨0⟩ ao.toCore j)])
    (L' := [.plain (.vecConst (Numerics.invLanes sz.width
      ((Numerics.lanes sz.width (128 / sz.width) c₁).set j.val k)))])
    (by v2img) (by v2rigid) (by v2img) (by simp) hstep

/-! ## Memory size and bulk operations (`8-reduction:595-660`) -/

theorem read_memorySize {mi : MemInst} {n : BitVec 32}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) (hn : n.toNat * pageSize = mi.bytes.size)
    {c : CConfig H} (hs : Sim ⟨s, f, [.plain .memorySize]⟩ c) :
    Target P tgt ⟨s, f, [constI32 n]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  refine finishSame hs (vs := []) (R := [.plain (.memorySize ⟨0⟩)]) (L' := [cconstI32 n])
    (by v2img) (by v2rigid) (by v2img) (by simp) ?_
  have hp : (MemInst.toCore mi).pages = n.toNat := by
    simp only [MemInst.toCore, Silmaril.Wasm.Execution.Core.MemInst.pages, ← hn,
      Silmaril.Wasm.Execution.Memory.pageSize]
    omega
  have hL : ([cconstI32 n] : List CAdmin)
      = [cconstI32 (BitVec.ofNat 32 (MemInst.toCore mi).pages)] := by
    rw [hp, ofNat_toNat32]
  rw [hL]
  exact .memory (.size hma)

theorem read_memoryFillTrap {i n : BitVec 32} {v : Val} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) (h : mi.bytes.size < i.toNat + n.toNat)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, Val.toCore v, .num ⟨.int .i32, n⟩])
    (R := [.plain (.memoryFill ⟨0⟩)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.fillOob (a := .i32) (x := ⟨0⟩) hma h))

theorem read_memoryFillZero {i : BitVec 32} {v : Val} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) (h : i.toNat ≤ mi.bytes.size)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, v.toAdmin, constI32 0, .plain .memoryFill]⟩ c) :
    Target P tgt ⟨s, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, Val.toCore v, .num ⟨.int .i32, 0⟩])
    (R := [.plain (.memoryFill ⟨0⟩)]) (L' := [])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.fillZero (a := .i32) (x := ⟨0⟩) hma h))

theorem read_memoryFillSucc {i n : BitVec 32} {v : Val} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) (h : i.toNat + n.toNat ≤ mi.bytes.size)
    (hn : n ≠ 0) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩ c) :
    Target P tgt ⟨s, f, [constI32 i, v.toAdmin, store8,
      constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain .memoryFill]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  exact finishSame hs (vs := [.num ⟨.int .i32, i⟩, Val.toCore v, .num ⟨.int .i32, n⟩])
    (R := [.plain (.memoryFill ⟨0⟩)])
    (L' := [cconstI32 i, (Val.toCore v).toAdmin,
      .plain (.intStore .i32 (some .i8) ⟨0⟩ memarg0.toCore),
      cconstI32 (i + 1), (Val.toCore v).toAdmin,
      cconstI32 (n - 1), .plain (.memoryFill ⟨0⟩)])
    (by v2img) (by v2rigid) (by v2img) (by simp [store8])
    (.memory (.fillSucc (a := .i32) (x := ⟨0⟩) hma h hn))

theorem read_memoryCopyTrap {j i n : BitVec 32} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (h : mi.bytes.size < i.toNat + n.toNat ∨ mi.bytes.size < j.toNat + n.toNat)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  exact finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩])
    (R := [.plain (.memoryCopy ⟨0⟩ ⟨0⟩)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.copyOob (a₁ := .i32) (a₂ := .i32) (a' := .i32) hma hma h.symm))

theorem read_memoryCopyZero {j i : BitVec 32} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (h : i.toNat ≤ mi.bytes.size ∧ j.toNat ≤ mi.bytes.size) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 0, .plain .memoryCopy]⟩ c) :
    Target P tgt ⟨s, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  exact finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, 0⟩])
    (R := [.plain (.memoryCopy ⟨0⟩ ⟨0⟩)]) (L' := [])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.copyZero (a₁ := .i32) (a₂ := .i32) (a' := .i32) hma hma h.symm))

theorem read_memoryCopyLe {j i n : BitVec 32} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (h : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size)
    (hn : n ≠ 0) (hle : j.toNat ≤ i.toNat) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]⟩ c) :
    Target P tgt ⟨s, f, [constI32 j, constI32 i, load8u, store8,
      constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain .memoryCopy]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  exact finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩])
    (R := [.plain (.memoryCopy ⟨0⟩ ⟨0⟩)])
    (L' := [cconstI32 j, cconstI32 i,
      .plain (.intLoad .i32 (some (.i8, .unsigned)) ⟨0⟩ memarg0.toCore),
      .plain (.intStore .i32 (some .i8) ⟨0⟩ memarg0.toCore),
      cconstI32 (j + 1), cconstI32 (i + 1),
      cconstI32 (n - 1), .plain (.memoryCopy ⟨0⟩ ⟨0⟩)])
    (by v2img) (by v2rigid) (by v2img) (by simp [store8, load8u])
    (.memory (.copyLe (a₁ := .i32) (a₂ := .i32) (a' := .i32) hma hma h.symm hn hle))

theorem read_memoryCopyGt {j i n : BitVec 32} {mi : MemInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (h : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size)
    (hn : n ≠ 0) (hgt : i.toNat < j.toNat) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]⟩ c) :
    Target P tgt ⟨s, f, [constI32 (j + n - 1), constI32 (i + n - 1), load8u, store8,
      constI32 j, constI32 i, constI32 (n - 1), .plain .memoryCopy]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  refine finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩])
    (R := [.plain (.memoryCopy ⟨0⟩ ⟨0⟩)])
    (L' := [cconstI32 (j + n - 1), cconstI32 (i + n - 1),
      .plain (.intLoad .i32 (some (.i8, .unsigned)) ⟨0⟩ memarg0.toCore),
      .plain (.intStore .i32 (some .i8) ⟨0⟩ memarg0.toCore),
      cconstI32 j, cconstI32 i,
      cconstI32 (n - 1), .plain (.memoryCopy ⟨0⟩ ⟨0⟩)])
    (by v2img) (by v2rigid) (by v2img) (by simp [store8, load8u]) ?_
  have hL : ([cconstI32 (j + n - 1), cconstI32 (i + n - 1),
      .plain (.intLoad .i32 (some (.i8, .unsigned)) ⟨0⟩ memarg0.toCore),
      .plain (.intStore .i32 (some .i8) ⟨0⟩ memarg0.toCore),
      cconstI32 j, cconstI32 i,
      cconstI32 (n - 1), .plain (.memoryCopy ⟨0⟩ ⟨0⟩)] : List CAdmin)
      = [cconstI32 (j + BitVec.ofNat 32 n.toNat - 1),
        cconstI32 (i + BitVec.ofNat 32 n.toNat - 1),
        .plain (.intLoad .i32 (some (.i8, .unsigned)) ⟨0⟩ memarg0.toCore),
        .plain (.intStore .i32 (some .i8) ⟨0⟩ memarg0.toCore),
        cconstI32 j, cconstI32 i,
        cconstI32 (n - 1), .plain (.memoryCopy ⟨0⟩ ⟨0⟩)] := by
    rw [ofNat_toNat32]
  rw [hL]
  exact .memory (.copyGt (a₁ := .i32) (a₂ := .i32) (a' := .i32) hma hma h.symm hn hgt)

theorem read_memoryInitTrap {x : DataIdx} {j i n : BitVec 32} {mi : MemInst} {di : DataInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hd : (⟨s, f⟩ : State H).data? x = some di)
    (h : di.bytes.size < i.toNat + n.toNat ∨ mi.bytes.size < j.toNat + n.toNat)
    {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.memoryInit x)]⟩ c) :
    Target P tgt ⟨s, f, [.trap]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  obtain ⟨ad, hda⟩ := bridge_data (sim_store hs) (sim_frame hs) hd
  exact finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩])
    (R := [.plain (.memoryInit ⟨0⟩ x)]) (L' := [.trap])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.initOob (a := .i32) (x := ⟨0⟩) hma hda h.symm))

theorem read_memoryInitZero {x : DataIdx} {j i : BitVec 32} {mi : MemInst} {di : DataInst}
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hd : (⟨s, f⟩ : State H).data? x = some di)
    (h : i.toNat ≤ di.bytes.size ∧ j.toNat ≤ mi.bytes.size) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 0, .plain (.memoryInit x)]⟩ c) :
    Target P tgt ⟨s, f, []⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  obtain ⟨ad, hda⟩ := bridge_data (sim_store hs) (sim_frame hs) hd
  exact finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, 0⟩])
    (R := [.plain (.memoryInit ⟨0⟩ x)]) (L' := [])
    (by v2img) (by v2rigid) (by v2img) (by simp)
    (.memory (.initZero (a := .i32) (x := ⟨0⟩) hma hda h.symm))

theorem read_memoryInitSucc {x : DataIdx} {j i n : BitVec 32} {mi : MemInst} {di : DataInst}
    {b : UInt8} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
    (hd : (⟨s, f⟩ : State H).data? x = some di)
    (h : i.toNat + n.toNat ≤ di.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size)
    (hn : n ≠ 0) (hb : di.bytes.data[i.toNat]? = some b) {c : CConfig H}
    (hs : Sim ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.memoryInit x)]⟩ c) :
    Target P tgt ⟨s, f, [constI32 j, constI32 (BitVec.ofNat 32 b.toNat), store8,
      constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.memoryInit x)]⟩ c := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨am, hma⟩ := bridge_mem (sim_store hs) (sim_frame hs) hm
  obtain ⟨ad, hda⟩ := bridge_data (sim_store hs) (sim_frame hs) hd
  exact finishSame hs (vs := [.num ⟨.int .i32, j⟩, .num ⟨.int .i32, i⟩, .num ⟨.int .i32, n⟩])
    (R := [.plain (.memoryInit ⟨0⟩ x)])
    (L' := [cconstI32 j, cconstI32 (BitVec.ofNat 32 b.toNat),
      .plain (.intStore .i32 (some .i8) ⟨0⟩ memarg0.toCore),
      cconstI32 (j + 1), cconstI32 (i + 1),
      cconstI32 (n - 1), .plain (.memoryInit ⟨0⟩ x)])
    (by v2img) (by v2rigid) (by v2img) (by simp [store8])
    (.memory (.initSucc (a := .i32) (x := ⟨0⟩) hma hda h.symm hn hb))

end Silmaril.Wasm.V2.Execution.ToCoreSim
