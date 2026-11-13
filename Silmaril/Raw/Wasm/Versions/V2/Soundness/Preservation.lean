module

public import Silmaril.Raw.Wasm.Versions.V2.Soundness.PresPure

/-!
# WebAssembly 2.0 soundness: preservation (subject reduction)

`Step.preservation`: a well-typed configuration steps to a well-typed
configuration at the *same* result type, over an extended store.

**Deviation (no SpecTec source).** As recorded in
`Silmaril/Wasm/V2/Soundness/Store.lean`, the pinned SpecTec wasm-2.0 sources
(WebAssembly/spec `608711107b7f1edb13efd57b7d79b49477462d36`, see
`specs/wasm/core-2.0.json`) contain **no `7-soundness` file**, so 2.0 states no
preservation theorem. The statement below is the W3C WebAssembly 2.0 appendix
*Soundness*, theorem "Preservation", cross-checked against the Core 3.0
development (`Silmaril/Wasm/Execution/Core/Soundness/Preservation.lean`).

## The generalised invariant

Core 3.0 needs `Step.preservation_gen` with a *context ordering*: a 3.0 step may
initialise a local, so the typing context the code is checked in moves. **2.0
has no local-initialization tracking**, so nothing of the sort is needed: the
only 2.0 rule that touches the frame is `Step/local.set` (`8-reduction:380`),
which changes a local's *value* and not its type, so `Frame_ok` is preserved
with the *same* context.

What is still needed is the separation between

* the **frame context** `Cf`, the context `Frame_ok` assigns to the current
  frame (`ModuleInstOk`'s module-level context plus the locals), which has
  `LABELS = eps` and `RETURN = eps`; and
* the **typing context** `Ct`, in which the code is actually checked, which is
  `Cf` with labels pushed by `AdminOk.label` and a return type set by
  `AdminOk.frame`.

`CtxUnder Ct Cf` says exactly that: `Ct` and `Cf` agree on every field except
`LABELS` and `RETURN`. `Step.preservation_gen` is stated for an arbitrary such
pair, which is what makes the three context rules `Step/ctxt-instrs`,
`Step/ctxt-label` and `Step/ctxt-frame` go through. `Step.preservation` is the
instance `Ct = Cf = C`.

## What is proved

**Everything: this file and `Soundness/PresPure.lean` contain no `sorry`.**
`Step.preservation` depends only on `propext`, `Classical.choice` and
`Quot.sound`.

The proof is one induction on `Step`, with one lemma per group of rules of
`8-reduction`:

| family | rules | lemma |
| --- | --- | --- |
| pure (all eight families) | `Step_pure/*` | `PureStep.preservation` (`PresPure.lean`) |
| block | `Step_read/block`, `/loop` | `pres_read_block`, `pres_read_loop` |
| call | `/call`, `/call_indirect-*`, `/call_addr` | `pres_read_call`, `pres_read_callIndirect`, `pres_read_callAddr` |
| reference | `/ref.func` | `pres_read_refFunc` |
| local | `/local.get`, `Step/local.set` | `pres_read_localGet`, `pres_localSet` |
| global | `/global.get`, `Step/global.set` | `pres_read_globalGet`, `pres_globalSet` |
| table | `/table.get-val`, the bulk loops, `Step/table.set-val`, `/table.grow-*` | `pres_read_tableGetVal`, `pres_read_tableFillSucc`, `pres_read_tableCopy`, `pres_read_tableInitSucc`, `pres_tableSetVal`, `pres_tableGrowSucceed` |
| memory | the loads, the bulk loops, `Step/store-*`, `/vstore*`, `/memory.grow-*` | `pres_read_memoryFillSucc`, `pres_read_memoryCopy`, `pres_read_memoryInitSucc`, `pres_memoryWrite`, `pres_memoryGrowSucceed` |
| data/elem | `Step/data.drop`, `/elem.drop` | `pres_dataDrop`, `pres_elemDrop` |
| host | `Step/call_addr` on a host function | `pres_callAddrHost` |

Every `-trap`, `-oob` and `-fail` rule is discharged by `AdminsOk.trap_it` or
by one of the flat-redex lemmas of `PresPure.lean`; every `-zero` rule by
`AdminsOk.flat3_nil`.

## Bridges and store updates

Two reusable layers sit between the typing judgments and the reduction:

* the **bridges** `FrameOk.func_bridge`, `.global_bridge`, `.table_bridge`,
  `.elem_bridge` and `FrameOk.types_eq`, which turn an index into the *context*
  into an instance of the *store* whose type is at or below the declared one
  (`ExternAddrOk` has a `sub` rule, so table and memory types come back only up
  to `Tabletype_sub`/`Memtype_sub`, which is exactly what the rules need);
* the **store updates** `Extend.setXInst` and `StoreOk.setXInst`, which rebuild
  `Extend_store` and `Store_ok` from the one-instance fact. `StoreOk.mk_of_extend`
  is the shared worker: every instance of the new store is either an old one
  (carried over by `*Ok.extend`) or the single new one.

-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Memory (Bytes pageSize)

variable {H : Type}

/-! ## List lemmas

Two facts about `List.Forall₂` that the frame and the context bridges need. -/

/-- A pointwise relation survives overwriting one entry with a related value. -/
theorem forall₂_set {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ (i : Nat) (a : α) (b : β), l₂[i]? = some b → R a b →
      List.Forall₂ R (l₁.set i a) l₂ := by
  induction h with
  | nil => intro i a b hi _; simp at hi
  | cons hx hs ih =>
    intro i a b hi ha
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact .cons ha hs
    | succ n =>
      simp only [List.getElem?_cons_succ] at hi
      exact .cons hx (ih n a b hi ha)

/-- A pointwise relation transports an index resolution on the right to one on
the left. -/
theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ (i : Nat) (b : β), l₂[i]? = some b →
      ∃ a, l₁[i]? = some a ∧ R a b := by
  induction h with
  | nil => intro i b hi; simp at hi
  | cons hx hs ih =>
    intro i b hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨_, rfl, hx⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨a, ha, hR⟩ := ih n b hi
      exact ⟨a, by simpa using ha, hR⟩

/-! ## Reflexivity and transitivity of the external subtype relations

`Validation/Types.lean` proves these for `Limits` and `ExternType`; the three
intermediate ones are immediate and are stated here because the inversions of
`ExternAddrOk` below need them. -/

theorem TableType.sub_refl (tt : TableType) : TableType.Sub tt tt :=
  ⟨Limits.sub_refl _, rfl⟩

theorem TableType.sub_trans {a b c : TableType} (h₁ : TableType.Sub a b)
    (h₂ : TableType.Sub b c) : TableType.Sub a c :=
  ⟨Limits.sub_trans h₁.1 h₂.1, h₁.2.trans h₂.2⟩

theorem MemoryType.sub_refl (mt : MemoryType) : MemoryType.Sub mt mt := Limits.sub_refl _

theorem MemoryType.sub_trans {a b c : MemoryType} (h₁ : MemoryType.Sub a b)
    (h₂ : MemoryType.Sub b c) : MemoryType.Sub a c := Limits.sub_trans h₁ h₂

/-! ## Inversion of `ExternAddrOk`

The `sub` rule (`Execution/Instantiation.lean`) means an external address is
typed *at or below* the instance's own type, so each inversion returns the
instance together with a `*type.Sub`. In 2.0 `Functype_sub` and
`Globaltype_sub` are equality (`6-typing:105`, `108`), so those two inversions
return the type on the nose. -/

theorem ExternAddrOk.func_inv_aux {s : Store H} {xa : ExternAddr} {xt : ExternType}
    (h : ExternAddrOk s xa xt) : ∀ a ft, xa = .func a → xt = .func ft →
      ∃ fi, s.funcInst? a = some fi ∧ fi.type = ft := by
  induction h with
  | func hfi =>
    rintro a ft h1 h2; injection h1 with h1; subst h1
    injection h2 with h2; exact ⟨_, hfi, h2⟩
  | global _ => rintro a ft h1 _; cases h1
  | table _ => rintro a ft h1 _; cases h1
  | mem _ => rintro a ft h1 _; cases h1
  | sub _ _ hsub ih =>
    rintro a ft rfl h2
    cases hsub with
    | func hs =>
      injection h2 with h2
      obtain ⟨fi, hfi, rfl⟩ := ih a _ rfl rfl
      exact ⟨fi, hfi, hs.trans h2⟩
    | global _ => cases h2
    | table _ => cases h2
    | memory _ => cases h2

theorem ExternAddrOk.func_inv {s : Store H} {a : FuncAddr} {ft : FuncType}
    (h : ExternAddrOk s (.func a) (.func ft)) : ∃ fi, s.funcInst? a = some fi ∧ fi.type = ft :=
  h.func_inv_aux a ft rfl rfl

theorem ExternAddrOk.global_inv_aux {s : Store H} {xa : ExternAddr} {xt : ExternType}
    (h : ExternAddrOk s xa xt) : ∀ a gt, xa = .global a → xt = .global gt →
      ∃ gi, s.globalInst? a = some gi ∧ gi.type = gt := by
  induction h with
  | global hgi =>
    rintro a gt h1 h2; injection h1 with h1; subst h1
    injection h2 with h2; exact ⟨_, hgi, h2⟩
  | func _ => rintro a gt h1 _; cases h1
  | table _ => rintro a gt h1 _; cases h1
  | mem _ => rintro a gt h1 _; cases h1
  | sub _ _ hsub ih =>
    rintro a gt rfl h2
    cases hsub with
    | global hs =>
      injection h2 with h2
      obtain ⟨gi, hgi, rfl⟩ := ih a _ rfl rfl
      exact ⟨gi, hgi, hs.trans h2⟩
    | func _ => cases h2
    | table _ => cases h2
    | memory _ => cases h2

theorem ExternAddrOk.global_inv {s : Store H} {a : GlobalAddr} {gt : GlobalType}
    (h : ExternAddrOk s (.global a) (.global gt)) :
    ∃ gi, s.globalInst? a = some gi ∧ gi.type = gt := h.global_inv_aux a gt rfl rfl

theorem ExternAddrOk.table_inv_aux {s : Store H} {xa : ExternAddr} {xt : ExternType}
    (h : ExternAddrOk s xa xt) : ∀ a tt, xa = .table a → xt = .table tt →
      ∃ ti, s.tableInst? a = some ti ∧ TableType.Sub ti.type tt := by
  induction h with
  | table hti =>
    rintro a tt h1 h2; injection h1 with h1; subst h1
    injection h2 with h2; subst h2
    exact ⟨_, hti, TableType.sub_refl _⟩
  | func _ => rintro a tt h1 _; cases h1
  | global _ => rintro a tt h1 _; cases h1
  | mem _ => rintro a tt h1 _; cases h1
  | sub _ _ hsub ih =>
    rintro a tt rfl h2
    cases hsub with
    | table hs =>
      injection h2 with h2
      subst h2
      obtain ⟨ti, hti, hsub'⟩ := ih a _ rfl rfl
      exact ⟨ti, hti, TableType.sub_trans hsub' hs⟩
    | func _ => cases h2
    | global _ => cases h2
    | memory _ => cases h2

theorem ExternAddrOk.table_inv {s : Store H} {a : TableAddr} {tt : TableType}
    (h : ExternAddrOk s (.table a) (.table tt)) :
    ∃ ti, s.tableInst? a = some ti ∧ TableType.Sub ti.type tt := h.table_inv_aux a tt rfl rfl

theorem ExternAddrOk.mem_inv_aux {s : Store H} {xa : ExternAddr} {xt : ExternType}
    (h : ExternAddrOk s xa xt) : ∀ a mt, xa = .mem a → xt = .memory mt →
      ∃ mi, s.memInst? a = some mi ∧ MemoryType.Sub mi.type mt := by
  induction h with
  | mem hmi =>
    rintro a mt h1 h2; injection h1 with h1; subst h1
    injection h2 with h2; subst h2
    exact ⟨_, hmi, MemoryType.sub_refl _⟩
  | func _ => rintro a mt h1 _; cases h1
  | global _ => rintro a mt h1 _; cases h1
  | table _ => rintro a mt h1 _; cases h1
  | sub _ _ hsub ih =>
    rintro a mt rfl h2
    cases hsub with
    | memory hs =>
      injection h2 with h2
      subst h2
      obtain ⟨mi, hmi, hsub'⟩ := ih a _ rfl rfl
      exact ⟨mi, hmi, MemoryType.sub_trans hsub' hs⟩
    | func _ => cases h2
    | global _ => cases h2
    | table _ => cases h2

theorem ExternAddrOk.mem_inv {s : Store H} {a : MemAddr} {mt : MemoryType}
    (h : ExternAddrOk s (.mem a) (.memory mt)) :
    ∃ mi, s.memInst? a = some mi ∧ MemoryType.Sub mi.type mt := h.mem_inv_aux a mt rfl rfl

/-! ## From a context index to a store instance

The bridges `Step_read` needs: an index into the *context* resolves, through
the frame's module instance, to an instance of the *store* whose type is at or
below the one the context declares. -/

theorem ModuleInstOk.func_bridge {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) {x : FuncIdx} {ft : FuncType} (hx : C.funcs[x.toNat]? = some ft) :
    ∃ a fi, mi.funcAddr? x = some a ∧ s.funcInst? a = some fi ∧ fi.type = ft := by
  cases h with
  | mk _ hfuncs =>
    obtain ⟨a, ha, hok⟩ := forall₂_getElem? hfuncs _ _ hx
    obtain ⟨fi, hfi, he⟩ := hok.func_inv
    exact ⟨a, fi, ha, hfi, he⟩

theorem ModuleInstOk.global_bridge {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) {x : GlobalIdx} {gt : GlobalType}
    (hx : C.globals[x.toNat]? = some gt) :
    ∃ a gi, mi.globalAddr? x = some a ∧ s.globalInst? a = some gi ∧ gi.type = gt := by
  cases h with
  | mk _ _ hglobals =>
    obtain ⟨a, ha, hok⟩ := forall₂_getElem? hglobals _ _ hx
    obtain ⟨gi, hgi, he⟩ := hok.global_inv
    exact ⟨a, gi, ha, hgi, he⟩

theorem ModuleInstOk.table_bridge {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) {x : TableIdx} {tt : TableType}
    (hx : C.tables[x.toNat]? = some tt) :
    ∃ a ti, mi.tableAddr? x = some a ∧ s.tableInst? a = some ti ∧ TableType.Sub ti.type tt := by
  cases h with
  | mk _ _ _ htables =>
    obtain ⟨a, ha, hok⟩ := forall₂_getElem? htables _ _ hx
    obtain ⟨ti, hti, he⟩ := hok.table_inv
    exact ⟨a, ti, ha, hti, he⟩

theorem FrameOk.module_ok {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    ∃ C₀, ModuleInstOk s f.module C₀ ∧ C.types = C₀.types ∧ C.funcs = C₀.funcs ∧
      C.globals = C₀.globals ∧ C.tables = C₀.tables ∧ C.mems = C₀.mems ∧
      C.elems = C₀.elems ∧ C.datas = C₀.datas ∧ C.refs = C₀.refs := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := h
  exact ⟨C₀, hm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `C.TYPES` is the frame's module instance's own type list. -/
theorem FrameOk.types_eq {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    C.types = f.module.types := by
  obtain ⟨C₀, hm, he, -⟩ := h.module_ok
  rw [he, hm.types_eq]

theorem FrameOk.func_bridge {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {x : FuncIdx} {ft : FuncType} (hx : C.funcs[x.toNat]? = some ft) :
    ∃ a fi, f.module.funcAddr? x = some a ∧ s.funcInst? a = some fi ∧ fi.type = ft := by
  obtain ⟨C₀, hm, -, he, -⟩ := h.module_ok
  exact hm.func_bridge (by rw [← he]; exact hx)

theorem FrameOk.global_bridge {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {x : GlobalIdx} {gt : GlobalType} (hx : C.globals[x.toNat]? = some gt) :
    ∃ a gi, f.module.globalAddr? x = some a ∧ s.globalInst? a = some gi ∧
      (⟨s, f⟩ : State H).global? x = some gi ∧ gi.type = gt := by
  obtain ⟨C₀, hm, -, -, he, -⟩ := h.module_ok
  obtain ⟨a, gi, ha, hgi, hty⟩ := hm.global_bridge (by rw [← he]; exact hx)
  exact ⟨a, gi, ha, hgi, by simp [State.global?, ha, hgi], hty⟩

theorem FrameOk.table_bridge {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {x : TableIdx} {tt : TableType} (hx : C.tables[x.toNat]? = some tt) :
    ∃ a ti, f.module.tableAddr? x = some a ∧ s.tableInst? a = some ti ∧
      (⟨s, f⟩ : State H).table? x = some ti ∧ TableType.Sub ti.type tt := by
  obtain ⟨C₀, hm, -, -, -, he, -⟩ := h.module_ok
  obtain ⟨a, ti, ha, hti, hsub⟩ := hm.table_bridge (by rw [← he]; exact hx)
  exact ⟨a, ti, ha, hti, by simp [State.table?, ha, hti], hsub⟩

/-! ## The typing context versus the frame context

A 2.0 step never changes the *types* in the frame's context: `Step/local.set`
(`8-reduction:380`) overwrites a local's value, and `Frame_ok` then holds again
with the same context. What a step does change is where in the code we are, so
the code is typed in a context obtained from the frame's by pushing labels
(`AdminOk.label`) and setting a return type (`AdminOk.frame`). `CtxUnder Ct Cf`
is exactly that relation: `Ct` and `Cf` agree on every field but `LABELS` and
`RETURN`. (Core 3.0's `CtxUnder` additionally orders the *locals*, because 3.0
tracks local initialisation; 2.0 does not, so the locals agree on the nose.) -/

/-- `Ct` is a typing context under the frame context `Cf`: the two agree except
on `LABELS` and `RETURN`. -/
def CtxUnder (Ct Cf : Context) : Prop :=
  ({ Ct with labels := [], return_ := none } : Context) = { Cf with labels := [], return_ := none }

theorem CtxUnder.refl (C : Context) : CtxUnder C C := rfl

/-- Pushing a label keeps the relation. -/
theorem CtxUnder.withLabel {Ct Cf : Context} (h : CtxUnder Ct Cf) (ts : CResultType) :
    CtxUnder (Ct.withLabel ts) Cf := h

/-- Setting the return type keeps the relation. -/
theorem CtxUnder.setReturn {Ct Cf : Context} (h : CtxUnder Ct Cf) (r : Option CResultType) :
    CtxUnder { Ct with return_ := r } Cf := h

theorem CtxUnder.eq {Ct Cf : Context} (h : CtxUnder Ct Cf) :
    ({ Ct with labels := [], return_ := none } : Context) =
      { Cf with labels := [], return_ := none } := h

theorem CtxUnder.types_eq {Ct Cf : Context} (h : CtxUnder Ct Cf) : Ct.types = Cf.types := by
  have h' := congrArg Context.types h.eq; exact h'

theorem CtxUnder.funcs_eq {Ct Cf : Context} (h : CtxUnder Ct Cf) : Ct.funcs = Cf.funcs := by
  have h' := congrArg Context.funcs h.eq; exact h'

theorem CtxUnder.globals_eq {Ct Cf : Context} (h : CtxUnder Ct Cf) : Ct.globals = Cf.globals := by
  have h' := congrArg Context.globals h.eq; exact h'

theorem CtxUnder.tables_eq {Ct Cf : Context} (h : CtxUnder Ct Cf) : Ct.tables = Cf.tables := by
  have h' := congrArg Context.tables h.eq; exact h'

theorem CtxUnder.mems_eq {Ct Cf : Context} (h : CtxUnder Ct Cf) : Ct.mems = Cf.mems := by
  have h' := congrArg Context.mems h.eq; exact h'

theorem CtxUnder.elems_eq {Ct Cf : Context} (h : CtxUnder Ct Cf) : Ct.elems = Cf.elems := by
  have h' := congrArg Context.elems h.eq; exact h'

theorem CtxUnder.datas_eq {Ct Cf : Context} (h : CtxUnder Ct Cf) : Ct.datas = Cf.datas := by
  have h' := congrArg Context.datas h.eq; exact h'

theorem CtxUnder.locals_eq {Ct Cf : Context} (h : CtxUnder Ct Cf) : Ct.locals = Cf.locals := by
  have h' := congrArg Context.locals h.eq; exact h'

theorem CtxUnder.refs_eq {Ct Cf : Context} (h : CtxUnder Ct Cf) : Ct.refs = Cf.refs := by
  have h' := congrArg Context.refs h.eq; exact h'

/-! ## The shape of the preservation statement -/

/-- The conclusion of preservation for a single step: the new store is well
typed and extends the old one, the new frame still realizes the *same* frame
context, and the new code still has the type the old code had. -/
def PresConcl (c c' : Config H) (Cf Ct : Context) (it : InstrType) : Prop :=
  StoreOk c'.store ∧ Extend c.store c'.store ∧ FrameOk c'.store c'.frame Cf ∧
    AdminsOk c'.store Ct c'.code it

/-- Preservation for one step, generalised over the typing context. -/
abbrev PresStmt (c c' : Config H) : Prop :=
  ∀ {Cf Ct : Context} {it : InstrType}, StoreOk c.store → FrameOk c.store c.frame Cf →
    CtxUnder Ct Cf → AdminsOk c.store Ct c.code it → PresConcl c c' Cf Ct it

/-- A step that changes neither the store nor the frame. -/
theorem PresConcl.pure {s : Store H} {f : Frame} {is is' : List Admin} {Cf Ct : Context}
    {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf)
    (hty : AdminsOk s Ct is' it) :
    PresConcl (H := H) ⟨s, f, is⟩ ⟨s, f, is'⟩ Cf Ct it :=
  ⟨hs, Extend.refl s, hf, hty⟩

theorem ModuleInstOk.elem_bridge {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) {x : ElemIdx} {rt : ElemType}
    (hx : C.elems[x.toNat]? = some rt) :
    ∃ a ei, mi.elemAddr? x = some a ∧ s.elemInst? a = some ei ∧ ElemInstOk s ei ∧
      ei.type = rt := by
  cases h with
  | mk _ _ _ _ _ helems =>
    obtain ⟨a, ha, ei, hei, hok, hty⟩ := forall₂_getElem? helems _ _ hx
    exact ⟨a, ei, ha, hei, hok, hty⟩

theorem FrameOk.elem_bridge {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C)
    {x : ElemIdx} {rt : ElemType} (hx : C.elems[x.toNat]? = some rt) :
    ∃ ei, (⟨s, f⟩ : State H).elem? x = some ei ∧ ElemInstOk s ei ∧ ei.type = rt := by
  obtain ⟨C₀, hm, -, -, -, -, -, he, -⟩ := h.module_ok
  obtain ⟨a, ei, ha, hei, hok, hty⟩ := hm.elem_bridge (by rw [← he]; exact hx)
  exact ⟨ei, by simp [State.elem?, ha, hei], hok, hty⟩

/-! ## Two more flat-redex helpers -/

/-- An arity-zero flat redex whose reduct is a single constant instruction. -/
theorem AdminsOk.flat0_const {s : Store H} {C : Context} {i j : Instr} {it : InstrType}
    (h : AdminsOk s C [.plain i] it)
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params = [])
    (hj : ∀ it₀, InstrOk C i it₀ → InstrOk C j ⟨[], it₀.results⟩) :
    AdminsOk s C [.plain j] it :=
  AdminsOk.flat0 harity (fun it₀ hi => .single (.plain (hj it₀ hi))) h

/-- An arity-three flat redex with no results and an empty reduct: the `-zero`
rules of the six bulk families (`8-reduction:432`, `448`, `471`, `612`, `628`,
`651`). -/
theorem AdminsOk.flat3_nil {s : Store H} {C : Context} {a₁ a₂ a₃ : Admin} {i : Instr}
    {it : InstrType} (h : AdminsOk s C [a₁, a₂, a₃, .plain i] it)
    (hv₁ : a₁.isVal) (hv₂ : a₂.isVal) (hv₃ : a₃.isVal)
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params.length = 3)
    (hres : ∀ it₀, InstrOk C i it₀ → it₀.results = []) : AdminsOk s C [] it := by
  obtain ⟨v₁, hv₁'⟩ := Option.isSome_iff_exists.mp hv₁
  obtain ⟨v₂, hv₂'⟩ := Option.isSome_iff_exists.mp hv₂
  obtain ⟨v₃, hv₃'⟩ := Option.isSome_iff_exists.mp hv₃
  obtain rfl := Admin.toAdmin_of_val? hv₁'
  obtain rfl := Admin.toAdmin_of_val? hv₂'
  obtain rfl := Admin.toAdmin_of_val? hv₃'
  refine AdminsOk.flat3 harity (fun _ _ _ it₀ _ _ _ hi _ => ?_) h
  rw [hres it₀ hi]
  exact .nil

/-- An arity-two flat redex with no results and an empty reduct: the memory
stores (`8-reduction:563`, `571`, `579`, `588`). -/
theorem AdminsOk.flat2_nil {s : Store H} {C : Context} {a₁ a₂ : Admin} {i : Instr}
    {it : InstrType} (h : AdminsOk s C [a₁, a₂, .plain i] it)
    (hv₁ : a₁.isVal) (hv₂ : a₂.isVal)
    (harity : ∀ it₀, InstrOk C i it₀ → it₀.params.length = 2)
    (hres : ∀ it₀, InstrOk C i it₀ → it₀.results = []) : AdminsOk s C [] it := by
  obtain ⟨v₁, hv₁'⟩ := Option.isSome_iff_exists.mp hv₁
  obtain ⟨v₂, hv₂'⟩ := Option.isSome_iff_exists.mp hv₂
  obtain rfl := Admin.toAdmin_of_val? hv₁'
  obtain rfl := Admin.toAdmin_of_val? hv₂'
  refine AdminsOk.flat2 harity (fun _ _ it₀ _ _ hi _ => ?_) h
  rw [hres it₀ hi]
  exact .nil

/-! ## `Step_read`: the block family (`8-reduction:61-74`) -/

/-- `$blocktype(z, bt)` (`8-reduction:63`) and `Blocktype_ok` (`6-typing:203`)
agree: the context's `TYPES` is the frame's module instance's own type list. -/
theorem blockTypeOk_eq {s : Store H} {f : Frame} {Cf Ct : Context} {bt : BlockType}
    {ft : FuncType} {it₀ : InstrType} (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (hbt : f.module.blockType? bt = some ft) (hok : BlockTypeOk Ct bt it₀) :
    it₀ = InstrType.lift ft.params ft.results := by
  have htypes : Ct.types = f.module.types := by rw [hu.types_eq, hf.types_eq]
  cases hok with
  | result t =>
    cases t <;>
      · simp only [ModuleInst.blockType?, Option.some.injEq] at hbt
        subst hbt
        rfl
  | typeIdx hx =>
    rw [htypes] at hx
    simp only [ModuleInst.blockType?, ModuleInst.type?, hx, Option.some.injEq] at hbt
    subst hbt
    rfl

/-- `Step_read/block` (`8-reduction:68`). -/
theorem pres_read_block {s : Store H} {f : Frame} {Cf Ct : Context} {bt : BlockType}
    {body : List Instr} {vs : List Val} {ft : FuncType} {it : InstrType}
    (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (hbt : f.module.blockType? bt = some ft) (hk : vs.length = ft.params.length)
    (hty : AdminsOk s Ct (vals vs ++ [.plain (.block bt body)]) it) :
    AdminsOk s Ct [.label ft.results.length [] (vals vs ++ expression body)] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv hty
  cases hi with
  | block hbt' hbody =>
    obtain he := blockTypeOk_eq hf hu hbt hbt'
    obtain ⟨he₁, he₂⟩ : _ ∧ _ := InstrType.mk.injEq .. ▸ he
    rw [he₁] at hp
    rw [he₂] at hr
    obtain ⟨hp1, hp2⟩ := sub_split_right (by simp [← hvs.length_eq, hk]) hp
    obtain heq : liftResult ft.params = liftResult ts := CResultType.sub_liftResult_iff.mp hp2
    refine AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp1) hr ?_
    refine .single (.label (t' := liftResult ft.results) (by simp) (AdminsOk.id _) ?_)
    refine AdminsOk.append ?_ (AdminsOk.of_instrsOk (he₂ ▸ he₁ ▸ hbody))
    rw [heq]
    exact AdminsOk.of_vals hvs

/-- `Step_read/loop` (`8-reduction:72`): the label's continuation is the loop
itself, so a branch to it re-enters. -/
theorem pres_read_loop {s : Store H} {f : Frame} {Cf Ct : Context} {bt : BlockType}
    {body : List Instr} {vs : List Val} {ft : FuncType} {it : InstrType}
    (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (hbt : f.module.blockType? bt = some ft) (hk : vs.length = ft.params.length)
    (hty : AdminsOk s Ct (vals vs ++ [.plain (.loop bt body)]) it) :
    AdminsOk s Ct [.label ft.params.length [.loop bt body] (vals vs ++ expression body)] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv hty
  cases hi with
  | loop hbt' hbody =>
    obtain he := blockTypeOk_eq hf hu hbt hbt'
    obtain ⟨he₁, he₂⟩ : _ ∧ _ := InstrType.mk.injEq .. ▸ he
    rw [he₁] at hp
    rw [he₂] at hr
    obtain ⟨hp1, hp2⟩ := sub_split_right (by simp [← hvs.length_eq, hk]) hp
    obtain heq : liftResult ft.params = liftResult ts := CResultType.sub_liftResult_iff.mp hp2
    refine AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp1) hr ?_
    refine .single (.label (t' := liftResult ft.params) (by simp) ?_ ?_)
    · exact .single (.plain (he₂ ▸ he₁ ▸ InstrOk.loop hbt' hbody))
    · refine AdminsOk.append ?_ (AdminsOk.of_instrsOk (he₂ ▸ he₁ ▸ hbody))
      rw [heq]
      exact AdminsOk.of_vals hvs

/-! ## `Step_read`: the call and reference families (`8-reduction:117-135`,
`210-213`) -/

/-- `Step_read/call` (`8-reduction:119`). -/
theorem pres_read_call {s : Store H} {f : Frame} {Cf Ct : Context} {x : FuncIdx}
    {a : FuncAddr} {it : InstrType} (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (hx : f.module.funcAddr? x = some a)
    (hty : AdminsOk s Ct [.plain (.call x)] it) : AdminsOk s Ct [.callAddr a] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv (vs := []) hty
  cases hvs
  cases hi with
  | @call _ _ ft hft =>
    obtain ⟨a', fi, ha, hfi, rfl⟩ := hf.func_bridge (by rw [← hu.funcs_eq]; exact hft)
    rw [hx] at ha
    obtain rfl := Option.some.inj ha
    exact AdminsOk.rebuild (us := us) (ps := (InstrType.lift fi.type.params fi.type.results).params)
      (by simpa using hp) (by simpa using hr) (.single (.callAddr hfi))

/-- `Step_read/ref.func` (`8-reduction:212`). -/
theorem pres_read_refFunc {s : Store H} {f : Frame} {Cf Ct : Context} {x : FuncIdx}
    {a : FuncAddr} {it : InstrType} (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (hx : f.module.funcAddr? x = some a)
    (hty : AdminsOk s Ct [.plain (.refFunc x)] it) : AdminsOk s Ct [.refFuncAddr a] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv (vs := []) hty
  cases hvs
  cases hi with
  | @refFunc _ _ ft hft _ =>
    obtain ⟨a', fi, ha, hfi, -⟩ := hf.func_bridge (by rw [← hu.funcs_eq]; exact hft)
    rw [hx] at ha
    obtain rfl := Option.some.inj ha
    exact AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp) hr
      (.single (.refFuncAddr hfi))

/-! ## `Step_read`: the local and global families (`8-reduction:375-390`) -/

/-- `Step_read/local.get` (`8-reduction:377`). -/
theorem pres_read_localGet {s : Store H} {f : Frame} {Cf Ct : Context} {x : LocalIdx}
    {v : Val} {it : InstrType} (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (hv : (⟨s, f⟩ : State H).local? x = some v)
    (hty : AdminsOk s Ct [.plain (.localGet x)] it) : AdminsOk s Ct [v.toAdmin] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv (vs := []) hty
  cases hvs
  cases hi with
  | @localGet _ _ t hx =>
    obtain ⟨v', hv', hok⟩ :=
      forall₂_getElem? hf.locals_forall₂ x.toNat t (by rw [← hu.locals_eq]; exact hx)
    simp only [State.local?, Frame.local?] at hv
    rw [hv] at hv'
    obtain rfl := Option.some.inj hv'
    exact AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp) hr
      (.single (AdminOk.toAdmin_ok hok))

/-- `Step_read/global.get` (`8-reduction:389`). -/
theorem pres_read_globalGet {s : Store H} {f : Frame} {Cf Ct : Context} {x : GlobalIdx}
    {gi : GlobalInst} {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf)
    (hu : CtxUnder Ct Cf) (hg : (⟨s, f⟩ : State H).global? x = some gi)
    (hty : AdminsOk s Ct [.plain (.globalGet x)] it) :
    AdminsOk s Ct [gi.value.toAdmin] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv (vs := []) hty
  cases hvs
  cases hi with
  | @globalGet _ _ gt hgt =>
    obtain ⟨a, gi', -, hgi', hst, rfl⟩ := hf.global_bridge (by rw [← hu.globals_eq]; exact hgt)
    rw [hg] at hst
    obtain rfl := Option.some.inj hst
    have hok := hs.globals gi (getElem?_mem hgi')
    exact AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp) hr
      (.single (AdminOk.toAdmin_ok hok.2))

/-! ## `Step_read`: the table family (`8-reduction:396-480`) -/

/-- `Step_read/table.get-val` (`8-reduction:402`). -/
theorem pres_read_tableGetVal {s : Store H} {f : Frame} {Cf Ct : Context} {x : TableIdx}
    {i : BitVec 32} {ti : TableInst} {r : Ref} {it : InstrType} (hs : StoreOk s)
    (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hr : ti.refs[i.toNat]? = some r)
    (hty : AdminsOk s Ct [constI32 i, .plain (.tableGet x)] it) :
    AdminsOk s Ct [aref r] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hres⟩ := AdminsOk.flat_inv (vs := [Val.i32 i]) hty
  cases hi with
  | @tableGet _ _ tt hx =>
    obtain ⟨a, ti', -, hti', hst, hsub⟩ := hf.table_bridge (by rw [← hu.tables_eq]; exact hx)
    rw [ht] at hst
    obtain rfl := Option.some.inj hst
    have hok := hs.tables ti (getElem?_mem hti')
    have hrok : RefOk s r ti.type.element := hok.2.2 r (getElem?_mem hr)
    rw [hsub.2] at hrok
    obtain ⟨t, ts', hv, hts, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
    cases hts
    obtain rfl := ValOk.i32_eq hv
    obtain ⟨hp1, -⟩ := sub_split_right (d := [CValType.val ValType.i32]) (by simp) hp
    exact AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp1) hres
      (.single (AdminOk.toAdmin_ok (ValOk.ref hrok)))

/-! ## Preservation for `Step_read` (`8-reduction:7`)

The rules that read the store and the frame. These are where the typing of the
*context* has to be matched against the typing of the *store*: an index into
`C.TABLES` has to be turned into a table instance of the right element type, and
so on. -/

/-! ## `Step_read`: the bulk table and memory loops

`table.fill`/`table.copy`/`table.init` and `memory.fill`/`memory.copy`/
`memory.init` reduce **one element (byte) at a time** by emitting further
instructions (`8-reduction:437-480`, `617-660`). All the typing information the
emitted instructions need — the table's element type, the memory type, the data
segment — is already in the premises of the redex's own `Instr_ok` rule, so
these lemmas need neither the store nor the frame, except `table.init-succ`,
whose emitted reference comes from the element segment. -/

/-- An `I32` constant has type `I32`. -/
theorem valOk_i32 {s : Store H} (c : BitVec 32) : ValOk s (Val.i32 c) .i32 := .num _

/-- `(STORE I32 8 $memarg0)`, the instruction the `memory.fill`/`copy`/`init`
loops emit. -/
theorem instrOk_store8 {C : Context} {mt : MemoryType} (hm : C.mems[0]? = some mt) :
    InstrOk C (.intStore .i32 (some .i8) memarg0) ⟨[.val .i32, .val .i32], []⟩ :=
  InstrOk.intStorePack hm (by decide) (by decide)

/-- `(LOAD I32 (8 _ U) $memarg0)`, the instruction the `memory.copy` loop
emits. -/
theorem instrOk_load8u {C : Context} {mt : MemoryType} (hm : C.mems[0]? = some mt) :
    InstrOk C (.intLoad .i32 (some (.i8, .unsigned)) memarg0) ⟨[.val .i32], [.val .i32]⟩ :=
  InstrOk.intLoadPack hm (by decide) (by decide)

/-- `Step_read/table.fill-succ` (`8-reduction:437`). -/
theorem pres_read_tableFillSucc {s : Store H} {Ct : Context} {x : TableIdx}
    {i n : BitVec 32} {v : Val} {it : InstrType}
    (hty : AdminsOk s Ct [constI32 i, v.toAdmin, constI32 n, .plain (.tableFill x)] it) :
    AdminsOk s Ct [constI32 i, v.toAdmin, .plain (.tableSet x),
      constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain (.tableFill x)] it := by
  refine AdminsOk.flat3 (v₁ := Val.i32 i) (v₂ := v) (v₃ := Val.i32 n)
    (fun _ hi => by cases hi; rfl) (fun t₁ t₂ t₃ it₀ h₁ h₂ h₃ hi hps => ?_) hty
  cases hi with
  | @tableFill _ _ tt hx =>
    simp only [List.cons.injEq, CValType.val.injEq, and_true] at hps
    obtain ⟨rfl, rfl, rfl⟩ := hps
    have e1 : AdminsOk s Ct (vals [Val.i32 i, v]) ⟨[], liftResult [.i32, .ref tt.element]⟩ :=
      AdminsOk.of_vals (.cons h₁ (.cons h₂ .nil))
    have e2 : AdminsOk s Ct [.plain (.tableSet x)]
        ⟨liftResult [.i32, .ref tt.element], []⟩ := .single (.plain (InstrOk.tableSet hx))
    have e3 : AdminsOk s Ct (vals [Val.i32 (i + 1), v, Val.i32 (n - 1)])
        ⟨[], liftResult [.i32, .ref tt.element, .i32]⟩ :=
      AdminsOk.of_vals (.cons (valOk_i32 _) (.cons h₂ (.cons (valOk_i32 _) .nil)))
    have e4 : AdminsOk s Ct [.plain (.tableFill x)]
        ⟨liftResult [.i32, .ref tt.element, .i32], []⟩ :=
      .single (.plain (InstrOk.tableFill hx))
    exact ((e1.append e2).append e3).append e4

/-- `Step_read/table.copy-le` and `/table.copy-gt` (`8-reduction:453`, `460`):
the two directions emit the same instructions at different indices. -/
theorem pres_read_tableCopy {s : Store H} {Ct : Context} {x y : TableIdx}
    {j i n a b c d : BitVec 32} {it : InstrType}
    (hty : AdminsOk s Ct [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)] it) :
    AdminsOk s Ct [constI32 a, constI32 b, .plain (.tableGet y), .plain (.tableSet x),
      constI32 c, constI32 d, constI32 (n - 1), .plain (.tableCopy x y)] it := by
  refine AdminsOk.flat3 (v₁ := Val.i32 j) (v₂ := Val.i32 i) (v₃ := Val.i32 n)
    (fun _ hi => by cases hi; rfl) (fun t₁ t₂ t₃ it₀ _ _ _ hi hps => ?_) hty
  cases hi with
  | @tableCopy _ _ _ tx ty hx₁ hx₂ hrt =>
    have e1 : AdminsOk s Ct (vals [Val.i32 a, Val.i32 b]) ⟨[], liftResult [.i32, .i32]⟩ :=
      AdminsOk.of_vals (.cons (valOk_i32 _) (.cons (valOk_i32 _) .nil))
    have e2 : AdminsOk s Ct [.plain (.tableGet y)]
        ⟨liftResult [.i32, .i32], liftResult [.i32, .ref ty.element]⟩ := by
      simpa using AdminsOk.frame (s := s) (ts := [CValType.val .i32])
        (AdminsOk.single (.plain (InstrOk.tableGet hx₂)))
    have e3 : AdminsOk s Ct [.plain (.tableSet x)]
        ⟨liftResult [.i32, .ref ty.element], []⟩ := by
      rw [← hrt]
      exact .single (.plain (InstrOk.tableSet hx₁))
    have e4 : AdminsOk s Ct (vals [Val.i32 c, Val.i32 d, Val.i32 (n - 1)])
        ⟨[], liftResult [.i32, .i32, .i32]⟩ :=
      AdminsOk.of_vals (.cons (valOk_i32 _) (.cons (valOk_i32 _) (.cons (valOk_i32 _) .nil)))
    have e5 : AdminsOk s Ct [.plain (.tableCopy x y)] ⟨liftResult [.i32, .i32, .i32], []⟩ :=
      .single (.plain (InstrOk.tableCopy hx₁ hx₂ hrt))
    exact ((((e1.append e2).append e3).append e4).append e5)

/-- `Step_read/table.init-succ` (`8-reduction:476`): the emitted reference comes
from the element segment, whose type is the table's element type. -/
theorem pres_read_tableInitSucc {s : Store H} {f : Frame} {Cf Ct : Context} {x : TableIdx}
    {y : ElemIdx} {j i n : BitVec 32} {ei : ElemInst} {r : Ref} {it : InstrType}
    (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (he : (⟨s, f⟩ : State H).elem? y = some ei) (hr : ei.refs[i.toNat]? = some r)
    (hty : AdminsOk s Ct [constI32 j, constI32 i, constI32 n, .plain (.tableInit x y)] it) :
    AdminsOk s Ct [constI32 j, aref r, .plain (.tableSet x),
      constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.tableInit x y)] it := by
  refine AdminsOk.flat3 (v₁ := Val.i32 j) (v₂ := Val.i32 i) (v₃ := Val.i32 n)
    (fun _ hi => by cases hi; rfl) (fun t₁ t₂ t₃ it₀ _ _ _ hi hps => ?_) hty
  cases hi with
  | @tableInit _ _ _ tt rt hx₁ hx₂ hrt =>
    obtain ⟨ei', he', hok, hety⟩ := hf.elem_bridge (by rw [← hu.elems_eq]; exact hx₂)
    have hee : ei' = ei := by rw [he] at he'; exact (Option.some.inj he').symm
    subst hee
    have hrok : RefOk s r tt.element := by
      rw [hrt, ← hety]
      exact hok r (getElem?_mem hr)
    have e1 : AdminsOk s Ct (vals [Val.i32 j, Val.ref r])
        ⟨[], liftResult [.i32, .ref tt.element]⟩ :=
      AdminsOk.of_vals (.cons (valOk_i32 _) (.cons (.ref hrok) .nil))
    have e2 : AdminsOk s Ct [.plain (.tableSet x)]
        ⟨liftResult [.i32, .ref tt.element], []⟩ := .single (.plain (InstrOk.tableSet hx₁))
    have e3 : AdminsOk s Ct (vals [Val.i32 (j + 1), Val.i32 (i + 1), Val.i32 (n - 1)])
        ⟨[], liftResult [.i32, .i32, .i32]⟩ :=
      AdminsOk.of_vals (.cons (valOk_i32 _) (.cons (valOk_i32 _) (.cons (valOk_i32 _) .nil)))
    have e4 : AdminsOk s Ct [.plain (.tableInit x y)] ⟨liftResult [.i32, .i32, .i32], []⟩ :=
      .single (.plain (InstrOk.tableInit hx₁ hx₂ hrt))
    exact ((e1.append e2).append e3).append e4

/-- `Step_read/memory.fill-succ` (`8-reduction:617`). -/
theorem pres_read_memoryFillSucc {s : Store H} {Ct : Context} {i n : BitVec 32} {v : Val}
    {it : InstrType}
    (hty : AdminsOk s Ct [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill] it) :
    AdminsOk s Ct [constI32 i, v.toAdmin, store8,
      constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain .memoryFill] it := by
  refine AdminsOk.flat3 (v₁ := Val.i32 i) (v₂ := v) (v₃ := Val.i32 n)
    (fun _ hi => by cases hi; rfl) (fun t₁ t₂ t₃ it₀ h₁ h₂ h₃ hi hps => ?_) hty
  cases hi with
  | @memoryFill _ mt hm =>
    simp only [List.cons.injEq, CValType.val.injEq, and_true] at hps
    obtain ⟨rfl, rfl, rfl⟩ := hps
    have e1 : AdminsOk s Ct (vals [Val.i32 i, v]) ⟨[], liftResult [.i32, .i32]⟩ :=
      AdminsOk.of_vals (.cons h₁ (.cons h₂ .nil))
    have e2 : AdminsOk s Ct [store8] ⟨liftResult [.i32, .i32], []⟩ :=
      .single (.plain (instrOk_store8 hm))
    have e3 : AdminsOk s Ct (vals [Val.i32 (i + 1), v, Val.i32 (n - 1)])
        ⟨[], liftResult [.i32, .i32, .i32]⟩ :=
      AdminsOk.of_vals (.cons (valOk_i32 _) (.cons h₂ (.cons (valOk_i32 _) .nil)))
    have e4 : AdminsOk s Ct [.plain .memoryFill] ⟨liftResult [.i32, .i32, .i32], []⟩ :=
      .single (.plain (InstrOk.memoryFill hm))
    exact ((e1.append e2).append e3).append e4

/-- `Step_read/memory.copy-le` and `/memory.copy-gt` (`8-reduction:633`,
`640`). -/
theorem pres_read_memoryCopy {s : Store H} {Ct : Context} {j i n a b c d : BitVec 32}
    {it : InstrType}
    (hty : AdminsOk s Ct [constI32 j, constI32 i, constI32 n, .plain .memoryCopy] it) :
    AdminsOk s Ct [constI32 a, constI32 b, load8u, store8,
      constI32 c, constI32 d, constI32 (n - 1), .plain .memoryCopy] it := by
  refine AdminsOk.flat3 (v₁ := Val.i32 j) (v₂ := Val.i32 i) (v₃ := Val.i32 n)
    (fun _ hi => by cases hi; rfl) (fun t₁ t₂ t₃ it₀ _ _ _ hi hps => ?_) hty
  cases hi with
  | @memoryCopy _ mt hm =>
    have e1 : AdminsOk s Ct (vals [Val.i32 a, Val.i32 b]) ⟨[], liftResult [.i32, .i32]⟩ :=
      AdminsOk.of_vals (.cons (valOk_i32 _) (.cons (valOk_i32 _) .nil))
    have e2 : AdminsOk s Ct [load8u] ⟨liftResult [.i32, .i32], liftResult [.i32, .i32]⟩ := by
      have hf2 := AdminsOk.frame (s := s) (C := Ct) (ts := [CValType.val ValType.i32])
        (AdminsOk.single (.plain (instrOk_load8u hm)))
      simpa [load8u] using hf2
    have e3 : AdminsOk s Ct [store8] ⟨liftResult [.i32, .i32], []⟩ :=
      .single (.plain (instrOk_store8 hm))
    have e4 : AdminsOk s Ct (vals [Val.i32 c, Val.i32 d, Val.i32 (n - 1)])
        ⟨[], liftResult [.i32, .i32, .i32]⟩ :=
      AdminsOk.of_vals (.cons (valOk_i32 _) (.cons (valOk_i32 _) (.cons (valOk_i32 _) .nil)))
    have e5 : AdminsOk s Ct [.plain .memoryCopy] ⟨liftResult [.i32, .i32, .i32], []⟩ :=
      .single (.plain (InstrOk.memoryCopy hm))
    exact ((((e1.append e2).append e3).append e4).append e5)

/-- `Step_read/memory.init-succ` (`8-reduction:656`). -/
theorem pres_read_memoryInitSucc {s : Store H} {Ct : Context} {x : DataIdx}
    {j i n : BitVec 32} {b : UInt8} {it : InstrType}
    (hty : AdminsOk s Ct [constI32 j, constI32 i, constI32 n, .plain (.memoryInit x)] it) :
    AdminsOk s Ct [constI32 j, constI32 (BitVec.ofNat 32 b.toNat), store8,
      constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.memoryInit x)] it := by
  refine AdminsOk.flat3 (v₁ := Val.i32 j) (v₂ := Val.i32 i) (v₃ := Val.i32 n)
    (fun _ hi => by cases hi; rfl) (fun t₁ t₂ t₃ it₀ _ _ _ hi hps => ?_) hty
  cases hi with
  | @memoryInit _ _ mt hm hx =>
    have e1 : AdminsOk s Ct (vals [Val.i32 j, Val.i32 (BitVec.ofNat 32 b.toNat)])
        ⟨[], liftResult [.i32, .i32]⟩ :=
      AdminsOk.of_vals (.cons (valOk_i32 _) (.cons (valOk_i32 _) .nil))
    have e2 : AdminsOk s Ct [store8] ⟨liftResult [.i32, .i32], []⟩ :=
      .single (.plain (instrOk_store8 hm))
    have e3 : AdminsOk s Ct (vals [Val.i32 (j + 1), Val.i32 (i + 1), Val.i32 (n - 1)])
        ⟨[], liftResult [.i32, .i32, .i32]⟩ :=
      AdminsOk.of_vals (.cons (valOk_i32 _) (.cons (valOk_i32 _) (.cons (valOk_i32 _) .nil)))
    have e4 : AdminsOk s Ct [.plain (.memoryInit x)] ⟨liftResult [.i32, .i32, .i32], []⟩ :=
      .single (.plain (InstrOk.memoryInit hm hx))
    exact ((e1.append e2).append e3).append e4

/-! ## `Step_read`: the indirect call and `$invoke` (`8-reduction:122`, `131`) -/

/-- `Step_read/call_indirect-call` (`8-reduction:122`): the table entry's
function instance has the type the type index names. -/
theorem pres_read_callIndirect {s : Store H} {f : Frame} {Cf Ct : Context} {x : TableIdx}
    {y : TypeIdx} {i : BitVec 32} {a : FuncAddr} {fi : FuncInst H} {it : InstrType}
    (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf) (hfi : s.funcInst? a = some fi)
    (hy : (⟨s, f⟩ : State H).type? y = some fi.type)
    (hty : AdminsOk s Ct [constI32 i, .plain (.callIndirect x y)] it) :
    AdminsOk s Ct [.callAddr a] it := by
  obtain ⟨ts, us, it₀, hvs, hi, hp, hres⟩ := AdminsOk.flat_inv (vs := [Val.i32 i]) hty
  obtain ⟨t, ts', hv, hts, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  cases hts
  obtain rfl := ValOk.i32_eq hv
  cases hi with
  | @callIndirect _ _ _ tt ft hx hrt hyc =>
    have htypes : Ct.types = f.module.types := by rw [hu.types_eq, hf.types_eq]
    have hft : ft = fi.type := by
      rw [htypes] at hyc
      simp only [State.type?, ModuleInst.type?] at hy
      rw [hy] at hyc
      exact (Option.some.inj hyc).symm
    subst hft
    have hp' : CResultType.Sub (it.params ++ liftResult [ValType.i32])
        ((us ++ liftResult fi.type.params) ++ [CValType.val ValType.i32]) := by
      simpa [List.append_assoc] using hp
    obtain ⟨hp1, -⟩ := sub_split_right (by simp) hp'
    exact AdminsOk.rebuild (us := us) (ps := liftResult fi.type.params)
      (rs := liftResult fi.type.results) hp1 hres (.single (.callAddr hfi))

/-- Default values have their declared types. -/
theorem forall₂_defaultVal (s : Store H) :
    ∀ ls : List ValType, List.Forall₂ (ValOk s) (ls.map defaultVal) ls
  | [] => .nil
  | t :: ts => .cons (valOk_defaultVal s t) (forall₂_defaultVal s ts)

/-- `Step_read/call_addr` (`8-reduction:131`) on a Wasm function: the new frame
holds the arguments followed by the declared locals at their default values, and
the body is checked in the context the function instance's module realizes,
which is exactly `Context.withFuncFrame` of `Func_ok` (`6-typing:592`). -/
theorem pres_read_callAddr {s : Store H} {Ct : Context} {a : FuncAddr} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {it : InstrType} (hs : StoreOk s)
    (hfi : s.funcInst? a = some fi) (hcode : fi.code = .wasm fn)
    (hk : vs.length = fi.type.params.length)
    (hty : AdminsOk s Ct (vals vs ++ [.callAddr a]) it) :
    AdminsOk s Ct [.frame fi.type.results.length (Frame.forCall fi.module vs fn.locals)
      [.label fi.type.results.length [] (expression fn.body)]] it := by
  obtain ⟨tm, hV, hI⟩ := AdminsOk.append_inv hty
  obtain ⟨ts, hvs, hsub⟩ := AdminsOk.vals_inv hV
  obtain ⟨us, it₀, ha, hp0, hres⟩ := AdminsOk.single_inv' hI
  cases ha with
  | @callAddr _ _ fi' hfi' =>
    have hff : fi' = fi := by rw [hfi] at hfi'; exact (Option.some.inj hfi').symm
    subst hff
    have hp : CResultType.Sub (it.params ++ liftResult ts)
        (us ++ liftResult fi'.type.params) := CResultType.sub_trans hsub hp0
    obtain ⟨hp1, hp2⟩ :=
      sub_split_right (d := liftResult fi'.type.params)
        (by simp [← hvs.length_eq, hk]) hp
    obtain rfl : ts = fi'.type.params :=
      liftResult_inj (CResultType.sub_liftResult_iff.mp hp2).symm
    cases hs.funcs fi' (getElem?_mem hfi) with
    | host _ hcode' => rw [hcode] at hcode'; exact absurd hcode' (by simp)
    | @wasm C₀ code hok hm hcode' hfok =>
      obtain rfl : fn = code := by rw [hcode] at hcode'; injection hcode'
      cases hfok with
      | mk hx hbody =>
        have hfrok : FrameOk s (Frame.forCall fi'.module vs fn.locals)
            { C₀ with locals := C₀.locals ++ (fi'.type.params ++ fn.locals) } := by
          refine ⟨C₀, fi'.type.params ++ fn.locals, by simpa using hm, ?_, rfl⟩
          simpa using List.rel_append hvs (forall₂_defaultVal s fn.locals)
        refine AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp1) hres ?_
        refine .single (.frame hfrok (by simp) ?_)
        refine .single (.label (t' := liftResult fi'.type.results) (by simp)
          (AdminsOk.id _) ?_)
        have hc := AdminsOk.of_instrsOk (s := s) hbody
        simpa [Context.withLabel, Context.withFuncFrame, hm.labels_nil] using hc

theorem ReadStep.preservation {s : Store H} {f : Frame} {Cf Ct : Context}
    {is is' : List Admin} {it : InstrType} (hs : StoreOk s) (hf : FrameOk s f Cf)
    (hu : CtxUnder Ct Cf) (hty : AdminsOk s Ct is it) (h : ReadStep s f is is') :
    AdminsOk s Ct is' it := by
  cases h with
  | block hbt hk => exact pres_read_block hf hu hbt hk hty
  | loop hbt hk => exact pres_read_loop hf hu hbt hk hty
  | call hx => exact pres_read_call hf hu hx hty
  | refFunc hx => exact pres_read_refFunc hf hu hx hty
  | localGet hv => exact pres_read_localGet hf hu hv hty
  | globalGet hg => exact pres_read_globalGet hs hf hu hg hty
  | tableGetVal ht hr => exact pres_read_tableGetVal hs hf hu ht hr hty
  | callIndirectCall _ _ hfi hy => exact pres_read_callIndirect hf hu hfi hy hty
  | callAddr hfi hcode hk => exact pres_read_callAddr hs hfi hcode hk hty
  | tableFillSucc _ _ _ => exact pres_read_tableFillSucc hty
  | tableCopyLe _ _ _ _ _ => exact pres_read_tableCopy hty
  | tableCopyGt _ _ _ _ _ => exact pres_read_tableCopy hty
  | tableInitSucc _ he _ _ hr => exact pres_read_tableInitSucc hf hu he hr hty
  | memoryFillSucc _ _ _ => exact pres_read_memoryFillSucc hty
  | memoryCopyLe _ _ _ _ => exact pres_read_memoryCopy hty
  | memoryCopyGt _ _ _ _ => exact pres_read_memoryCopy hty
  | memoryInitSucc _ _ _ _ _ => exact pres_read_memoryInitSucc hty
  | _ =>
    first
    | exact AdminsOk.trap_it _
    | exact AdminsOk.flat0_const hty (fun _ hi => by cases hi; rfl)
        (fun _ hi => by cases hi; exact .intConst)
    | exact AdminsOk.flat1_const hty (by rfl)
        (fun _ hi => by cases hi <;> rfl)
        (fun _ hi => by
          cases hi <;> first | exact .intConst | exact .floatConst | exact .vecConst)
    | exact AdminsOk.flat2_const hty (by rfl)
        (by rfl)
        (fun _ hi => by cases hi; rfl)
        (fun _ hi => by
          cases hi; exact .vecConst)
    | exact AdminsOk.flat3_nil hty (by rfl)
        (by first | rfl | simp) (by rfl)
        (fun _ hi => by cases hi; rfl) (fun _ hi => by cases hi; rfl)

/-! ## Updating one instance of the store

Every state-writing rule of `8-reduction` replaces *one* instance by a related
one (`$with_global`, `$with_table`, `$with_mem`, `$with_elem`, `$with_data`,
`$growtable`, `$growmemory`). `Extend_store` and `Store_ok` are both rebuilt
from the corresponding one-instance fact. -/

theorem extendFunc_refl (x : FuncInst H) : ExtendFunc x x := rfl
theorem extendGlobal_refl (x : GlobalInst) : ExtendGlobal x x := ⟨rfl, Or.inr rfl⟩
theorem extendTable_refl (x : TableInst) : ExtendTable x x :=
  ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
theorem extendMem_refl (x : MemInst) : ExtendMem x x := ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩
theorem extendElem_refl (x : ElemInst) : ExtendElem x x := ⟨rfl, Or.inl rfl⟩
theorem extendData_refl (x : DataInst) : ExtendData x x := Or.inl rfl

/-- Overwriting one entry with a related one extends the list. -/
theorem ExtendsList.set {α : Type} {R : α → α → Prop} (hrefl : ∀ x, R x x) {l : List α}
    {i : Nat} {x y : α} (hx : l[i]? = some x) (hxy : R x y) : ExtendsList R l (l.set i y) := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hx
  refine ⟨by simp, ?_⟩
  intro j z hz
  by_cases hj : i = j
  · subst hj
    rw [hx] at hz
    obtain rfl := Option.some.inj hz
    exact ⟨y, by simp [hlt], hxy⟩
  · exact ⟨z, by simp [hj, hz], hrefl z⟩

theorem Extend.setGlobalInst {s : Store H} {a : GlobalAddr} {gi gi' : GlobalInst}
    (hg : s.globalInst? a = some gi) (h : ExtendGlobal gi gi') :
    Extend s (s.setGlobalInst a gi') :=
  { Extend.refl s with globals := ExtendsList.set extendGlobal_refl hg h }

theorem Extend.setTableInst {s : Store H} {a : TableAddr} {ti ti' : TableInst}
    (ht : s.tableInst? a = some ti) (h : ExtendTable ti ti') :
    Extend s (s.setTableInst a ti') :=
  { Extend.refl s with tables := ExtendsList.set extendTable_refl ht h }

theorem Extend.setMemInst {s : Store H} {a : MemAddr} {mi mi' : MemInst}
    (hm : s.memInst? a = some mi) (h : ExtendMem mi mi') :
    Extend s (s.setMemInst a mi') :=
  { Extend.refl s with mems := ExtendsList.set extendMem_refl hm h }

theorem Extend.setElemInst {s : Store H} {a : ElemAddr} {ei ei' : ElemInst}
    (he : s.elemInst? a = some ei) (h : ExtendElem ei ei') :
    Extend s (s.setElemInst a ei') :=
  { Extend.refl s with elems := ExtendsList.set extendElem_refl he h }

theorem Extend.setDataInst {s : Store H} {a : DataAddr} {di di' : DataInst}
    (hd : s.dataInst? a = some di) (h : ExtendData di di') :
    Extend s (s.setDataInst a di') :=
  { Extend.refl s with datas := ExtendsList.set extendData_refl hd h }

/-- `Store_ok` for a store that extends a well-typed one: every instance is
either an old one (which `*Ok.extend` carries over) or a new one that is
already known to be well typed. -/
theorem StoreOk.mk_of_extend {s s' : Store H} (hs : StoreOk s) (he : Extend s s')
    (hf : ∀ fi ∈ s'.funcs, fi ∈ s.funcs)
    (hg : ∀ gi ∈ s'.globals, gi ∈ s.globals ∨ GlobalInstOk s' gi)
    (ht : ∀ ti ∈ s'.tables, ti ∈ s.tables ∨ TableInstOk s' ti)
    (hm : ∀ mi ∈ s'.mems, mi ∈ s.mems ∨ MemInstOk mi)
    (hel : ∀ ei ∈ s'.elems, ei ∈ s.elems ∨ ElemInstOk s' ei) : StoreOk s' where
  funcs fi hfi := (hs.funcs fi (hf fi hfi)).extend hs he
  globals gi hgi := (hg gi hgi).elim (fun h => (hs.globals gi h).extend he) id
  tables ti hti := (ht ti hti).elim (fun h => (hs.tables ti h).extend he) id
  mems mi hmi := (hm mi hmi).elim (fun h => hs.mems mi h) id
  elems ei hei :=
    (hel ei hei).elim (fun h => ElemInstOk.extend he (extendElem_refl ei) (hs.elems ei h)) id
  datas _ _ := trivial

theorem StoreOk.setGlobalInst {s : Store H} (hs : StoreOk s) {a : GlobalAddr}
    {gi gi' : GlobalInst} (hg : s.globalInst? a = some gi) (hext : ExtendGlobal gi gi')
    (hok : GlobalInstOk s gi') : StoreOk (s.setGlobalInst a gi') := by
  refine StoreOk.mk_of_extend hs (Extend.setGlobalInst hg hext) (fun _ h => h) ?_
    (fun _ h => .inl h) (fun _ h => .inl h) (fun _ h => .inl h)
  intro g hgm
  rcases List.mem_or_eq_of_mem_set hgm with h | rfl
  · exact .inl h
  · exact .inr (hok.extend (Extend.setGlobalInst hg hext))

theorem StoreOk.setTableInst {s : Store H} (hs : StoreOk s) {a : TableAddr}
    {ti ti' : TableInst} (ht : s.tableInst? a = some ti) (hext : ExtendTable ti ti')
    (hok : TableInstOk s ti') : StoreOk (s.setTableInst a ti') := by
  refine StoreOk.mk_of_extend hs (Extend.setTableInst ht hext) (fun _ h => h)
    (fun _ h => .inl h) ?_ (fun _ h => .inl h) (fun _ h => .inl h)
  intro t htm
  rcases List.mem_or_eq_of_mem_set htm with h | rfl
  · exact .inl h
  · exact .inr (hok.extend (Extend.setTableInst ht hext))

theorem StoreOk.setMemInst {s : Store H} (hs : StoreOk s) {a : MemAddr} {mi mi' : MemInst}
    (hm : s.memInst? a = some mi) (hext : ExtendMem mi mi') (hok : MemInstOk mi') :
    StoreOk (s.setMemInst a mi') := by
  refine StoreOk.mk_of_extend hs (Extend.setMemInst hm hext) (fun _ h => h)
    (fun _ h => .inl h) (fun _ h => .inl h) ?_ (fun _ h => .inl h)
  intro m hmm
  rcases List.mem_or_eq_of_mem_set hmm with h | rfl
  · exact .inl h
  · exact .inr hok

theorem StoreOk.setElemInst {s : Store H} (hs : StoreOk s) {a : ElemAddr} {ei ei' : ElemInst}
    (he : s.elemInst? a = some ei) (hext : ExtendElem ei ei') (hok : ElemInstOk s ei') :
    StoreOk (s.setElemInst a ei') := by
  refine StoreOk.mk_of_extend hs (Extend.setElemInst he hext) (fun _ h => h)
    (fun _ h => .inl h) (fun _ h => .inl h) (fun _ h => .inl h) ?_
  intro e hem
  rcases List.mem_or_eq_of_mem_set hem with h | rfl
  · exact .inl h
  · exact .inr (ElemInstOk.extend (Extend.setElemInst he hext) (extendElem_refl _) hok)

theorem StoreOk.setDataInst {s : Store H} (hs : StoreOk s) {a : DataAddr} {di di' : DataInst}
    (hd : s.dataInst? a = some di) (hext : ExtendData di di') :
    StoreOk (s.setDataInst a di') :=
  StoreOk.mk_of_extend hs (Extend.setDataInst hd hext) (fun _ h => h)
    (fun _ h => .inl h) (fun _ h => .inl h) (fun _ h => .inl h) (fun _ h => .inl h)

/-! ## Preservation for the state-writing rules of `Step` (`8-reduction:5`) -/

/-- `Step/local.set` (`8-reduction:380`): the store does not change and the
frame's local `x` is overwritten with a value of its declared type, so
`Frame_ok` holds again with the *same* context. (This is the whole reason 2.0
needs no context ordering in `Step.preservation_gen`.) -/
theorem pres_localSet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} :
    PresStmt (H := H) ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ ⟨s, f.setLocal x v, []⟩ := by
  intro Cf Ct it hs hf hu hty
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv (vs := [v]) hty
  obtain ⟨t, ts', hv, hts, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  cases hts
  cases hi with
  | @localSet _ _ t₀ hx =>
    obtain ⟨hp1, hp2⟩ := sub_split_right (d := [CValType.val t₀]) (by simp) hp
    obtain hteq : [CValType.val t₀] = liftResult [t] := CResultType.sub_liftResult_iff.mp hp2
    obtain rfl : t₀ = t := by simpa using hteq
    refine ⟨hs, Extend.refl s, ?_,
      AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp1) hr .nil⟩
    obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
    refine ⟨C₀, lts, hm, ?_, rfl⟩
    have hxl : lts[x.toNat]? = some t₀ := by
      rw [hu.locals_eq] at hx
      simpa [hm.locals_nil] using hx
    exact forall₂_set hl x.toNat v t₀ hxl hv

/-- `Step/global.set` (`8-reduction:392`): `$with_global(z, x, val)`. The
global is mutable (`Instr_ok/global.set`, `6-typing:390`), so `Extend_globalinst`
(`7.1-soundness:278`) admits the new value, and the value has the global's
declared type, so `Globalinst_ok` holds again. -/
theorem pres_globalSet {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val} {a : GlobalAddr}
    {gi : GlobalInst} (ha : f.module.globalAddr? x = some a)
    (hg : s.globalInst? a = some gi) :
    PresStmt (H := H) ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩
      ⟨s.setGlobalInst a { gi with value := v }, f, []⟩ := by
  intro Cf Ct it hs hf hu hty
  obtain ⟨ts, us, it₀, hvs, hi, hp, hr⟩ := AdminsOk.flat_inv (vs := [v]) hty
  obtain ⟨t, ts', hv, hts, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  cases hts
  cases hi with
  | @globalSet _ _ gt hgt hmut =>
    obtain ⟨a', gi', ha', hgi', -, hgty⟩ := hf.global_bridge (by rw [← hu.globals_eq]; exact hgt)
    have haa : a' = a := by rw [ha] at ha'; exact (Option.some.inj ha').symm
    subst haa
    have hgg : gi' = gi := by rw [hg] at hgi'; exact (Option.some.inj hgi').symm
    subst hgg
    obtain ⟨hp1, hp2⟩ := sub_split_right (d := [CValType.val gt.value]) (by simp) hp
    have hteq : gt.value = t := by
      have := CResultType.sub_liftResult_iff.mp hp2
      simpa using this
    have hvg : ValOk s v gi'.type.value := by rw [hgty, hteq]; exact hv
    have hext : ExtendGlobal gi' { gi' with value := v } := ⟨rfl, .inl (by rw [hgty]; exact hmut)⟩
    have hok : GlobalInstOk s { gi' with value := v } := ⟨trivial, hvg⟩
    have he := Extend.setGlobalInst hg hext
    refine ⟨hs.setGlobalInst hg hext hok, he, hf.extend hs he, AdminsOk.extend hs he ?_⟩
    exact AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp1) hr .nil

/-- `Step/table.set-val` (`8-reduction:410`): `$with_table(z, x, i, ref)`. The
written reference has the table's element type, so `Tableinst_ok` holds again,
and the length is unchanged, so `Extend_tableinst` holds. -/
theorem pres_tableSetVal {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {r : Ref}
    {a : TableAddr} {ti : TableInst} (ha : f.module.tableAddr? x = some a)
    (ht : s.tableInst? a = some ti) (hlt : i.toNat < ti.refs.length) :
    PresStmt (H := H) ⟨s, f, [constI32 i, aref r, .plain (.tableSet x)]⟩
      ⟨s.setTableInst a (ti.setRef i.toNat r), f, []⟩ := by
  intro Cf Ct it hs hf hu hty
  obtain ⟨ts, us, it₀, hvs, hi, hp, hres⟩ :=
    AdminsOk.flat_inv (vs := [Val.i32 i, Val.ref r]) hty
  obtain ⟨t₁, ts₁, hv₁, hts₁, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  obtain ⟨t₂, ts₂, hv₂, hts₂, rfl⟩ := List.forall₂_cons_left_iff.mp hts₁
  cases hts₂
  cases hi with
  | @tableSet _ _ tt hx =>
    obtain ⟨a', ti', ha', hti', -, hsub⟩ := hf.table_bridge (by rw [← hu.tables_eq]; exact hx)
    have haa : a' = a := by rw [ha] at ha'; exact (Option.some.inj ha').symm
    subst haa
    have htt : ti' = ti := by rw [ht] at hti'; exact (Option.some.inj hti').symm
    subst htt
    obtain ⟨hp1, hp2⟩ :=
      sub_split_right (d := [CValType.val ValType.i32, CValType.val (ValType.ref tt.element)])
        (by simp) hp
    have hteq := CResultType.sub_liftResult_iff.mp hp2
    obtain ⟨-, hte⟩ : ValType.i32 = t₁ ∧ ValType.ref tt.element = t₂ := by simpa using hteq
    subst hte
    cases hv₂ with
    | ref hrok =>
      have hok0 := hs.tables ti' (getElem?_mem hti')
      have hrok' : RefOk s r ti'.type.element := by rw [hsub.2]; exact hrok
      have hext : ExtendTable ti' (ti'.setRef i.toNat r) :=
        ⟨rfl, rfl, Nat.le_refl _, by simp [TableInst.setRef]⟩
      have hok : TableInstOk s (ti'.setRef i.toNat r) := by
        refine ⟨hok0.1, by simpa [TableInst.setRef] using hok0.2.1, ?_⟩
        intro r' hr'
        rcases List.mem_or_eq_of_mem_set hr' with h | rfl
        · exact hok0.2.2 r' h
        · exact hrok'
      have he := Extend.setTableInst ht hext
      refine ⟨hs.setTableInst ht hext hok, he, hf.extend hs he, AdminsOk.extend hs he ?_⟩
      exact AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp1) hres .nil

/-- `Step/table.grow-succeed` (`8-reduction:420`): `$growtable(ti, n, r)`
appends `r^n` and sets the type's minimum to the new size, so `Tableinst_ok`
holds again and `Extend_tableinst` (`7.1-soundness:287`) is satisfied. The
result is the **old** size. -/
theorem pres_tableGrowSucceed {s : Store H} {f : Frame} {x : TableIdx} {n : BitVec 32}
    {r : Ref} {a : TableAddr} {ti ti' : TableInst} (ha : f.module.tableAddr? x = some a)
    (ht : s.tableInst? a = some ti) (hg : ti.grow? n.toNat r = some ti') :
    PresStmt (H := H) ⟨s, f, [aref r, constI32 n, .plain (.tableGrow x)]⟩
      ⟨s.setTableInst a ti', f, [constI32 (BitVec.ofNat 32 ti.refs.length)]⟩ := by
  intro Cf Ct it hs hf hu hty
  obtain ⟨ts, us, it₀, hvs, hi, hp, hres⟩ :=
    AdminsOk.flat_inv (vs := [Val.ref r, Val.i32 n]) hty
  obtain ⟨t₁, ts₁, hv₁, hts₁, rfl⟩ := List.forall₂_cons_left_iff.mp hvs
  obtain ⟨t₂, ts₂, hv₂, hts₂, rfl⟩ := List.forall₂_cons_left_iff.mp hts₁
  cases hts₂
  cases hi with
  | @tableGrow _ _ tt hx =>
    obtain ⟨a', ti'', ha', hti', -, hsub⟩ := hf.table_bridge (by rw [← hu.tables_eq]; exact hx)
    have haa : a' = a := by rw [ha] at ha'; exact (Option.some.inj ha').symm
    subst haa
    have htt : ti'' = ti := by rw [ht] at hti'; exact (Option.some.inj hti').symm
    subst htt
    obtain ⟨hp1, hp2⟩ :=
      sub_split_right (d := [CValType.val (ValType.ref tt.element), CValType.val ValType.i32])
        (by simp) hp
    have hteq := CResultType.sub_liftResult_iff.mp hp2
    obtain ⟨hte, -⟩ : ValType.ref tt.element = t₁ ∧ ValType.i32 = t₂ := by simpa using hteq
    subst hte
    cases hv₁ with
    | ref hrok0 =>
      have hok0 := hs.tables ti'' (getElem?_mem hti')
      have hrok : RefOk s r ti''.type.element := by rw [hsub.2]; exact hrok0
      obtain ⟨hmin1, hmin2⟩ := TableInst.grow?_min hg
      obtain ⟨helt, hmax⟩ := TableInst.grow?_type hg
      have hlen := TableInst.grow?_refs_length hg
      have hrefs := TableInst.grow?_refs hg
      have hTOk : TableType.Ok ti'.type := by
        refine ⟨by rw [hmin1]; exact Nat.le_sub_one_of_lt hmin2, ?_⟩
        cases hm : ti'.type.limits.max with
        | none => trivial
        | some j =>
          have hj : ti''.type.limits.max = some j := by rw [← hmax]; exact hm
          exact ⟨by rw [hmin1]; exact TableInst.grow?_le_max hg hj,
            (hok0.1.max_bounds hj).2⟩
      have hok : TableInstOk s ti' := by
        refine ⟨hTOk, by rw [hlen, hmin1], ?_⟩
        rw [hrefs, helt]
        intro r' hr'
        rcases List.mem_append.mp hr' with h | h
        · exact hok0.2.2 r' h
        · obtain rfl := List.eq_of_mem_replicate h
          exact hrok
      have hext : ExtendTable ti'' ti' :=
        ⟨helt.symm, hmax.symm, by rw [hmin1, ← hok0.2.1]; omega, by rw [hlen]; omega⟩
      have he := Extend.setTableInst ht hext
      refine ⟨hs.setTableInst ht hext hok, he, hf.extend hs he, AdminsOk.extend hs he ?_⟩
      exact AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp1) hres
        (.single (.plain .intConst))

/-- `Step/elem.drop` (`8-reduction:483`): `$with_elem(z, x, eps)`. An empty
segment is trivially `Eleminst_ok`, and `Extend_eleminst` (`7.1-soundness:299`)
admits dropping the contents wholesale. -/
theorem pres_elemDrop {s : Store H} {f : Frame} {x : ElemIdx} {a : ElemAddr} {ei : ElemInst}
    (_ha : f.module.elemAddr? x = some a) (hei : s.elemInst? a = some ei) :
    PresStmt (H := H) ⟨s, f, [.plain (.elemDrop x)]⟩
      ⟨s.setElemInst a { ei with refs := [] }, f, []⟩ := by
  intro Cf Ct it hs hf hu hty
  have hext : ExtendElem ei { ei with refs := [] } := ⟨rfl, .inr rfl⟩
  have hok : ElemInstOk s { ei with refs := [] } := by intro r hr; cases hr
  have he := Extend.setElemInst hei hext
  refine ⟨hs.setElemInst hei hext hok, he, hf.extend hs he, AdminsOk.extend hs he ?_⟩
  exact AdminsOk.flat0 (fun _ hi => by cases hi; rfl) (fun _ hi => by cases hi; exact .nil) hty

/-- `Step/data.drop` (`8-reduction:663`): `$with_data(z, x, eps)`.
`Datainst_ok` (`7.1-soundness:123`) has no premises, so only `Extend_datainst`
has to be checked. -/
theorem pres_dataDrop {s : Store H} {f : Frame} {x : DataIdx} {a : DataAddr} {di : DataInst}
    (_ha : f.module.dataAddr? x = some a) (hd : s.dataInst? a = some di) :
    PresStmt (H := H) ⟨s, f, [.plain (.dataDrop x)]⟩
      ⟨s.setDataInst a ⟨ByteArray.empty⟩, f, []⟩ := by
  intro Cf Ct it hs hf hu hty
  have hext : ExtendData di ⟨ByteArray.empty⟩ := .inr rfl
  have he := Extend.setDataInst hd hext
  refine ⟨hs.setDataInst hd hext, he, hf.extend hs he, AdminsOk.extend hs he ?_⟩
  exact AdminsOk.flat0 (fun _ hi => by cases hi; rfl) (fun _ hi => by cases hi; exact .nil) hty

/-- `$with_mem(z, 0, i, j, b*)` keeps the memory's type and its size. -/
theorem MemInst.writeBytes?_eq {mi mi' : MemInst} {i j : Nat} {bs : Bytes}
    (h : mi.writeBytes? i j bs = some mi') :
    mi'.type = mi.type ∧ mi'.bytes.size = mi.bytes.size := by
  unfold MemInst.writeBytes? at h
  split at h
  · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hb⟩
  · exact absurd h (by simp)

/-- The memory-writing rules `Step/store-num-val` (`8-reduction:563`),
`/store-pack-val` (`:571`), `/vstore-val` (`:579`) and `/vstore_lane-val`
(`:588`): `$with_mem` keeps the memory's type and size, so `Meminst_ok`
(`7.1-soundness:104`) holds again and `Extend_meminst` (`:282`) is immediate.
The reduct of all four is `eps`. -/
theorem pres_memoryWrite {s : Store H} {f : Frame} {a : MemAddr} {mi mi' : MemInst}
    {i j : Nat} {bs : Bytes} {code code' : List Admin}
    (hm : s.memInst? a = some mi) (hw : mi.writeBytes? i j bs = some mi')
    (hcode : ∀ (Ct : Context) (it : InstrType), AdminsOk s Ct code it → AdminsOk s Ct code' it) :
    PresStmt (H := H) ⟨s, f, code⟩ ⟨s.setMemInst a mi', f, code'⟩ := by
  intro Cf Ct it hs hf hu hty
  obtain ⟨htype, hsize⟩ := MemInst.writeBytes?_eq hw
  have hok0 := hs.mems mi (getElem?_mem hm)
  have hok : MemInstOk mi' :=
    ⟨by rw [htype]; exact hok0.1, by rw [hsize, htype]; exact hok0.2⟩
  have hext : ExtendMem mi mi' :=
    ⟨by rw [htype], by rw [htype], by rw [hsize]⟩
  have he := Extend.setMemInst hm hext
  exact ⟨hs.setMemInst hm hext hok, he, hf.extend hs he,
    AdminsOk.extend hs he (hcode Ct it hty)⟩

/-- `Step/memory.grow-succeed` (`8-reduction:600`): `$growmemory(mi, n)` appends
`n` pages and sets the type's minimum to the new page count, so `Meminst_ok`
holds again and `Extend_meminst` is satisfied. The result is the **old** size in
pages. -/
theorem pres_memoryGrowSucceed {s : Store H} {f : Frame} {n : BitVec 32} {a : MemAddr}
    {mi mi' : MemInst} (_ha : f.module.memAddr? memIdx0 = some a)
    (hm : s.memInst? a = some mi) (hgw : mi.grow? n.toNat = some mi') :
    PresStmt (H := H) ⟨s, f, [constI32 n, .plain .memoryGrow]⟩
      ⟨s.setMemInst a mi', f, [constI32 (BitVec.ofNat 32 mi.pages)]⟩ := by
  intro Cf Ct it hs hf hu hty
  have hok0 := hs.mems mi (getElem?_mem hm)
  obtain ⟨hmin1, hmin2⟩ := MemInst.grow?_min hgw
  have hsize := MemInst.grow?_size hgw
  have hmax := MemInst.grow?_max hgw
  have hpages : mi.bytes.size / pageSize = mi.type.limits.min.val := by
    rw [hok0.2]
    simp only [pageSize]
    omega
  have hMOk : MemoryType.Ok mi'.type := by
    refine ⟨by rw [hmin1]; exact hmin2, ?_⟩
    cases hmm : mi'.type.limits.max with
    | none => trivial
    | some j =>
      have hj : mi.type.limits.max = some j := by rw [← hmax]; exact hmm
      exact ⟨by rw [hmin1]; exact MemInst.grow?_le_max hgw hj, (hok0.1.max_bounds hj).2⟩
  have hok : MemInstOk mi' := by
    refine ⟨hMOk, ?_⟩
    rw [hsize, hmin1, hpages, hok0.2]
    simp only [pageSize]
    omega
  have hext : ExtendMem mi mi' :=
    ⟨hmax.symm, by rw [hmin1, hpages]; omega, by rw [hsize]; omega⟩
  have he := Extend.setMemInst hm hext
  refine ⟨hs.setMemInst hm hext hok, he, hf.extend hs he, AdminsOk.extend hs he ?_⟩
  exact AdminsOk.flat1_const hty rfl (fun _ hi => by cases hi; rfl)
    (fun _ hi => by cases hi; exact .intConst)

/-- `Step/call_addr` on a host function that returns (deviation 3 of
`Execution/Step.lean`). The `HostOk` contract (`Soundness/Defs.lean`) gives a
well-typed, store-extending outcome; the typing of the arguments it needs is
read off the redex by `AdminsOk.flat_inv`. -/
theorem pres_callAddrHost {host : HostSemantics H} (hhost : HostOk host) {s s' : Store H}
    {f : Frame} {a : FuncAddr} {vs : List Val} {fi : FuncInst H} {hf : H} {r : Result}
    (hfa : s.funcInst? a = some fi) (hcode : fi.code = .host hf)
    (hk : vs.length = fi.type.params.length) (hout : host hf s vs (.returned s' r)) :
    PresStmt (H := H) ⟨s, f, vals vs ++ [.callAddr a]⟩ ⟨s', f, r.toAdmin⟩ := by
  intro Cf Ct it hs hfr hu hty
  obtain ⟨tm, hV, hI⟩ := AdminsOk.append_inv hty
  obtain ⟨ts, hvs, hsub⟩ := AdminsOk.vals_inv hV
  obtain ⟨us, it₀, ha, hp0, hres⟩ := AdminsOk.single_inv' hI
  cases ha with
  | @callAddr _ _ fi' hfi' =>
    have hff : fi' = fi := by rw [hfa] at hfi'; exact (Option.some.inj hfi').symm
    have hp : CResultType.Sub (it.params ++ liftResult ts)
        (us ++ liftResult fi'.type.params) := CResultType.sub_trans hsub hp0
    obtain ⟨hp1, hp2⟩ :=
      sub_split_right (d := liftResult fi'.type.params)
        (by simp [← hvs.length_eq, hk, hff]) hp
    obtain rfl : ts = fi'.type.params :=
      liftResult_inj (CResultType.sub_liftResult_iff.mp hp2).symm
    obtain ⟨hs', hext, hrt⟩ :=
      hhost.returned hs (getElem?_mem hfa) hcode (by rw [← hff]; exact hvs) hout
    refine ⟨hs', hext, hfr.extend hs hext, ?_⟩
    cases r with
    | trap => exact AdminsOk.trap_it _
    | values ws =>
      refine AdminsOk.rebuild (us := us) (ps := []) (by simpa using hp1) hres ?_
      have hr' : ValsOk s' ws (liftResult fi'.type.results) := by rw [hff]; exact hrt
      exact AdminsOk.of_vals (valsOk_liftResult.mp hr')

/-! ## Preservation (generalised) -/

/-- **Preservation, generalised** to code typed in a context `Ct` under the
frame's context `Cf`. Unlike Core 3.0 the conclusion keeps *both* contexts
fixed: 2.0 has no local-initialisation tracking, so no step moves them. -/
theorem Step.preservation_gen {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c c' : Config H} (h : Step P host c c') : PresStmt c c' := by
  induction h with
  | pure hp =>
    intro Cf Ct it hs hf _ hty
    exact PresConcl.pure hs hf (PureStep.preservation hty hp)
  | read hr =>
    intro Cf Ct it hs hf hu hty
    exact PresConcl.pure hs hf (ReadStep.preservation hs hf hu hty hr)
  | ctxtInstrs _ _ ih =>
    intro Cf Ct it hs hf hu hty
    obtain ⟨m₁, hA, hR⟩ := AdminsOk.append_inv hty
    obtain ⟨m₂, hV, hI⟩ := AdminsOk.append_inv hA
    obtain ⟨hs', hext, hf', hI'⟩ := ih hs hf hu hI
    exact ⟨hs', hext, hf',
      ((AdminsOk.extend hs hext hV).append hI').append (AdminsOk.extend hs hext hR)⟩
  | ctxtLabel _ ih =>
    intro Cf Ct it hs hf hu hty
    obtain ⟨us, it₀, ha, hp, hr⟩ := AdminsOk.single_inv' hty
    obtain ⟨t', ts, hn, rfl, hc, hb⟩ := ha.label_inv
    obtain ⟨hs', hext, hf', hb'⟩ := ih hs hf (hu.withLabel t') hb
    exact ⟨hs', hext, hf', AdminsOk.rebuild (ps := []) hp hr
      (.single (.label hn (AdminsOk.extend hs hext hc) hb'))⟩
  | ctxtFrame _ ih =>
    intro Cf Ct it hs hf hu hty
    obtain ⟨us, it₀, ha, hp, hr⟩ := AdminsOk.single_inv' hty
    obtain ⟨C', ts, hfr, hn, rfl, hb⟩ := ha.frame_inv
    obtain ⟨hs', hext, hfr', hb'⟩ := ih hs hfr ((CtxUnder.refl C').setReturn _) hb
    exact ⟨hs', hext, FrameOk.extend hs hext hf,
      AdminsOk.rebuild (ps := []) hp hr (.single (.frame hfr' hn hb'))⟩
  | callAddrHost hfa hcode hk hout => exact pres_callAddrHost hhost hfa hcode hk hout
  | callAddrHostDiv _ _ _ _ =>
    intro Cf Ct it hs hf _ hty
    exact PresConcl.pure hs hf hty
  | localSet => exact pres_localSet
  | globalSet ha hg => exact pres_globalSet ha hg
  | tableSetTrap _ _ _ =>
    intro Cf Ct it hs hf _ _
    exact PresConcl.pure hs hf (AdminsOk.trap_it _)
  | tableSetVal ha ht hi => exact pres_tableSetVal ha ht hi
  | tableGrowSucceed ha ht hg _ => exact pres_tableGrowSucceed ha ht hg
  | tableGrowFail _ _ _ =>
    intro Cf Ct it hs hf _ hty
    refine PresConcl.pure hs hf (AdminsOk.flat2_const hty (by simp) rfl ?_ ?_)
    · intro _ hi; cases hi; rfl
    · intro _ hi; cases hi; exact .intConst
  | elemDrop ha he => exact pres_elemDrop ha he
  | storeIntTrap _ _ _ | storeFloatTrap _ _ _ | storePackTrap _ _ _
  | vecStoreOob _ _ _ | vecStoreLaneOob _ _ _ =>
    intro Cf Ct it hs hf _ _
    exact PresConcl.pure hs hf (AdminsOk.trap_it _)
  | memoryGrowFail _ _ _ =>
    intro Cf Ct it hs hf _ hty
    refine PresConcl.pure hs hf (AdminsOk.flat1_const hty rfl ?_ ?_)
    · intro _ hi; cases hi; rfl
    · intro _ hi; cases hi; exact .intConst
  | dataDrop ha hd => exact pres_dataDrop ha hd
  | storeIntVal _ hm hw | storeFloatVal _ hm hw | storePackVal _ hm hw
  | vecStoreVal _ hm hw =>
    exact pres_memoryWrite hm hw (fun _ _ hty =>
      AdminsOk.flat2_nil hty rfl rfl (fun _ hi => by cases hi; rfl)
        (fun _ hi => by cases hi; rfl))
  | vecStoreLaneVal _ hm _ hw =>
    exact pres_memoryWrite hm hw (fun _ _ hty =>
      AdminsOk.flat2_nil hty rfl rfl (fun _ hi => by cases hi; rfl)
        (fun _ hi => by cases hi; rfl))
  | memoryGrowSucceed ha hm hgw _ => exact pres_memoryGrowSucceed ha hm hgw

/-- **Preservation (subject reduction).** A well-typed configuration steps to a
well-typed configuration of the *same* result type, over an extended store. -/
theorem Step.preservation {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts) (h : Step P host c c') :
    ConfigOk c' ts ∧ Extend c.store c'.store := by
  obtain ⟨C, ⟨hs, hf⟩, hty⟩ := hc
  obtain ⟨hs', hext, hf', hty'⟩ :=
    Step.preservation_gen hhost h hs hf (CtxUnder.refl C) hty
  exact ⟨⟨C, ⟨hs', hf'⟩, hty'⟩, hext⟩

end Silmaril.Wasm.V2.Execution
