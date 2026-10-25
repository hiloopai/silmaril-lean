module

public import Silmaril.Wasm.Binaryen.LinkBehaviours
public import Silmaril.Wasm.Link.OrdinarySimulation
public import Silmaril.Wasm.SingleThreaded.Locality

@[expose] public section

/-! # Index scoping of linked code, preserved without typing

`link_sound` (`Binaryen/Merge.lean`) compares behaviour sets of a typed invocation.
`Program.beh` does not assume `InvokeOk`, so `merge_sound` needs the comparison for
every argument list. This file gives it for both store relations of the linker,
without configuration typing:

* `renamed_behaviours`: a global-address renaming (`GlobalPermutation.Renamed`)
  keeps behaviour sets; the renaming simulation is untyped and the relation is
  symmetric.
* `related_behaviours`: the linking relation (`StoreRelation.Related`) keeps behaviour
  sets when the source store's function bodies are index-scoped (`StoreSc`, implied by
  `StoreOk`). Forward, `WholeSimulation.step` only needs annotation scoping, which is
  preserved by every step (`xas_step`); backward, a target step implies a source step
  (`back`), so a stuck source has a stuck target.

Scoping (`XI`) extends `CodeScope.Instruction` with the function, global and type
indices that the reduction rules look up: a relocated index can only be pulled back
to a source lookup when the source index is in range.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Link.GC
open Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type}

/-! ## Index scoping -/

/-- The indices, beyond the annotations of `CodeScope.Instruction`, that reduction
rules look up in the module instance. -/
def XE (m : ModuleInst) (i : Instr) : Prop :=
  match i with
  | .block _ body | .loop _ body | .tryTable _ _ body =>
      ∀ nested : { i // i ∈ body }, XE m nested.val
  | .if_ _ yes no =>
      (∀ nested : { i // i ∈ yes }, XE m nested.val) ∧
      (∀ nested : { i // i ∈ no }, XE m nested.val)
  | .call x | .returnCall x | .refFunc x => x.toNat < m.funcs.length
  | .globalGet x | .globalSet x => x.toNat < m.globals.length
  | .callIndirect _ y | .returnCallIndirect _ y => y.toNat < m.types.length
  | .structNew x | .structNewDefault x | .structGet _ x _ | .structSet x _ | .arrayNew x
  | .arrayNewDefault x | .arrayNewFixed x _ | .arrayNewData x _ | .arrayNewElem x _
  | .arrayGet _ x | .arraySet x | .arrayFill x | .arrayInitData x _ | .arrayInitElem x _ =>
      x.toNat < m.types.length
  | .arrayCopy x y => x.toNat < m.types.length ∧ y.toNat < m.types.length
  | _ => True
termination_by sizeOf i
decreasing_by
  all_goals have h := List.sizeOf_lt_of_mem nested.property
  all_goals simp_wf
  all_goals omega

/-- An instruction scoped in module instance `m`. -/
def XI (m : ModuleInst) (i : Instr) : Prop :=
  CodeScope.Instruction m.types.length i ∧ XE m i

/-- Administrative code scoped in `m`; frames scope their bodies in their own module. -/
def XA (m : ModuleInst) (a : Admin) : Prop :=
  match a with
  | .plain i => XI m i
  | .label _ cont body => (∀ i ∈ cont, XI m i) ∧ ∀ nested : { a // a ∈ body }, XA m nested.val
  | .handler _ _ body => ∀ nested : { a // a ∈ body }, XA m nested.val
  | .frame _ fr body => ∀ nested : { a // a ∈ body }, XA fr.module nested.val
  | _ => True
termination_by sizeOf a
decreasing_by
  all_goals have h := List.sizeOf_lt_of_mem nested.property
  all_goals simp_wf
  all_goals omega

def XAs (m : ModuleInst) (xs : List Admin) : Prop := ∀ a ∈ xs, XA m a

/-- Every stored wasm body is scoped in its own module instance. -/
def StoreSc (s : Store H) : Prop :=
  ∀ {a : Nat} {fi : FuncInst H} {code : Func}, s.funcs[a]? = some fi → fi.code = .wasm code →
    ∀ i ∈ code.body, XI fi.module i

@[simp] theorem xas_nil (m : ModuleInst) : XAs m [] := by simp [XAs]

@[simp] theorem xas_cons_iff {m : ModuleInst} {a : Admin} {xs : List Admin} :
    XAs m (a :: xs) ↔ XA m a ∧ XAs m xs := by simp [XAs]

@[simp] theorem xas_append_iff {m : ModuleInst} {xs ys : List Admin} :
    XAs m (xs ++ ys) ↔ XAs m xs ∧ XAs m ys := by
  simp only [XAs, List.mem_append, or_imp, forall_and]

@[simp] theorem xa_plain {m : ModuleInst} {i : Instr} : XA m (.plain i) ↔ XI m i := by rw [XA]

@[simp] theorem xa_label {m : ModuleInst} {k : Nat} {cont : List Instr} {body : List Admin} :
    XA m (.label k cont body) ↔ (∀ i ∈ cont, XI m i) ∧ XAs m body := by
  simp [XA, XAs]

@[simp] theorem xa_handler {m : ModuleInst} {k : Nat} {cs : List Catch} {body : List Admin} :
    XA m (.handler k cs body) ↔ XAs m body := by simp [XA, XAs]

@[simp] theorem xa_frame {m : ModuleInst} {k : Nat} {fr : Frame} {body : List Admin} :
    XA m (.frame k fr body) ↔ XAs fr.module body := by simp [XA, XAs]

@[simp] theorem xa_ref {m : ModuleInst} {r : Ref} : XA m (.ref r) := by simp [XA]

@[simp] theorem xa_trap {m : ModuleInst} : XA m .trap := by simp [XA]

@[simp] theorem xa_callRefType {m : ModuleInst} {d : DefType} : XA m (.callRefType d) := by
  simp [XA]

@[simp] theorem xa_returnCallRefType {m : ModuleInst} {d : DefType} :
    XA m (.returnCallRefType d) := by simp [XA]

theorem xa_value (m : ModuleInst) (v : Val) : XA m v.toAdmin := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r <;>
    simp [Val.toAdmin, XI, XE, CodeScope.Instruction]

@[simp] theorem xas_vals (m : ModuleInst) (vs : List Val) : XAs m (vals vs) := by
  intro a ha
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp ha
  exact xa_value m v

@[simp] theorem xas_expression {m : ModuleInst} {xs : List Instr} :
    XAs m (expression xs) ↔ ∀ i ∈ xs, XI m i := by
  simp [XAs, expression]

theorem xi_block {m : ModuleInst} {bt : BlockType} {body : List Instr} :
    XI m (.block bt body) ↔
      ControlViews.BlockScoped m.types.length bt ∧ ∀ i ∈ body, XI m i := by
  simp only [XI, CodeScope.Instruction, XE]
  constructor
  · rintro ⟨⟨hb, hc⟩, he⟩
    exact ⟨hb, fun i hi => ⟨hc ⟨i, hi⟩, he ⟨i, hi⟩⟩⟩
  · rintro ⟨hb, h⟩
    exact ⟨⟨hb, fun n => (h n.val n.property).1⟩, fun n => (h n.val n.property).2⟩

theorem xi_loop {m : ModuleInst} {bt : BlockType} {body : List Instr} :
    XI m (.loop bt body) ↔
      ControlViews.BlockScoped m.types.length bt ∧ ∀ i ∈ body, XI m i := by
  simp only [XI, CodeScope.Instruction, XE]
  constructor
  · rintro ⟨⟨hb, hc⟩, he⟩
    exact ⟨hb, fun i hi => ⟨hc ⟨i, hi⟩, he ⟨i, hi⟩⟩⟩
  · rintro ⟨hb, h⟩
    exact ⟨⟨hb, fun n => (h n.val n.property).1⟩, fun n => (h n.val n.property).2⟩

theorem xi_tryTable {m : ModuleInst} {bt : BlockType} {cs : List Catch} {body : List Instr} :
    XI m (.tryTable bt cs body) ↔
      ControlViews.BlockScoped m.types.length bt ∧ ∀ i ∈ body, XI m i := by
  simp only [XI, CodeScope.Instruction, XE]
  constructor
  · rintro ⟨⟨hb, hc⟩, he⟩
    exact ⟨hb, fun i hi => ⟨hc ⟨i, hi⟩, he ⟨i, hi⟩⟩⟩
  · rintro ⟨hb, h⟩
    exact ⟨⟨hb, fun n => (h n.val n.property).1⟩, fun n => (h n.val n.property).2⟩

theorem xi_if {m : ModuleInst} {bt : BlockType} {yes no : List Instr} :
    XI m (.if_ bt yes no) ↔
      ControlViews.BlockScoped m.types.length bt ∧ (∀ i ∈ yes, XI m i) ∧ ∀ i ∈ no, XI m i := by
  simp only [XI, CodeScope.Instruction, XE]
  constructor
  · rintro ⟨⟨hb, hy, hn⟩, hey, hen⟩
    exact ⟨hb, fun i hi => ⟨hy ⟨i, hi⟩, hey ⟨i, hi⟩⟩, fun i hi => ⟨hn ⟨i, hi⟩, hen ⟨i, hi⟩⟩⟩
  · rintro ⟨hb, hy, hn⟩
    exact ⟨⟨hb, fun n => (hy n.val n.property).1, fun n => (hn n.val n.property).1⟩,
      fun n => (hy n.val n.property).2, fun n => (hn n.val n.property).2⟩

/-- Scoping includes the annotation scoping of the linker's simulation. -/
theorem xa_admin (m : ModuleInst) : (a : Admin) → XA m a → AdminScope.Admin m.types.length a
  | .plain i, h => by
    rw [XA] at h
    rw [AdminScope.Admin]
    exact h.1
  | .label k cont body, h => by
    rw [XA] at h
    rw [AdminScope.Admin]
    exact ⟨fun i hi => (h.1 i hi).1, fun nested => xa_admin m nested.val (h.2 nested)⟩
  | .handler k cs body, h => by
    rw [XA] at h
    rw [AdminScope.Admin]
    exact fun nested => xa_admin m nested.val (h nested)
  | .frame k fr body, h => by
    rw [XA] at h
    rw [AdminScope.Admin]
    exact fun nested => xa_admin fr.module nested.val (h nested)
  | .ref r, _ => by simp only [AdminScope.Admin]
  | .callRefType d, _ => by simp only [AdminScope.Admin]
  | .returnCallRefType d, _ => by simp only [AdminScope.Admin]
  | .trap, _ => by simp only [AdminScope.Admin]
termination_by a => sizeOf a
decreasing_by
  all_goals have h := List.sizeOf_lt_of_mem nested.property
  all_goals simp_wf
  all_goals omega

theorem xas_admins {m : ModuleInst} {xs : List Admin} (h : XAs m xs) :
    AdminScope.Admins m.types.length xs := fun a ha => xa_admin m a (h a ha)

theorem StoreSc.functionScopes {s : Store H} (h : StoreSc s) : Simulation.FunctionScopes s :=
  fun lookup wasm i hi => (h lookup wasm i hi).1

theorem StoreSc.of_funcs {s s' : Store H} (h : StoreSc s) (hf : s'.funcs = s.funcs) :
    StoreSc s' := fun lookup wasm => h (hf ▸ lookup) wasm

/-! ## Scoping is preserved by every host-free step -/

/-- `RETURN_CALL_REF` turned into `CALL_REF` carries no scoped index. -/
theorem xa_retToCallIn (m m' : ModuleInst) {c : Admin} (hc : c.IsReturnCallRef) :
    XA m (c.retToCallIn m') := by
  cases c with
  | plain i =>
    cases i <;> try exact (hc : False).elim
    simp only [Admin.retToCallIn]
    split
    · exact xa_callRefType
    · simp [XI, XE, CodeScope.Instruction]
  | returnCallRefType d => exact xa_callRefType
  | _ => exact (hc : False).elim

theorem xas_parametric {m : ModuleInst} {is is' : List Admin} (h : ParametricStep is is') :
    XAs m is' := by
  cases h <;> simp [xa_value]

theorem xas_numeric {P : Profile} {m : ModuleInst} {is is' : List Admin} (h : NumericStep P is is') :
    XAs m is' := by
  cases h <;> simp [xa_value, constI32, XI, XE, CodeScope.Instruction]

theorem xas_vector {P : Profile} {m : ModuleInst} {is is' : List Admin} (h : VectorStep P is is') :
    XAs m is' := by
  cases h <;> simp [xa_value, constI32, vconst, XI, XE, CodeScope.Instruction]

theorem xas_variable {s s' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : VariableStep ⟨s, f, is⟩ ⟨s', f', is'⟩) : XAs f'.module is' := by
  cases h <;> simp [xa_value, XI, XE, CodeScope.Instruction]

theorem xas_reference {s s' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : RefStep ⟨s, f, is⟩ ⟨s', f', is'⟩) : XAs f'.module is' := by
  cases h <;> simp [xa_value, constI32]

theorem xas_table {P : Profile} {s s' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : TableStep P ⟨s, f, is⟩ ⟨s', f', is'⟩) : XAs f'.module is' := by
  cases h <;> simp [xa_value, constI32, aconst, XI, XE, CodeScope.Instruction]

theorem xas_memory {P : Profile} {s s' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : MemoryStep P ⟨s, f, is⟩ ⟨s', f', is'⟩) : XAs f'.module is' := by
  cases h <;> simp [xa_value, constI32, aconst, store8, load8u, XI, XE, CodeScope.Instruction]

theorem xas_aggregate {s s' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : AggregateStep ⟨s, f, is⟩ ⟨s', f', is'⟩) (hc : XAs f.module is) : XAs f'.module is' := by
  cases h
  case arrayNewElemAlloc =>
    rw [xas_append_iff]
    refine ⟨?_, ?_⟩
    · intro a ha
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
      exact xa_ref
    · simp_all [XI, XE, CodeScope.Instruction]
  all_goals simp_all [xa_value, constI32, arrRef, XI, XE, CodeScope.Instruction]

/-- **Scoping is an invariant of host-free execution**, with no typing. -/
theorem xas_step {P : Profile} {c c' : Config H} (h : Step P Simulation.noHost c c') :
    StoreSc c.store → XAs c.frame.module c.code → XAs c'.frame.module c'.code := by
  induction h with
  | parametric h => intro _ _; exact xas_parametric h
  | numeric h => intro _ _; exact xas_numeric h
  | vector h => intro _ _; exact xas_vector h
  | «variable» h =>
    rename_i c c'
    obtain ⟨s, f, is⟩ := c
    obtain ⟨s', f', is'⟩ := c'
    intro _ _
    exact xas_variable h
  | table h =>
    rename_i c c'
    obtain ⟨s, f, is⟩ := c
    obtain ⟨s', f', is'⟩ := c'
    intro _ _
    exact xas_table h
  | memory h =>
    rename_i c c'
    obtain ⟨s, f, is⟩ := c
    obtain ⟨s', f', is'⟩ := c'
    intro _ _
    exact xas_memory h
  | reference h =>
    rename_i c c'
    obtain ⟨s, f, is⟩ := c
    obtain ⟨s', f', is'⟩ := c'
    intro _ _
    exact xas_reference h
  | aggregate h =>
    rename_i c c'
    obtain ⟨s, f, is⟩ := c
    obtain ⟨s', f', is'⟩ := c'
    intro _ hc
    exact xas_aggregate h hc
  | @ctxtInstrs s s' f f' vs is is' rest h _ ih =>
    intro hs hc
    have hm : f'.module = f.module := Simulation.frame_module h
    simp only [xas_append_iff] at hc ⊢
    refine ⟨⟨xas_vals _ _, ih hs hc.1.2⟩, ?_⟩
    rw [hm]
    exact hc.2
  | @ctxtLabel s s' f f' n cont is is' h ih =>
    intro hs hc
    have hm : f'.module = f.module := Simulation.frame_module h
    simp only [xas_cons_iff, xa_label, xas_nil, and_true] at hc ⊢
    refine ⟨?_, ih hs hc.2⟩
    rw [hm]
    exact hc.1
  | ctxtHandler h ih =>
    intro hs hc
    simp only [xas_cons_iff, xa_handler, xas_nil, and_true] at hc ⊢
    exact ih hs hc
  | @ctxtFrame s s' f fi fi' n is is' h ih =>
    intro hs hc
    simp only [xas_cons_iff, xa_frame, xas_nil, and_true] at hc ⊢
    exact ih hs hc
  | block hbt hm =>
    intro _ hc
    simp only [xas_append_iff, xas_cons_iff, xa_plain, xas_nil, and_true, xi_block] at hc
    simp only [xas_cons_iff, xa_label, xas_nil, and_true, xas_append_iff, xas_vals,
      xas_expression, true_and, List.not_mem_nil, false_imp_iff, implies_true]
    exact hc.2.2
  | loop hbt hm =>
    intro _ hc
    simp only [xas_append_iff, xas_cons_iff, xa_plain, xas_nil, and_true] at hc
    have hc' := hc.2
    rw [xi_loop] at hc'
    simp only [xas_cons_iff, xa_label, xas_nil, and_true, xas_append_iff, xas_vals,
      xas_expression, true_and, List.mem_singleton, forall_eq]
    exact ⟨hc.2, hc'.2⟩
  | ifTrue hc =>
    intro _ h
    simp only [xas_cons_iff, xa_plain, xas_nil, and_true, xi_if] at h
    simp only [xas_cons_iff, xa_plain, xas_nil, and_true, xi_block]
    exact ⟨h.2.1, h.2.2.1⟩
  | ifFalse =>
    intro _ h
    simp only [xas_cons_iff, xa_plain, xas_nil, and_true, xi_if] at h
    simp only [xas_cons_iff, xa_plain, xas_nil, and_true, xi_block]
    exact ⟨h.2.1, h.2.2.2⟩
  | labelVals => intro _ _; exact xas_vals _ _
  | brLabelZero hl hn =>
    intro _ h
    simp only [xas_cons_iff, xa_label, xas_nil, and_true] at h
    simp only [xas_append_iff, xas_vals, xas_expression, true_and]
    exact h.1
  | brLabelSucc hl =>
    intro _ _
    simp [XI, XE, CodeScope.Instruction]
  | brHandler =>
    intro _ _
    simp [XI, XE, CodeScope.Instruction]
  | brIfTrue hc => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | brIfFalse => intro _ _; simp
  | brTableLt hi => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | brTableGe hi => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | brOnNullNull => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | brOnNullAddr hv => intro _ _; simp [xa_value]
  | brOnNonNullNull => intro _ _; simp
  | brOnNonNullAddr hv => intro _ _; simp [xa_value, XI, XE, CodeScope.Instruction]
  | brOnCastSucceed h => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | brOnCastFail h => intro _ _; simp
  | brOnCastFailSucceed h => intro _ _; simp
  | brOnCastFailFail h => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | call hx hf => intro _ _; simp
  | callRefNull hc => intro _ _; simp
  | callRefFunc hc hf he hn hcode =>
    intro hs _
    simp only [xas_cons_iff, xa_frame, xa_label, xas_nil, and_true, xas_expression,
      List.not_mem_nil, false_imp_iff, implies_true, true_and]
    exact hs hf hcode
  | callRefHost hc hf he hn hcode hhost => exact hhost.elim
  | callRefHostDiv hc hf he hn hcode hhost => exact hhost.elim
  | returnCall hx hf => intro _ _; simp
  | returnCallRefLabel hc =>
    intro _ h
    simp only [xas_cons_iff, xa_label, xas_nil, and_true, xas_append_iff] at h
    simp only [xas_append_iff, xas_vals, true_and, xas_cons_iff, xas_nil, and_true]
    exact h.2.1.2
  | returnCallRefHandler hc =>
    intro _ h
    simp only [xas_cons_iff, xa_handler, xas_nil, and_true, xas_append_iff] at h
    simp only [xas_append_iff, xas_vals, true_and, xas_cons_iff, xas_nil, and_true]
    exact h.1.2
  | returnCallRefFrameNull hc => intro _ _; simp
  | returnCallRefFrameAddr hc hf he hn =>
    rename_i fi _ _ _ _ _ _ _ _ _
    intro _ _
    simp only [xas_append_iff, xas_vals, xas_cons_iff, xa_ref, xas_nil, and_true, true_and]
    exact xa_retToCallIn _ _ hc
  | callIndirect =>
    intro _ h
    simp only [xas_cons_iff, xa_plain, xas_nil, and_true] at h
    simp only [XI, XE, CodeScope.Instruction] at h
    simp only [xas_cons_iff, xa_plain, xas_nil, and_true, XI, XE, CodeScope.Instruction,
      RefType.Scoped, HeapType.Scoped, and_self, true_and]
    exact h.2
  | returnCallIndirect =>
    intro _ h
    simp only [xas_cons_iff, xa_plain, xas_nil, and_true] at h
    simp only [XI, XE, CodeScope.Instruction] at h
    simp only [xas_cons_iff, xa_plain, xas_nil, and_true, XI, XE, CodeScope.Instruction,
      RefType.Scoped, HeapType.Scoped, and_self, true_and]
    exact h.2
  | frameVals hn => intro _ _; exact xas_vals _ _
  | returnFrame hn => intro _ _; exact xas_vals _ _
  | returnLabel => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | returnHandler => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | throw ht he hn => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | throwRefNull => intro _ _; simp
  | throwRefInstrs hne => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | throwRefLabel => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | throwRefFrame => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | throwRefHandlerEmpty => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | throwRefHandlerCatch he ht => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | throwRefHandlerCatchRef he ht => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | throwRefHandlerCatchAll => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | throwRefHandlerCatchAllRef => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | throwRefHandlerNext h => intro _ _; simp [XI, XE, CodeScope.Instruction]
  | tryTable hbt hm =>
    intro _ hc
    simp only [xas_append_iff, xas_cons_iff, xa_plain, xas_nil, and_true, xi_tryTable] at hc
    simp only [xas_cons_iff, xa_handler, xa_label, xas_nil, and_true, xas_append_iff, xas_vals,
      xas_expression, true_and, List.not_mem_nil, false_imp_iff, implies_true]
    exact hc.2.2
  | handlerVals => intro _ _; exact xas_vals _ _
  | trapInstrs hne => intro _ _; simp
  | trapLabel => intro _ _; simp
  | trapHandler => intro _ _; simp
  | trapFrame => intro _ _; simp

theorem funcs_step {P : Profile} {c c' : Config H} (h : Step P Simulation.noHost c c') :
    c'.store.funcs = c.store.funcs :=
  (SingleThreaded.Step.framesLocal h).1


/-! ## Validated code is scoped -/

theorem withLocals_counts (C : Context) (xs : List Nat) (lts : List LocalType) :
    (C.withLocals xs lts).types = C.types ∧ (C.withLocals xs lts).funcs = C.funcs ∧
      (C.withLocals xs lts).globals = C.globals := by
  induction xs generalizing C lts with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x xs ih =>
    cases lts with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons lt lts => exact ih (C.setLocal x lt) lts

theorem initLocals_counts (C : Context) (xs : List Nat) :
    (C.initLocals xs).types = C.types ∧ (C.initLocals xs).funcs = C.funcs ∧
      (C.initLocals xs).globals = C.globals :=
  withLocals_counts _ _ _

/-- The counts a module instance shares with a validation context. -/
def Fits (m : ModuleInst) (C : Context) : Prop :=
  m.types.length = C.types.length ∧ m.funcs.length = C.funcs.length ∧
    m.globals.length = C.globals.length

theorem lt_of_lookup {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- **Validated instructions satisfy the extra scoping.** -/
theorem xe_of_typing {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it) :
    ∀ i ∈ is, ∀ m : ModuleInst, Fits m C → XE m i := by
  refine InstrsOk.rec (motive_1 := fun C i _ _ => ∀ m : ModuleInst, Fits m C → XE m i)
    (motive_2 := fun C is _ _ => ∀ i ∈ is, ∀ m : ModuleInst, Fits m C → XE m i)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ h
  case refine_1 => intros C i it valid m _; cases valid <;> simp only [XE]
  case refine_2 => intros C i it valid m _; cases valid <;> simp only [XE]
  case refine_3 => intros C i it valid m _; cases valid <;> simp only [XE]
  case refine_4 =>
    intros C i it valid m hm
    cases valid <;> simp only [XE]
    case globalGet h => rw [hm.2.2]; exact lt_of_lookup h
    case globalSet h => rw [hm.2.2]; exact lt_of_lookup h
  case refine_5 => intros C i it valid m _; cases valid <;> simp only [XE]
  case refine_6 => intros C i it valid m _; cases valid <;> simp only [XE]
  case refine_7 =>
    intros C i it valid m hm
    cases valid <;> simp only [XE]
    case refFunc h _ => rw [hm.2.1]; exact lt_of_lookup h
    all_goals first
      | (rw [hm.1]; exact lt_of_lookup ‹C.type? _ = some _›)
      | (rename_i hd₁ _ hd₂ _ _
         exact ⟨by rw [hm.1]; exact lt_of_lookup hd₁, by rw [hm.1]; exact lt_of_lookup hd₂⟩)
  case refine_8 =>
    intros C bt body params results xs ht hb ih m hm
    rw [XE]
    exact fun nested => ih nested.val nested.property m hm
  case refine_9 =>
    intros C bt body params results xs ht hb ih m hm
    rw [XE]
    exact fun nested => ih nested.val nested.property m hm
  case refine_10 =>
    intros C bt yes no params results xs ys ht hy hn ihy ihn m hm
    rw [XE]
    exact ⟨fun nested => ihy nested.val nested.property m hm,
      fun nested => ihn nested.val nested.property m hm⟩
  case refine_18 =>
    intros C x d ps rs hf he m hm
    simp only [XE]
    rw [hm.2.1]
    exact lt_of_lookup hf
  case refine_20 =>
    intros C x y a l rt d ps rs ht hs hd he m hm
    simp only [XE]
    rw [hm.1]
    exact lt_of_lookup hd
  case refine_22 =>
    intros C x d ps rs rs' t₃ t₄ hf he hr hs hok m hm
    simp only [XE]
    rw [hm.2.1]
    exact lt_of_lookup hf
  case refine_24 =>
    intros C x y a l rt d ps rs rs' t₃ t₄ ht hs hd he hr hrs hok m hm
    simp only [XE]
    rw [hm.1]
    exact lt_of_lookup hd
  case refine_27 =>
    intros C bt cs body params results xs ht hb hc ih m hm
    rw [XE]
    exact fun nested => ih nested.val nested.property m hm
  case refine_28 => intros C i hi; simp only [List.not_mem_nil] at hi
  case refine_29 =>
    intros C i it valid ih j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact ih
  case refine_30 =>
    intros C left right params middle results xs ys hl hx hr ihl ihr i hi m hm
    rcases List.mem_append.mp hi with hi | hi
    · exact ihl i hi m hm
    · obtain ⟨h1, h2, h3⟩ := initLocals_counts C xs
      exact ihr i hi m ⟨hm.1.trans (congrArg List.length h1).symm,
        hm.2.1.trans (congrArg List.length h2).symm, hm.2.2.trans (congrArg List.length h3).symm⟩
  case refine_31 =>
    intros C a rest params middle results xs ys ha hx hr iha ihr j hj m hm
    rcases List.mem_cons.mp hj with rfl | hj
    · exact iha m hm
    · obtain ⟨h1, h2, h3⟩ := initLocals_counts C xs
      exact ihr j hj m ⟨hm.1.trans (congrArg List.length h1).symm,
        hm.2.1.trans (congrArg List.length h2).symm, hm.2.2.trans (congrArg List.length h3).symm⟩
  case refine_32 => intros C is it it' valid hs hok ih; exact ih
  case refine_33 => intros C is ts t₁ t₂ xs valid hok ih; exact ih
  all_goals intros; simp only [XE]

/-- **Stored bodies of a valid store are scoped.** -/
theorem storeSc_of_ok {s : Store H} (hs : StoreOk s) : StoreSc s := by
  intro a fi code lookup wasm i hi
  refine ⟨CodeScope.store_scope hs lookup wasm i hi, ?_⟩
  have valid := hs.funcs fi (List.mem_of_getElem? lookup)
  cases valid with
  | wasm _ hm codeEq hf _ =>
    rw [wasm] at codeEq
    cases codeEq
    cases hm with
    | mk _ _ hglobals hfuncs _ _ _ _ _ _ _ _ =>
      cases hf with
      | mk _ _ _ hb =>
        exact xe_of_typing hb i hi _ ⟨rfl, hfuncs.length_eq, hglobals.length_eq⟩
  | host _ _ codeEq =>
    rw [wasm] at codeEq
    cases codeEq

end Silmaril.Wasm.Binaryen.MergeUntyped
