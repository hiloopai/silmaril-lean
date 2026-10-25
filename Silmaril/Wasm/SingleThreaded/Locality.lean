module

public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.Execution.Core.Typing.Store

@[expose] public section

/-! # Locality and store-extension laws (U28)

* **Locality (shared-nothing).** An internal step can only change memories,
  tables and globals that are reachable from the thread: from the module instances
  of its frames, and transitively from the modules of functions whose addresses
  are reachable (through module instances, table entries, globals and code).
* **Extension.** On valid stores and typed threads, internal steps extend the
  store (`Extend`), so callout statuses of *other* parked threads are preserved.
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type}

/-- Frames syntactically present in administrative code (outermost first). -/
def codeFrames : List Admin → List Frame
  | [] => []
  | .label _ _ body :: rest => codeFrames body ++ codeFrames rest
  | .handler _ _ body :: rest => codeFrames body ++ codeFrames rest
  | .frame _ f body :: rest => f :: codeFrames body ++ codeFrames rest
  | _ :: rest => codeFrames rest

/-- Module instances syntactically present in administrative code. -/
def codeModules (code : List Admin) : List ModuleInst := (codeFrames code).map Frame.module

/-- References syntactically present in administrative code (reference values). -/
def codeRefs : List Admin → List Ref
  | [] => []
  | .ref r :: rest => r :: codeRefs rest
  | .label _ _ body :: rest => codeRefs body ++ codeRefs rest
  | .handler _ _ body :: rest => codeRefs body ++ codeRefs rest
  | .frame _ _ body :: rest => codeRefs body ++ codeRefs rest
  | _ :: rest => codeRefs rest

/-- Function addresses syntactically present in administrative code. -/
def codeFuncs (code : List Admin) : List Nat :=
  (codeRefs code).filterMap fun | .func a => some a | _ => none

/-- The frames of a thread: its own frame and every frame in its code. -/
def Thread.frames (s : Store H) (t : Thread) : List Frame :=
  (t.config s).frame :: codeFrames (t.config s).code

/-- Memory, table and global addresses a thread can touch in *one* step: those of
the module instances of its frames (graft from design A). -/
def Thread.activeMems (s : Store H) (t : Thread) : List Nat := (t.frames s).flatMap (·.module.mems)
def Thread.activeTables (s : Store H) (t : Thread) : List Nat :=
  (t.frames s).flatMap (·.module.tables)
def Thread.activeGlobals (s : Store H) (t : Thread) : List Nat :=
  (t.frames s).flatMap (·.module.globals)

mutual

/-- References reachable from a thread: from its code and the locals of its frames,
and transitively through globals, tables and element segments of reachable
module instances, fields of reachable structs, arrays and exceptions, and
`extern` wrappers. Closed under internal steps (`Internal.reachable_mono`). -/
inductive ReachableRef (s : Store H) (t : Thread) : Ref → Prop where
  | code {r : Ref} (h : r ∈ codeRefs (t.config s).code) : ReachableRef s t r
  | local {f : Frame} {r : Ref} (hf : f ∈ t.frames s) (hr : some (.ref r) ∈ f.locals) :
      ReachableRef s t r
  | global {m : ModuleInst} {ga : Nat} {gi : GlobalInst} {r : Ref} (hm : ReachableModule s t m)
      (hga : ga ∈ m.globals) (hg : s.globals[ga]? = some gi) (hv : gi.value = .ref r) :
      ReachableRef s t r
  | table {m : ModuleInst} {ta : Nat} {ti : TableInst} {r : Ref} (hm : ReachableModule s t m)
      (hta : ta ∈ m.tables) (ht : s.tables[ta]? = some ti) (hr : r ∈ ti.refs) :
      ReachableRef s t r
  | elem {m : ModuleInst} {ea : Nat} {ei : ElemInst} {r : Ref} (hm : ReachableModule s t m)
      (hea : ea ∈ m.elems) (he : s.elems[ea]? = some ei) (hr : r ∈ ei.refs) :
      ReachableRef s t r
  | structField {a : Nat} {si : StructInst} {r : Ref} (ha : ReachableRef s t (.struct a))
      (hs : s.structs[a]? = some si) (hr : FieldVal.val (.ref r) ∈ si.fields) :
      ReachableRef s t r
  | arrayField {a : Nat} {ai : ArrayInst} {r : Ref} (ha : ReachableRef s t (.array a))
      (hs : s.arrays[a]? = some ai) (hr : FieldVal.val (.ref r) ∈ ai.fields) :
      ReachableRef s t r
  | exnField {a : Nat} {e : ExnInst} {r : Ref} (ha : ReachableRef s t (.exn a))
      (hs : s.exns[a]? = some e) (hr : Val.ref r ∈ e.fields) : ReachableRef s t r
  | extern {r : Ref} (h : ReachableRef s t (.extern r)) : ReachableRef s t r

/-- Module instances reachable from a thread. -/
inductive ReachableModule (s : Store H) (t : Thread) : ModuleInst → Prop where
  | frame {f : Frame} (hf : f ∈ t.frames s) : ReachableModule s t f.module
  | ref {a : Nat} {fi : FuncInst H} (ha : ReachableRef s t (.func a))
      (hf : s.funcs[a]? = some fi) : ReachableModule s t fi.module
  | func {m : ModuleInst} {a : Nat} {fi : FuncInst H} (hm : ReachableModule s t m)
      (ha : a ∈ m.funcs) (hf : s.funcs[a]? = some fi) : ReachableModule s t fi.module

end

def ReachableMem (s : Store H) (t : Thread) (a : Nat) : Prop :=
  ∃ m, ReachableModule s t m ∧ a ∈ m.mems

def ReachableTable (s : Store H) (t : Thread) (a : Nat) : Prop :=
  ∃ m, ReachableModule s t m ∧ a ∈ m.tables

def ReachableGlobal (s : Store H) (t : Thread) (a : Nat) : Prop :=
  ∃ m, ReachableModule s t m ∧ a ∈ m.globals


/-! ## Frame-locality of single steps -/

theorem codeFrames_append (l₁ l₂ : List Admin) :
    codeFrames (l₁ ++ l₂) = codeFrames l₁ ++ codeFrames l₂ := by
  induction l₁ with
  | nil => simp [codeFrames]
  | cons a as ih => cases a <;> simp [codeFrames, ih]

theorem codeFrames_vals (vs : List Val) : codeFrames (vals vs) = [] := by
  induction vs with
  | nil => simp [vals, codeFrames]
  | cons v vs ih =>
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp_all [vals, codeFrames, Val.toAdmin]

/-- The store changes of a step only concern the frames `fs` (and never functions). -/
def FramesLocal (fs : List Frame) (s s' : Store H) : Prop :=
  s'.funcs = s.funcs ∧
  (∀ a, a ∉ fs.flatMap (·.module.mems) → s'.mems[a]? = s.mems[a]?) ∧
  (∀ a, a ∉ fs.flatMap (·.module.tables) → s'.tables[a]? = s.tables[a]?) ∧
  (∀ a, a ∉ fs.flatMap (·.module.globals) → s'.globals[a]? = s.globals[a]?)

theorem FramesLocal.refl (fs : List Frame) (s : Store H) : FramesLocal fs s s :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem FramesLocal.mono {fs gs : List Frame} {s s' : Store H} (h : FramesLocal fs s s')
    (hsub : ∀ f ∈ fs, f ∈ gs) : FramesLocal gs s s' := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, fun a ha => h1 a ?_, fun a ha => h2 a ?_, fun a ha => h3 a ?_⟩ <;>
  · simp only [List.mem_flatMap, not_exists, not_and] at ha ⊢
    exact fun f hf => ha f (hsub f hf)

theorem Store.mem?_spec {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst}
    (h : s.mem? f x = some (ma, mi)) : ma ∈ f.module.mems := by
  unfold Store.mem? at h
  cases ha : f.module.mems[x.toNat]? with
  | none => simp [ha] at h
  | some b =>
    cases hb : s.mems[b]? with
    | none => simp [ha, hb] at h
    | some c =>
      simp [ha, hb] at h
      obtain ⟨rfl, -⟩ := h
      exact List.mem_of_getElem? ha

theorem Store.table?_spec {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
    (h : s.table? f x = some (ta, ti)) : ta ∈ f.module.tables := by
  unfold Store.table? at h
  cases ha : f.module.tables[x.toNat]? with
  | none => simp [ha] at h
  | some b =>
    cases hb : s.tables[b]? with
    | none => simp [ha, hb] at h
    | some c =>
      simp [ha, hb] at h
      obtain ⟨rfl, -⟩ := h
      exact List.mem_of_getElem? ha

theorem Store.global?_spec {s : Store H} {f : Frame} {x : GlobalIdx} {ga : Nat} {gi : GlobalInst}
    (h : s.global? f x = some (ga, gi)) : ga ∈ f.module.globals := by
  unfold Store.global? at h
  cases ha : f.module.globals[x.toNat]? with
  | none => simp [ha] at h
  | some b =>
    cases hb : s.globals[b]? with
    | none => simp [ha, hb] at h
    | some c =>
      simp [ha, hb] at h
      obtain ⟨rfl, -⟩ := h
      exact List.mem_of_getElem? ha

theorem FramesLocal.setMem {f : Frame} {s : Store H} {ma : Nat} {mi : MemInst}
    (h : ma ∈ f.module.mems) : FramesLocal [f] s (s.setMem ma mi) := by
  refine ⟨rfl, fun a ha => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  have : ma ≠ a := by rintro rfl; simp_all
  simp [Store.setMem, List.getElem?_set_ne this]

theorem FramesLocal.setTable {f : Frame} {s : Store H} {ta : Nat} {ti : TableInst}
    (h : ta ∈ f.module.tables) : FramesLocal [f] s (s.setTable ta ti) := by
  refine ⟨rfl, fun _ _ => rfl, fun a ha => ?_, fun _ _ => rfl⟩
  have : ta ≠ a := by rintro rfl; simp_all
  simp [Store.setTable, List.getElem?_set_ne this]

theorem FramesLocal.setGlobal {f : Frame} {s : Store H} {ga : Nat} {v : Val}
    (h : ga ∈ f.module.globals) : FramesLocal [f] s (s.setGlobal ga v) := by
  refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun a ha => ?_⟩
  have : ga ≠ a := by rintro rfl; simp_all
  simp [Store.setGlobal, this]

theorem FramesLocal.funcs {fs : List Frame} {s s' : Store H} (h0 : s'.funcs = s.funcs)
    (h1 : s'.mems = s.mems) (h2 : s'.tables = s.tables) (h3 : s'.globals = s.globals) :
    FramesLocal fs s s' :=
  ⟨h0, fun _ _ => by rw [h1], fun _ _ => by rw [h2], fun _ _ => by rw [h3]⟩

theorem VariableStep.framesLocal {c c' : Config H} (h : VariableStep c c') :
    FramesLocal [c.frame] c.store c'.store := by
  cases h with
  | globalSet hg => exact FramesLocal.setGlobal (Store.global?_spec hg)
  | _ => exact FramesLocal.refl _ _

theorem TableStep.framesLocal {P : Profile} {c c' : Config H} (h : TableStep P c c') :
    FramesLocal [c.frame] c.store c'.store := by
  cases h with
  | setVal ht => exact FramesLocal.setTable (Store.table?_spec ht)
  | growSucceed ht => exact FramesLocal.setTable (Store.table?_spec ht)
  | elemDrop => exact FramesLocal.funcs rfl rfl rfl rfl
  | _ => exact FramesLocal.refl _ _

theorem MemoryStep.framesLocal {P : Profile} {c c' : Config H} (h : MemoryStep P c c') :
    FramesLocal [c.frame] c.store c'.store := by
  cases h with
  | storeIntVal hm => exact FramesLocal.setMem (Store.mem?_spec hm)
  | storePackVal hm => exact FramesLocal.setMem (Store.mem?_spec hm)
  | storeFloatVal hm => exact FramesLocal.setMem (Store.mem?_spec hm)
  | vecStoreVal hm => exact FramesLocal.setMem (Store.mem?_spec hm)
  | vecStoreLaneVal hm => exact FramesLocal.setMem (Store.mem?_spec hm)
  | growSucceed hm => exact FramesLocal.setMem (Store.mem?_spec hm)
  | dataDrop => exact FramesLocal.funcs rfl rfl rfl rfl
  | _ => exact FramesLocal.refl _ _

theorem RefStep.framesLocal {c c' : Config H} (h : RefStep c c') :
    FramesLocal [c.frame] c.store c'.store := by
  cases h <;> exact FramesLocal.refl _ _

theorem AggregateStep.framesLocal {c c' : Config H} (h : AggregateStep c c') :
    FramesLocal [c.frame] c.store c'.store := by
  cases h <;> exact FramesLocal.refl _ _

/-- A host-free step only changes the memories, tables and globals of the frames
of its configuration, and never the functions. -/
theorem Step.framesLocal {P : Profile} {c c' : Config H}
    (h : Step P (fun _ _ _ _ => False) c c') :
    FramesLocal (c.frame :: codeFrames c.code) c.store c'.store := by
  induction h with
  | «variable» h => exact (VariableStep.framesLocal h).mono (by simp)
  | table h => exact (TableStep.framesLocal h).mono (by simp)
  | memory h => exact (MemoryStep.framesLocal h).mono (by simp)
  | reference h => exact (RefStep.framesLocal h).mono (by simp)
  | aggregate h => exact (AggregateStep.framesLocal h).mono (by simp)
  | ctxtInstrs _ _ ih =>
    refine ih.mono ?_
    intro f hf
    simp only [List.mem_cons, codeFrames_append, codeFrames_vals, List.nil_append,
      List.mem_append] at hf ⊢
    tauto
  | ctxtLabel _ ih =>
    refine ih.mono ?_
    intro f hf
    simp only [List.mem_cons, codeFrames, List.append_nil] at hf ⊢
    exact hf
  | ctxtHandler _ ih =>
    refine ih.mono ?_
    intro f hf
    simp only [List.mem_cons, codeFrames, List.append_nil] at hf ⊢
    exact hf
  | ctxtFrame _ ih =>
    refine ih.mono ?_
    intro f hf
    simp only [List.mem_cons, codeFrames, List.append_nil] at hf ⊢
    tauto
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | throw => exact FramesLocal.funcs rfl rfl rfl rfl
  | _ => exact FramesLocal.refl _ _

attribute [local simp] Thread.config_store

theorem Internal.framesLocal {o : GrowOracle} {s s' : Store H} {t t' : Thread}
    (h : Internal o (s, t) (s', t')) : FramesLocal (t.frames s) s s' := by
  obtain ⟨f', code', -, h⟩ := h
  have := Step.framesLocal h
  simpa [Thread.frames] using this

/-- **Milestone (single-step memory locality).** One internal step only touches
memories of the thread's active frames (graft from design A). -/
theorem Internal.mems_active {o : GrowOracle} {s s' : Store H} {t t' : Thread} {a : Nat}
    (h : Internal o (s, t) (s', t')) (ha : a ∉ t.activeMems s) : s'.mems[a]? = s.mems[a]? :=
  (Internal.framesLocal h).2.1 a ha

theorem Internal.tables_active {o : GrowOracle} {s s' : Store H} {t t' : Thread} {a : Nat}
    (h : Internal o (s, t) (s', t')) (ha : a ∉ t.activeTables s) :
    s'.tables[a]? = s.tables[a]? :=
  (Internal.framesLocal h).2.2.1 a ha

theorem Internal.globals_active {o : GrowOracle} {s s' : Store H} {t t' : Thread} {a : Nat}
    (h : Internal o (s, t) (s', t')) (ha : a ∉ t.activeGlobals s) :
    s'.globals[a]? = s.globals[a]? :=
  (Internal.framesLocal h).2.2.2 a ha

/-! ## Reachability closure under internal steps

`Good s t` over-approximates, in the store `s` *before* a step, the references
that a successor of thread `t` can hold: references reachable in `(s, t)`,
function references of reachable modules, scalars, `extern` wrappers of good
references, and fresh heap addresses (at or beyond the current heap size). -/

/-- The references a value contributes. -/
def _root_.Silmaril.Wasm.Execution.Core.Val.heapRefs : Val → List Ref
  | .ref r => [r]
  | _ => []

@[simp] theorem _root_.Silmaril.Wasm.Execution.Core.Val.mem_heapRefs {v : Val} {r : Ref} : r ∈ v.heapRefs ↔ v = .ref r := by
  cases v <;> simp [Val.heapRefs, eq_comm]

@[simp] theorem codeRefs_nil : codeRefs [] = [] := by simp [codeRefs]
@[simp] theorem codeRefs_plain (i : Instr) (l : List Admin) :
    codeRefs (.plain i :: l) = codeRefs l := by simp [codeRefs]
@[simp] theorem codeRefs_ref (r : Ref) (l : List Admin) :
    codeRefs (.ref r :: l) = r :: codeRefs l := by simp [codeRefs]
@[simp] theorem codeRefs_callRefType (d : DefType) (l : List Admin) :
    codeRefs (.callRefType d :: l) = codeRefs l := by simp [codeRefs]
@[simp] theorem codeRefs_returnCallRefType (d : DefType) (l : List Admin) :
    codeRefs (.returnCallRefType d :: l) = codeRefs l := by simp [codeRefs]
@[simp] theorem codeRefs_trap (l : List Admin) : codeRefs (.trap :: l) = codeRefs l := by
  simp [codeRefs]
@[simp] theorem codeRefs_label (n : Nat) (cont : List Instr) (body l : List Admin) :
    codeRefs (.label n cont body :: l) = codeRefs body ++ codeRefs l := by simp [codeRefs]
@[simp] theorem codeRefs_handler (n : Nat) (cs : List Catch) (body l : List Admin) :
    codeRefs (.handler n cs body :: l) = codeRefs body ++ codeRefs l := by simp [codeRefs]
@[simp] theorem codeRefs_frame (n : Nat) (f : Frame) (body l : List Admin) :
    codeRefs (.frame n f body :: l) = codeRefs body ++ codeRefs l := by simp [codeRefs]

@[simp] theorem codeRefs_append (l₁ l₂ : List Admin) :
    codeRefs (l₁ ++ l₂) = codeRefs l₁ ++ codeRefs l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => cases a <;> simp [ih]

@[simp] theorem codeRefs_toAdmin (v : Val) (l : List Admin) :
    codeRefs (v.toAdmin :: l) = v.heapRefs ++ codeRefs l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, Val.heapRefs]

@[simp] theorem codeRefs_vals (vs : List Val) : codeRefs (vals vs) = vs.flatMap Val.heapRefs := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih =>
    have : vals (v :: vs) = v.toAdmin :: vals vs := rfl
    rw [this, codeRefs_toAdmin, ih]
    simp

@[simp] theorem codeRefs_expression (es : List Instr) : codeRefs (expression es) = [] := by
  induction es with
  | nil => simp [expression]
  | cons i es ih => simpa [expression] using ih

@[simp] theorem codeRefs_map_ref (l : List Ref) : codeRefs (l.map Admin.ref) = l := by
  induction l with
  | nil => simp
  | cons r l ih => simp [ih]

@[simp] theorem codeFrames_nil : codeFrames [] = [] := by simp [codeFrames]
@[simp] theorem codeFrames_plain (i : Instr) (l : List Admin) :
    codeFrames (.plain i :: l) = codeFrames l := by simp [codeFrames]
@[simp] theorem codeFrames_ref (r : Ref) (l : List Admin) :
    codeFrames (.ref r :: l) = codeFrames l := by simp [codeFrames]
@[simp] theorem codeFrames_callRefType (d : DefType) (l : List Admin) :
    codeFrames (.callRefType d :: l) = codeFrames l := by simp [codeFrames]
@[simp] theorem codeFrames_returnCallRefType (d : DefType) (l : List Admin) :
    codeFrames (.returnCallRefType d :: l) = codeFrames l := by simp [codeFrames]
@[simp] theorem codeFrames_trap (l : List Admin) : codeFrames (.trap :: l) = codeFrames l := by
  simp [codeFrames]
@[simp] theorem codeFrames_label (n : Nat) (cont : List Instr) (body l : List Admin) :
    codeFrames (.label n cont body :: l) = codeFrames body ++ codeFrames l := by simp [codeFrames]
@[simp] theorem codeFrames_handler (n : Nat) (cs : List Catch) (body l : List Admin) :
    codeFrames (.handler n cs body :: l) = codeFrames body ++ codeFrames l := by
  simp [codeFrames]
@[simp] theorem codeFrames_frame (n : Nat) (f : Frame) (body l : List Admin) :
    codeFrames (.frame n f body :: l) = f :: (codeFrames body ++ codeFrames l) := by
  simp [codeFrames]

attribute [simp] codeFrames_append codeFrames_vals

@[simp] theorem codeFrames_toAdmin (v : Val) (l : List Admin) :
    codeFrames (v.toAdmin :: l) = codeFrames l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

@[simp] theorem codeFrames_expression (es : List Instr) : codeFrames (expression es) = [] := by
  induction es with
  | nil => simp [expression]
  | cons i es ih => simpa [expression] using ih

@[simp] theorem codeFrames_map_ref (l : List Ref) : codeFrames (l.map Admin.ref) = [] := by
  induction l with
  | nil => simp
  | cons r l ih => simp [ih]

/-- References that a successor of `t` may hold, judged in the pre-step store. -/
inductive Good (s : Store H) (t : Thread) : Ref → Prop where
  | reach {r : Ref} (h : ReachableRef s t r) : Good s t r
  | func {m : ModuleInst} {a : Nat} (hm : ReachableModule s t m) (ha : a ∈ m.funcs) :
      Good s t (.func a)
  | i31 (b : BitVec 31) : Good s t (.i31 b)
  | null : Good s t .null
  | extern {r : Ref} (h : Good s t r) : Good s t (.extern r)
  | struct {a : Nat} (h : s.structs.length ≤ a) : Good s t (.struct a)
  | array {a : Nat} (h : s.arrays.length ≤ a) : Good s t (.array a)
  | exn {a : Nat} (h : s.exns.length ≤ a) : Good s t (.exn a)

theorem Good.unextern {s : Store H} {t : Thread} {r : Ref} (h : Good s t (.extern r)) :
    Good s t r := by
  cases h with
  | reach h => exact .reach (.extern h)
  | extern h => exact h

theorem Good.structField {s : Store H} {t : Thread} {a : Nat} {si : StructInst} {r : Ref}
    (h : Good s t (.struct a)) (hs : s.structs[a]? = some si)
    (hr : FieldVal.val (.ref r) ∈ si.fields) : Good s t r := by
  cases h with
  | reach h => exact .reach (.structField h hs hr)
  | struct hl => simp [List.getElem?_eq_none hl] at hs

theorem Good.arrayField {s : Store H} {t : Thread} {a : Nat} {ai : ArrayInst} {r : Ref}
    (h : Good s t (.array a)) (hs : s.arrays[a]? = some ai)
    (hr : FieldVal.val (.ref r) ∈ ai.fields) : Good s t r := by
  cases h with
  | reach h => exact .reach (.arrayField h hs hr)
  | array hl => simp [List.getElem?_eq_none hl] at hs

theorem Good.exnField {s : Store H} {t : Thread} {a : Nat} {e : ExnInst} {r : Ref}
    (h : Good s t (.exn a)) (hs : s.exns[a]? = some e) (hr : Val.ref r ∈ e.fields) :
    Good s t r := by
  cases h with
  | reach h => exact .reach (.exnField h hs hr)
  | exn hl => simp [List.getElem?_eq_none hl] at hs

theorem Good.funcModule {s : Store H} {t : Thread} {a : Nat} {fi : FuncInst H}
    (h : Good s t (.func a)) (hf : s.funcs[a]? = some fi) : ReachableModule s t fi.module := by
  cases h with
  | reach h => exact .ref h hf
  | func hm ha => exact .func hm ha hf

def FrameGood (s : Store H) (t : Thread) (fr : Frame) : Prop :=
  ReachableModule s t fr.module ∧ ∀ r, some (Val.ref r) ∈ fr.locals → Good s t r

def CfgGood (s : Store H) (t : Thread) (c : Config H) : Prop :=
  (∀ r ∈ codeRefs c.code, Good s t r) ∧ FrameGood s t c.frame ∧
    ∀ fr ∈ codeFrames c.code, FrameGood s t fr

theorem CfgGood.sub {s s₀ s₁ : Store H} {t : Thread} {f : Frame} {code code' : List Admin}
    (h : CfgGood s t ⟨s₀, f, code⟩)
    (hr : ∀ r ∈ codeRefs code', r ∈ codeRefs code ∨ Good s t r)
    (hf : ∀ fr ∈ codeFrames code', fr ∈ codeFrames code) : CfgGood s t ⟨s₁, f, code'⟩ :=
  ⟨fun r hr' => (hr r hr').elim (h.1 r) id, h.2.1, fun fr hfr => h.2.2 fr (hf fr hfr)⟩

/-- The store after a step holds only old or good references. -/
structure StoreGood (s : Store H) (t : Thread) (s' : Store H) : Prop where
  funcs : s'.funcs = s.funcs
  globals : ∀ (ga : Nat) (gi' : GlobalInst) (r : Ref), s'.globals[ga]? = some gi' → gi'.value = .ref r →
    (∃ gi, s.globals[ga]? = some gi ∧ gi.value = .ref r) ∨ Good s t r
  tables : ∀ (ta : Nat) (ti' : TableInst) (r : Ref), s'.tables[ta]? = some ti' → r ∈ ti'.refs →
    (∃ ti, s.tables[ta]? = some ti ∧ r ∈ ti.refs) ∨ Good s t r
  elems : ∀ (ea : Nat) (ei' : ElemInst) (r : Ref), s'.elems[ea]? = some ei' → r ∈ ei'.refs →
    ∃ ei, s.elems[ea]? = some ei ∧ r ∈ ei.refs
  structs : ∀ (a : Nat) (si' : StructInst) (r : Ref), s'.structs[a]? = some si' → FieldVal.val (.ref r) ∈ si'.fields →
    (∃ si, s.structs[a]? = some si ∧ FieldVal.val (.ref r) ∈ si.fields) ∨ Good s t r
  arrays : ∀ (a : Nat) (ai' : ArrayInst) (r : Ref), s'.arrays[a]? = some ai' → FieldVal.val (.ref r) ∈ ai'.fields →
    (∃ ai, s.arrays[a]? = some ai ∧ FieldVal.val (.ref r) ∈ ai.fields) ∨ Good s t r
  exns : ∀ (a : Nat) (e' : ExnInst) (r : Ref), s'.exns[a]? = some e' → Val.ref r ∈ e'.fields →
    (∃ e, s.exns[a]? = some e ∧ Val.ref r ∈ e.fields) ∨ Good s t r

theorem StoreGood.of_eq {s s' : Store H} {t : Thread} (h0 : s'.funcs = s.funcs)
    (h1 : s'.globals = s.globals) (h2 : s'.tables = s.tables) (h3 : s'.elems = s.elems)
    (h4 : s'.structs = s.structs) (h5 : s'.arrays = s.arrays) (h6 : s'.exns = s.exns) :
    StoreGood s t s' where
  funcs := h0
  globals := fun _ gi _ hg hv => .inl ⟨gi, by rw [← h1]; exact hg, hv⟩
  tables := fun _ ti _ hg hv => .inl ⟨ti, by rw [← h2]; exact hg, hv⟩
  elems := fun _ ei _ hg hv => ⟨ei, by rw [← h3]; exact hg, hv⟩
  structs := fun _ si _ hg hv => .inl ⟨si, by rw [← h4]; exact hg, hv⟩
  arrays := fun _ ai _ hg hv => .inl ⟨ai, by rw [← h5]; exact hg, hv⟩
  exns := fun _ e _ hg hv => .inl ⟨e, by rw [← h6]; exact hg, hv⟩

theorem StoreGood.refl {s : Store H} {t : Thread} : StoreGood s t s :=
  .of_eq rfl rfl rfl rfl rfl rfl rfl

theorem getElem?_modify_some {α : Type} {l : List α} {i j : Nat} {g : α → α} {y : α}
    (h : (l.modify i g)[j]? = some y) : ∃ x, l[j]? = some x ∧ (y = x ∨ y = g x) := by
  rw [List.getElem?_modify] at h
  cases hx : l[j]? with
  | none => simp [hx] at h
  | some x =>
    simp only [hx, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
    refine ⟨x, rfl, ?_⟩
    split_ifs at h <;> simp_all

theorem getElem?_set_some {α : Type} {l : List α} {i j : Nat} {x y : α}
    (h : (l.set i x)[j]? = some y) : l[j]? = some y ∨ y = x := by
  rw [List.getElem?_set] at h
  split_ifs at h <;> simp_all

theorem getElem?_append_single {α : Type} {l : List α} {x y : α} {a : Nat}
    (h : (l ++ [x])[a]? = some y) : (l[a]? = some y) ∨ (a = l.length ∧ y = x) := by
  by_cases ha : a < l.length
  · left; rwa [List.getElem?_append_left ha] at h
  · right
    rw [List.getElem?_append_right (by omega)] at h
    have : a - l.length = 0 := by
      rcases hk : a - l.length with _ | k
      · rfl
      · rw [hk] at h; simp at h
    rw [this] at h
    simp at h
    exact ⟨by omega, h.symm⟩

theorem StoreGood.setGlobal {s : Store H} {t : Thread} {ga : Nat} {v : Val}
    (hv : ∀ r, v = .ref r → Good s t r) : StoreGood s t (s.setGlobal ga v) where
  funcs := rfl
  globals := by
    intro j gi' r hg hr
    obtain ⟨x, hx, rfl | rfl⟩ := getElem?_modify_some hg
    · exact .inl ⟨_, hx, hr⟩
    · exact .inr (hv r hr)
  tables := fun _ ti _ hg hv => .inl ⟨ti, hg, hv⟩
  elems := fun _ ei _ hg hv => ⟨ei, hg, hv⟩
  structs := fun _ si _ hg hv => .inl ⟨si, hg, hv⟩
  arrays := fun _ ai _ hg hv => .inl ⟨ai, hg, hv⟩
  exns := fun _ e _ hg hv => .inl ⟨e, hg, hv⟩

theorem StoreGood.setTable {s : Store H} {t : Thread} {ta : Nat} {ti : TableInst}
    (hti : ∀ r ∈ ti.refs, (∃ ti₀, s.tables[ta]? = some ti₀ ∧ r ∈ ti₀.refs) ∨ Good s t r) :
    StoreGood s t (s.setTable ta ti) where
  funcs := rfl
  globals := fun _ gi _ hg hv => .inl ⟨gi, hg, hv⟩
  tables := by
    intro j ti' r hg hr
    by_cases hj : ta = j
    · subst hj
      rw [Store.setTable, List.getElem?_set] at hg
      simp only [↓reduceIte] at hg
      split_ifs at hg
      simp only [Option.some.injEq] at hg
      subst hg
      exact hti r hr
    · rw [Store.setTable, List.getElem?_set, ite_eq_right hj] at hg
      exact .inl ⟨ti', hg, hr⟩
  elems := fun _ ei _ hg hv => ⟨ei, hg, hv⟩
  structs := fun _ si _ hg hv => .inl ⟨si, hg, hv⟩
  arrays := fun _ ai _ hg hv => .inl ⟨ai, hg, hv⟩
  exns := fun _ e _ hg hv => .inl ⟨e, hg, hv⟩

theorem StoreGood.setElemNil {s : Store H} {t : Thread} {ea : Nat} :
    StoreGood s t (s.setElem ea []) where
  funcs := rfl
  globals := fun _ gi _ hg hv => .inl ⟨gi, hg, hv⟩
  tables := fun _ ti _ hg hv => .inl ⟨ti, hg, hv⟩
  elems := by
    intro j ei' r hg hr
    obtain ⟨x, hx, rfl | rfl⟩ := getElem?_modify_some hg
    · exact ⟨_, hx, hr⟩
    · simp at hr
  structs := fun _ si _ hg hv => .inl ⟨si, hg, hv⟩
  arrays := fun _ ai _ hg hv => .inl ⟨ai, hg, hv⟩
  exns := fun _ e _ hg hv => .inl ⟨e, hg, hv⟩

theorem StoreGood.setStructField {s : Store H} {t : Thread} {a i : Nat} {fv : FieldVal}
    (hfv : ∀ r, fv = .val (.ref r) → Good s t r) : StoreGood s t (s.setStructField a i fv) where
  funcs := rfl
  globals := fun _ gi _ hg hv => .inl ⟨gi, hg, hv⟩
  tables := fun _ ti _ hg hv => .inl ⟨ti, hg, hv⟩
  elems := fun _ ei _ hg hv => ⟨ei, hg, hv⟩
  structs := by
    intro j si' r hg hr
    obtain ⟨x, hx, rfl | rfl⟩ := getElem?_modify_some hg
    · exact .inl ⟨_, hx, hr⟩
    · rcases List.mem_or_eq_of_mem_set hr with hr | hr
      · exact .inl ⟨_, hx, hr⟩
      · exact .inr (hfv r hr.symm)
  arrays := fun _ ai _ hg hv => .inl ⟨ai, hg, hv⟩
  exns := fun _ e _ hg hv => .inl ⟨e, hg, hv⟩

theorem StoreGood.setArrayField {s : Store H} {t : Thread} {a i : Nat} {fv : FieldVal}
    (hfv : ∀ r, fv = .val (.ref r) → Good s t r) : StoreGood s t (s.setArrayField a i fv) where
  funcs := rfl
  globals := fun _ gi _ hg hv => .inl ⟨gi, hg, hv⟩
  tables := fun _ ti _ hg hv => .inl ⟨ti, hg, hv⟩
  elems := fun _ ei _ hg hv => ⟨ei, hg, hv⟩
  structs := fun _ si _ hg hv => .inl ⟨si, hg, hv⟩
  arrays := by
    intro j ai' r hg hr
    obtain ⟨x, hx, rfl | rfl⟩ := getElem?_modify_some hg
    · exact .inl ⟨_, hx, hr⟩
    · rcases List.mem_or_eq_of_mem_set hr with hr | hr
      · exact .inl ⟨_, hx, hr⟩
      · exact .inr (hfv r hr.symm)
  exns := fun _ e _ hg hv => .inl ⟨e, hg, hv⟩

theorem StoreGood.addStruct {s : Store H} {t : Thread} {si : StructInst}
    (hsi : ∀ r, FieldVal.val (.ref r) ∈ si.fields → Good s t r) :
    StoreGood s t (s.addStruct si) where
  funcs := rfl
  globals := fun _ gi _ hg hv => .inl ⟨gi, hg, hv⟩
  tables := fun _ ti _ hg hv => .inl ⟨ti, hg, hv⟩
  elems := fun _ ei _ hg hv => ⟨ei, hg, hv⟩
  structs := by
    intro j si' r hg hr
    rcases getElem?_append_single hg with hg | ⟨-, rfl⟩
    · exact .inl ⟨_, hg, hr⟩
    · exact .inr (hsi r hr)
  arrays := fun _ ai _ hg hv => .inl ⟨ai, hg, hv⟩
  exns := fun _ e _ hg hv => .inl ⟨e, hg, hv⟩

theorem StoreGood.addArray {s : Store H} {t : Thread} {ai : ArrayInst}
    (hai : ∀ r, FieldVal.val (.ref r) ∈ ai.fields → Good s t r) :
    StoreGood s t (s.addArray ai) where
  funcs := rfl
  globals := fun _ gi _ hg hv => .inl ⟨gi, hg, hv⟩
  tables := fun _ ti _ hg hv => .inl ⟨ti, hg, hv⟩
  elems := fun _ ei _ hg hv => ⟨ei, hg, hv⟩
  structs := fun _ si _ hg hv => .inl ⟨si, hg, hv⟩
  arrays := by
    intro j ai' r hg hr
    rcases getElem?_append_single hg with hg | ⟨-, rfl⟩
    · exact .inl ⟨_, hg, hr⟩
    · exact .inr (hai r hr)
  exns := fun _ e _ hg hv => .inl ⟨e, hg, hv⟩

theorem StoreGood.addExn {s : Store H} {t : Thread} {e : ExnInst}
    (he : ∀ r, Val.ref r ∈ e.fields → Good s t r) : StoreGood s t (s.addExn e) where
  funcs := rfl
  globals := fun _ gi _ hg hv => .inl ⟨gi, hg, hv⟩
  tables := fun _ ti _ hg hv => .inl ⟨ti, hg, hv⟩
  elems := fun _ ei _ hg hv => ⟨ei, hg, hv⟩
  structs := fun _ si _ hg hv => .inl ⟨si, hg, hv⟩
  arrays := fun _ ai _ hg hv => .inl ⟨ai, hg, hv⟩
  exns := by
    intro j e' r hg hr
    rcases getElem?_append_single hg with hg | ⟨-, rfl⟩
    · exact .inl ⟨_, hg, hr⟩
    · exact .inr (he r hr)

theorem Store.global?_spec' {s : Store H} {f : Frame} {x : GlobalIdx} {ga : Nat}
    {gi : GlobalInst} (h : s.global? f x = some (ga, gi)) :
    ga ∈ f.module.globals ∧ s.globals[ga]? = some gi := by
  unfold Store.global? at h
  cases ha : f.module.globals[x.toNat]? with
  | none => simp [ha] at h
  | some b =>
    cases hb : s.globals[b]? with
    | none => simp [ha, hb] at h
    | some c =>
      simp [ha, hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_of_getElem? ha, hb⟩

theorem Store.table?_spec' {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat}
    {ti : TableInst} (h : s.table? f x = some (ta, ti)) :
    ta ∈ f.module.tables ∧ s.tables[ta]? = some ti := by
  unfold Store.table? at h
  cases ha : f.module.tables[x.toNat]? with
  | none => simp [ha] at h
  | some b =>
    cases hb : s.tables[b]? with
    | none => simp [ha, hb] at h
    | some c =>
      simp [ha, hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_of_getElem? ha, hb⟩

theorem Store.elem?_spec' {s : Store H} {f : Frame} {x : ElemIdx} {ea : Nat}
    {ei : ElemInst} (h : s.elem? f x = some (ea, ei)) :
    ea ∈ f.module.elems ∧ s.elems[ea]? = some ei := by
  unfold Store.elem? at h
  cases ha : f.module.elems[x.toNat]? with
  | none => simp [ha] at h
  | some b =>
    cases hb : s.elems[b]? with
    | none => simp [ha, hb] at h
    | some c =>
      simp [ha, hb] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_of_getElem? ha, hb⟩

theorem defaultVal?_ref {t : CValType} {r : Ref} (h : defaultVal? t = some (.ref r)) :
    r = .null := by
  unfold defaultVal? at h
  split at h <;> simp_all

theorem packField_eq_ref {z : CStorageType} {v : Val} {r : Ref}
    (h : packField z v = .val (.ref r)) : v = .ref r := by
  unfold packField at h
  split at h <;> simp_all

theorem unpackField_eq_ref {sx : Option Signedness} {fv : FieldVal} {r : Ref}
    (h : unpackField sx fv = .ref r) : fv = .val (.ref r) := by
  unfold unpackField at h
  split at h <;> simp_all [Val.i32]

theorem readField?_ne_ref {z : CStorageType} {b : ByteArray} {o : Nat} {r : Ref} :
    readField? z b o ≠ some (.ref r) := by
  unfold readField?
  split <;> simp [Val.i32]

theorem mapM_some_mem {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {vs : List β}, l.mapM g = some vs → ∀ v ∈ vs, ∃ x ∈ l, g x = some v
  | [], vs, h => by simp at h; subst h; simp
  | x :: l, vs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨a, ha, as, has, rfl⟩ := h
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨x, List.mem_cons_self .., ha⟩
    · obtain ⟨y, hy, hfy⟩ := mapM_some_mem has v hv
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

theorem Admin.retToCall_code {c : Admin} (hc : c.IsReturnCallRef) (l : List Admin) :
    codeRefs (c.retToCall :: l) = codeRefs l ∧ codeFrames (c.retToCall :: l) = codeFrames l := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [Admin.IsReturnCallRef, Admin.retToCall]
  rename_i i
  cases i <;> simp_all

theorem Admin.retToCallIn_code {c : Admin} (m : ModuleInst) (hc : c.IsReturnCallRef)
    (l : List Admin) :
    codeRefs (c.retToCallIn m :: l) = codeRefs l ∧
      codeFrames (c.retToCallIn m :: l) = codeFrames l := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [Admin.IsReturnCallRef, Admin.retToCallIn]
  rename_i i
  cases i <;> simp_all
  split <;> simp_all

section
variable {s : Store H} {t : Thread}

/-- Good references in the code of a configuration (helper). -/
theorem CfgGood.code {c : Config H} (hc : CfgGood s t c) {r : Ref} (hr : r ∈ codeRefs c.code) :
    Good s t r := hc.1 r hr

theorem ParametricStep.reach {is is' : List Admin} (h : ParametricStep is is') :
    (∀ r ∈ codeRefs is', r ∈ codeRefs is) ∧ ∀ fr ∈ codeFrames is', fr ∈ codeFrames is := by
  cases h <;> simp [constI32, Val.i32] <;> intros <;> simp_all

theorem NumericStep.reach {P : Profile} {is is' : List Admin} (h : NumericStep P is is') :
    (∀ r ∈ codeRefs is', r ∈ codeRefs is) ∧ ∀ fr ∈ codeFrames is', fr ∈ codeFrames is := by
  cases h <;> simp [constI32, Val.i32]

theorem VectorStep.reach {P : Profile} {is is' : List Admin} (h : VectorStep P is is') :
    (∀ r ∈ codeRefs is', r ∈ codeRefs is) ∧ ∀ fr ∈ codeFrames is', fr ∈ codeFrames is := by
  cases h <;> simp [constI32, Val.i32, vconst]

end

/-! ## One-step closure of `Good` -/

section StepGood
variable {t : Thread}

/-- Discharge `∀ x ∈ l', x ∈ l` side goals about code references/frames. -/
macro "sub_tac" : tactic => `(tactic| (intro x hx; simp [store8, load8u] at hx ⊢ <;> tauto))

@[simp] theorem codeRefs_constI32 (b : BitVec 32) (l : List Admin) :
    codeRefs (constI32 b :: l) = codeRefs l := by simp [constI32, Val.i32, Val.toAdmin]
@[simp] theorem codeFrames_constI32 (b : BitVec 32) (l : List Admin) :
    codeFrames (constI32 b :: l) = codeFrames l := by simp [constI32, Val.i32, Val.toAdmin]

/-- Rebuild `CfgGood` for a successor configuration. -/
theorem CfgGood.mk' {s s₀ s₁ : Store H} {f f' : Frame} {code code' : List Admin}
    (h : CfgGood s t ⟨s₀, f, code⟩) (hf : FrameGood s t f')
    (hr : ∀ r ∈ codeRefs code', r ∈ codeRefs code ∨ Good s t r)
    (hfr : ∀ fr ∈ codeFrames code', fr ∈ codeFrames code ∨ FrameGood s t fr) :
    CfgGood s t ⟨s₁, f', code'⟩ :=
  ⟨fun r hr' => (hr r hr').elim (h.1 r) id, hf,
    fun fr hfr' => (hfr fr hfr').elim (h.2.2 fr) id⟩

theorem CfgGood.same {s s₀ s₁ : Store H} {f : Frame} {code code' : List Admin}
    (h : CfgGood s t ⟨s₀, f, code⟩)
    (hr : ∀ r ∈ codeRefs code', r ∈ codeRefs code)
    (hfr : ∀ fr ∈ codeFrames code', fr ∈ codeFrames code) :
    CfgGood s t ⟨s₁, f, code'⟩ :=
  h.mk' h.2.1 (fun r h' => .inl (hr r h')) (fun fr h' => .inl (hfr fr h'))

theorem CfgGood.ref {s s₀ : Store H} {f : Frame} {code : List Admin} {r : Ref}
    (h : CfgGood s t ⟨s₀, f, code⟩) (hr : r ∈ codeRefs code) : Good s t r := h.1 r hr

theorem FrameGood.global {s : Store H} {f : Frame} {x : GlobalIdx} {ga : Nat} {gi : GlobalInst}
    {r : Ref} (hf : FrameGood s t f) (hg : s.global? f x = some (ga, gi))
    (hv : gi.value = .ref r) : Good s t r := by
  obtain ⟨h1, h2⟩ := Store.global?_spec' hg
  exact .reach (.global hf.1 h1 h2 hv)

theorem FrameGood.table {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
    {r : Ref} (hf : FrameGood s t f) (hg : s.table? f x = some (ta, ti))
    (hv : r ∈ ti.refs) : Good s t r := by
  obtain ⟨h1, h2⟩ := Store.table?_spec' hg
  exact .reach (.table hf.1 h1 h2 hv)

theorem FrameGood.elem {s : Store H} {f : Frame} {x : ElemIdx} {ea : Nat} {ei : ElemInst}
    {r : Ref} (hf : FrameGood s t f) (hg : s.elem? f x = some (ea, ei))
    (hv : r ∈ ei.refs) : Good s t r := by
  obtain ⟨h1, h2⟩ := Store.elem?_spec' hg
  exact .reach (.elem hf.1 h1 h2 hv)

theorem FrameGood.setLocal {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hf : FrameGood s t f) (hv : ∀ r, v = .ref r → Good s t r) :
    FrameGood s t (f.setLocal x v) := by
  refine ⟨hf.1, fun r hr => ?_⟩
  rcases List.mem_or_eq_of_mem_set hr with hr | hr
  · exact hf.2 r hr
  · simp only [Option.some.injEq] at hr
    exact hv r hr.symm

theorem StoreGood.setMem {s : Store H} {ma : Nat} {mi : MemInst} :
    StoreGood s t (s.setMem ma mi) :=
  .of_eq rfl rfl rfl rfl rfl rfl rfl

theorem VariableStep.good {c c' : Config H} (h : VariableStep c c')
    (hg : CfgGood c.store t c) : StoreGood c.store t c'.store ∧ CfgGood c.store t c' := by
  cases h with
  | localGet hl =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r hr => .inr ?_) (by simp)⟩
    simp only [codeRefs_toAdmin, codeRefs_nil, List.append_nil, Val.mem_heapRefs] at hr
    subst hr
    exact hg.2.1.2 r (List.mem_of_getElem? hl)
  | localSet hx =>
    exact ⟨.refl, hg.mk' (hg.2.1.setLocal fun r hr => hg.ref (by simp [hr])) (by simp)
      (by simp)⟩
  | localTee => exact ⟨.refl, hg.same (by simp) (by simp)⟩
  | globalGet hgl =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r hr => .inr ?_) (by simp)⟩
    simp only [codeRefs_toAdmin, codeRefs_nil, List.append_nil, Val.mem_heapRefs] at hr
    exact hg.2.1.global hgl hr
  | globalSet hgl =>
    exact ⟨.setGlobal fun r hr => hg.ref (by simp [hr]), hg.same (by simp) (by simp)⟩

theorem TableInst.grow?_refs {ti ti' : TableInst} {n : Nat} {r : Ref}
    (h : ti.grow? n r = some ti') : ti'.refs = ti.refs ++ List.replicate n r := by
  revert h
  unfold TableInst.grow?
  dsimp only
  split_ifs
  · intro h; cases h; rfl
  · intro h; cases h

theorem TableStep.good {P : Profile} {c c' : Config H} (h : TableStep P c c')
    (hg : CfgGood c.store t c) : StoreGood c.store t c'.store ∧ CfgGood c.store t c' := by
  cases h with
  | getVal ht hr =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => .inr ?_) (by simp)⟩
    simp at hr'
    subst hr'
    exact hg.2.1.table ht (List.mem_of_getElem? hr)
  | setVal ht hi =>
    refine ⟨.setTable fun r' hr' => ?_, hg.same (by simp) (by simp)⟩
    rcases List.mem_or_eq_of_mem_set hr' with hr' | rfl
    · exact .inl ⟨_, (Store.table?_spec' ht).2, hr'⟩
    · exact .inr (hg.ref (by simp))
  | growSucceed ht hgr hp =>
    refine ⟨.setTable fun r' hr' => ?_, hg.same (by simp) (by simp)⟩
    rw [TableInst.grow?_refs hgr, List.mem_append] at hr'
    rcases hr' with hr' | hr'
    · exact .inl ⟨_, (Store.table?_spec' ht).2, hr'⟩
    · rw [(List.mem_replicate.mp hr').2]
      exact .inr (hg.ref (by simp))
  | initSucc ht he hle hn hr =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => ?_) (by simp)⟩
    simp at hr'
    subst hr'
    exact .inr (hg.2.1.elem he (List.mem_of_getElem? hr))
  | elemDrop he => exact ⟨.setElemNil, hg.same (by simp) (by simp)⟩
  | _ => exact ⟨.refl, hg.same (by sub_tac) (by sub_tac)⟩

theorem MemoryStep.good {P : Profile} {c c' : Config H} (h : MemoryStep P c c')
    (hg : CfgGood c.store t c) : StoreGood c.store t c'.store ∧ CfgGood c.store t c' := by
  cases h <;> first
    | exact ⟨.refl, hg.same (by sub_tac) (by sub_tac)⟩
    | exact ⟨.setMem, hg.same (by sub_tac) (by sub_tac)⟩
    | exact ⟨.of_eq rfl rfl rfl rfl rfl rfl rfl, hg.same (by sub_tac) (by sub_tac)⟩

theorem RefStep.good {c c' : Config H} (h : RefStep c c')
    (hg : CfgGood c.store t c) : StoreGood c.store t c'.store ∧ CfgGood c.store t c' := by
  cases h with
  | refFunc hx =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => .inr ?_) (by simp)⟩
    simp at hr'
    subst hr'
    exact .func hg.2.1.1 (List.mem_of_getElem? hx)
  | refI31 i =>
    exact ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => .inr (by simp at hr'; subst hr'; exact .i31 _))
      (by simp)⟩
  | externConvertAddr hne =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => .inr ?_) (by simp)⟩
    simp at hr'
    subst hr'
    exact .extern (hg.ref (by simp))
  | anyConvertAddr r =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => .inr ?_) (by simp)⟩
    simp at hr'
    subst hr'
    exact (hg.ref (by simp)).unextern
  | refNull =>
    exact ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => .inr (by simp at hr'; subst hr'; exact .null))
      (by simp)⟩
  | _ => exact ⟨.refl, hg.same (by sub_tac) (by sub_tac)⟩

theorem mem_vals_refs {vs : List Val} {r : Ref} : r ∈ codeRefs (vals vs) ↔ Val.ref r ∈ vs := by
  simp

theorem Good.of_default {s : Store H} {v : Val} {r : Ref} {ty : CValType}
    (hv : defaultVal? ty = some v) (hr : v = .ref r) : Good s t r := by
  subst hr
  rw [defaultVal?_ref hv]
  exact .null

theorem AggregateStep.good {c c' : Config H} (h : AggregateStep c c')
    (hg : CfgGood c.store t c) : StoreGood c.store t c'.store ∧ CfgGood c.store t c' := by
  cases h with
  | structNew hd he hn =>
    refine ⟨.addStruct fun r hr => ?_, hg.mk' hg.2.1
      (fun r' hr' => .inr (by simp at hr'; subst hr'; exact .struct le_rfl)) (by simp)⟩
    simp only [List.mem_map, Prod.exists] at hr
    obtain ⟨ft, v, hmem, hp⟩ := hr
    have := packField_eq_ref hp
    subst this
    exact hg.ref (by simpa using (List.of_mem_zip hmem).2)
  | structNewDefault hd he hdef =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => .inr ?_) (by simp)⟩
    simp at hr'
    obtain ⟨ft, -, hft⟩ := mapM_some_mem hdef _ hr'
    exact Good.of_default hft rfl
  | structGetStruct hs hf =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => .inr ?_) (by simp)⟩
    simp at hr'
    have := unpackField_eq_ref hr'
    subst this
    exact (hg.ref (by simp)).structField hs (List.mem_of_getElem? hf)
  | structSetStruct hd he hi =>
    refine ⟨.setStructField fun r hr => ?_, hg.same (by simp) (by simp)⟩
    have := packField_eq_ref hr
    subst this
    exact hg.ref (by simp)
  | arrayNew v n =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => ?_) (by simp)⟩
    simp only [codeRefs_append, codeRefs_vals, List.mem_append, List.mem_flatMap,
      List.mem_replicate, Val.mem_heapRefs, codeRefs_plain, codeRefs_nil, List.not_mem_nil,
      or_false] at hr'
    obtain ⟨_, ⟨-, rfl⟩, rfl⟩ := hr'
    exact .inl (by simp)
  | arrayNewDefault hd he hv =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => ?_) (by simp)⟩
    simp only [codeRefs_append, codeRefs_vals, List.mem_append, List.mem_flatMap,
      List.mem_replicate, Val.mem_heapRefs, codeRefs_plain, codeRefs_nil, List.not_mem_nil,
      or_false] at hr'
    obtain ⟨_, ⟨-, rfl⟩, hr⟩ := hr'
    exact .inr (Good.of_default hv hr)
  | arrayNewFixed hd he hn =>
    refine ⟨.addArray fun r hr => ?_, hg.mk' hg.2.1
      (fun r' hr' => .inr (by simp at hr'; subst hr'; exact .array le_rfl)) (by simp)⟩
    simp only [List.mem_map] at hr
    obtain ⟨v, hv, hp⟩ := hr
    have := packField_eq_ref hp
    subst this
    exact hg.ref (by simpa using hv)
  | arrayNewElemAlloc he hle =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => .inr ?_) (fun fr hfr => by
      simp only [codeFrames_append, codeFrames_map_ref, codeFrames_plain, codeFrames_nil,
        List.append_nil, List.not_mem_nil] at hfr)⟩
    simp only [codeRefs_append, codeRefs_map_ref, codeRefs_plain, codeRefs_nil,
      List.append_nil] at hr'
    exact hg.2.1.elem he (List.mem_of_mem_drop (List.mem_of_mem_take hr'))
  | arrayNewDataNum hd he hdat _ _ hvs =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => ?_) (by simp)⟩
    simp at hr'
    obtain ⟨k, -, hk⟩ := mapM_some_mem hvs _ hr'
    exact absurd hk readField?_ne_ref
  | arrayGetArray ha hf =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => .inr ?_) (by simp)⟩
    simp at hr'
    have := unpackField_eq_ref hr'
    subst this
    exact (hg.ref (by simp)).arrayField ha (List.mem_of_getElem? hf)
  | arraySetArray ha hi hd he =>
    refine ⟨.setArrayField fun r hr => ?_, hg.same (by simp) (by simp)⟩
    have := packField_eq_ref hr
    subst this
    exact hg.ref (by simp)
  | arrayInitElemSucc ha he hle hn hr =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => ?_) (by simp)⟩
    simp at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inl (by simp)
    · exact .inr (hg.2.1.elem he (List.mem_of_getElem? hr))
    · exact .inl (by simp)
  | arrayInitDataNum ha hd he hdat hle hn hv =>
    refine ⟨.refl, hg.mk' hg.2.1 (fun r' hr' => ?_) (by simp)⟩
    simp at hr'
    rcases hr' with rfl | hr' | rfl
    · exact .inl (by simp)
    · subst hr'; exact absurd hv readField?_ne_ref
    · exact .inl (by simp)
  | _ => exact ⟨.refl, hg.same (by sub_tac) (by sub_tac)⟩

theorem Admin.IsReturnCallRef.code {c : Admin} (hc : c.IsReturnCallRef) (l : List Admin) :
    codeRefs (c :: l) = codeRefs l ∧ codeFrames (c :: l) = codeFrames l := by
  cases c <;> simp_all [Admin.IsReturnCallRef]

theorem Admin.IsCallRef.code {c : Admin} (hc : c.IsCallRef) (l : List Admin) :
    codeRefs (c :: l) = codeRefs l ∧ codeFrames (c :: l) = codeFrames l := by
  cases c <;> simp_all [Admin.IsCallRef]

theorem Frame.forCall_good {s : Store H} {m : ModuleInst} {vs : List Val} {ls : List ValType}
    (hm : ReachableModule s t m) (hvs : ∀ r, Val.ref r ∈ vs → Good s t r) :
    FrameGood s t (Frame.forCall m vs ls) := by
  refine ⟨hm, fun r hr => ?_⟩
  simp only [Frame.forCall, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨v, hv, hv'⟩ | ⟨ty, -, hty⟩
  · simp only [Option.some.injEq] at hv'
    subst hv'
    exact hvs r hv
  · exact Good.of_default hty rfl

/-- A host-free step from a configuration over the pre-step store `s` keeps
everything `Good`. -/
theorem Step.good {P : Profile} {c c' : Config H} (h : Step P (fun _ _ _ _ => False) c c')
    {s : Store H} (hs : c.store = s) (hg : CfgGood s t c) :
    StoreGood s t c'.store ∧ CfgGood s t c' := by
  induction h with
  | parametric h =>
    subst hs; obtain ⟨h1, h2⟩ := ParametricStep.reach h; exact ⟨.refl, hg.same h1 h2⟩
  | numeric h =>
    subst hs; obtain ⟨h1, h2⟩ := NumericStep.reach h; exact ⟨.refl, hg.same h1 h2⟩
  | vector h =>
    subst hs; obtain ⟨h1, h2⟩ := VectorStep.reach h; exact ⟨.refl, hg.same h1 h2⟩
  | «variable» h => subst hs; exact VariableStep.good h hg
  | table h => subst hs; exact TableStep.good h hg
  | memory h => subst hs; exact MemoryStep.good h hg
  | reference h => subst hs; exact RefStep.good h hg
  | aggregate h => subst hs; exact AggregateStep.good h hg
  | ctxtInstrs _ _ ih =>
    subst hs
    obtain ⟨hsg, hcg⟩ := ih rfl (hg.same (by simp; tauto) (by simp; tauto))
    refine ⟨hsg, hg.mk' hcg.2.1 (fun r hr => ?_) (fun fr hfr => ?_)⟩
    · simp only [codeRefs_append, List.mem_append] at hr ⊢
      rcases hr with (hr | hr) | hr
      · exact .inl (.inl (.inl hr))
      · exact .inr (hcg.1 r hr)
      · exact .inl (.inr hr)
    · simp only [codeFrames_append, List.mem_append] at hfr ⊢
      rcases hfr with (hr | hr) | hr
      · exact .inl (.inl (.inl hr))
      · exact .inr (hcg.2.2 fr hr)
      · exact .inl (.inr hr)
  | ctxtLabel _ ih =>
    subst hs
    obtain ⟨hsg, hcg⟩ := ih rfl (hg.same (by simp) (by simp))
    exact ⟨hsg, hg.mk' hcg.2.1 (fun r hr => .inr (hcg.1 r (by simpa using hr)))
      (fun fr hfr => .inr (hcg.2.2 fr (by simpa using hfr)))⟩
  | ctxtHandler _ ih =>
    subst hs
    obtain ⟨hsg, hcg⟩ := ih rfl (hg.same (by simp) (by simp))
    exact ⟨hsg, hg.mk' hcg.2.1 (fun r hr => .inr (hcg.1 r (by simpa using hr)))
      (fun fr hfr => .inr (hcg.2.2 fr (by simpa using hfr)))⟩
  | ctxtFrame _ ih =>
    subst hs
    obtain ⟨hsg, hcg⟩ := ih rfl (hg.mk' (hg.2.2 _ (by simp))
      (fun r hr => .inl (by simpa using hr)) (fun fr hfr => .inl (by simp [hfr])))
    refine ⟨hsg, hg.mk' hg.2.1 (fun r hr => .inr (hcg.1 r (by simpa using hr))) ?_⟩
    intro fr hfr
    simp only [codeFrames_frame, codeFrames_nil, List.append_nil, List.mem_cons] at hfr
    rcases hfr with rfl | hfr
    · exact .inr hcg.2.1
    · exact .inr (hcg.2.2 fr hfr)
  | call hx hf =>
    subst hs
    refine ⟨.refl, hg.mk' hg.2.1 (fun r hr => .inr ?_) (by simp)⟩
    simp at hr
    subst hr
    exact .func hg.2.1.1 (List.mem_of_getElem? hx)
  | returnCall hx hf =>
    subst hs
    refine ⟨.refl, hg.mk' hg.2.1 (fun r hr => .inr ?_) (by simp)⟩
    simp at hr
    subst hr
    exact .func hg.2.1.1 (List.mem_of_getElem? hx)
  | callRefFunc hc hf he hn hcode =>
    subst hs
    have h1 := fun l => (Admin.IsCallRef.code hc l).1
    refine ⟨.refl, hg.mk' hg.2.1 (fun r hr => by simp at hr) ?_⟩
    intro fr hfr
    simp only [codeFrames_frame, List.mem_cons, codeFrames_label, codeFrames_expression,
      codeFrames_nil, List.append_nil, List.not_mem_nil, or_false] at hfr
    subst hfr
    refine .inr (Frame.forCall_good ((hg.ref (by simp [h1])).funcModule hf) fun r hr => ?_)
    exact hg.ref (by simp [h1, hr])
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv => subst hs; exact ⟨.refl, hg⟩
  | returnCallRefLabel hc =>
    subst hs
    have h1 := fun l => (Admin.IsReturnCallRef.code hc l).1
    have h2 := fun l => (Admin.IsReturnCallRef.code hc l).2
    exact ⟨.refl, hg.same (by simp [h1]; tauto) (by simp [h2])⟩
  | returnCallRefHandler hc =>
    subst hs
    have h1 := fun l => (Admin.IsReturnCallRef.code hc l).1
    have h2 := fun l => (Admin.IsReturnCallRef.code hc l).2
    exact ⟨.refl, hg.same (by simp [h1]; tauto) (by simp [h2])⟩
  | returnCallRefFrameAddr hc hf he hn =>
    subst hs
    have h1 := fun l => (Admin.IsReturnCallRef.code hc l).1
    have h2 := fun l => (Admin.IsReturnCallRef.code hc l).2
    have h3 := fun m l => (Admin.retToCallIn_code m hc l).1
    have h4 := fun m l => (Admin.retToCallIn_code m hc l).2
    exact ⟨.refl, hg.same (by simp [h1, h3]; tauto) (by simp [h4])⟩
  | throw ht he hn =>
    subst hs
    refine ⟨.addExn fun r hr => hg.ref (by simp [hr]),
      hg.mk' hg.2.1 (fun r hr => .inr ?_) (by simp)⟩
    simp at hr
    subst hr
    exact .exn le_rfl
  | throwRefHandlerCatch he ht =>
    subst hs
    refine ⟨.refl, hg.mk' hg.2.1 (fun r hr => .inr ?_) (by simp)⟩
    simp at hr
    exact (hg.ref (by simp)).exnField he hr
  | throwRefHandlerCatchRef he ht =>
    subst hs
    refine ⟨.refl, hg.mk' hg.2.1 (fun r hr => ?_) (by simp)⟩
    simp at hr
    rcases hr with hr | rfl
    · exact .inr ((hg.ref (by simp)).exnField he hr)
    · exact .inl (by simp)
  | _ =>
    subst hs
    first
      | exact ⟨.refl, hg⟩
      | exact ⟨.refl, hg.same (by sub_tac) (by sub_tac)⟩

/-- The initial configuration of a thread is `Good`. -/
theorem CfgGood.init (s : Store H) (t : Thread) : CfgGood s t (t.config s) := by
  refine ⟨fun r hr => .reach (.code hr), ⟨.frame (by simp [Thread.frames]),
    fun r hr => .reach (.local (by simp [Thread.frames]) hr)⟩, fun fr hfr =>
    ⟨.frame (by simp [Thread.frames, hfr]),
      fun r hr => .reach (.local (by simp [Thread.frames, hfr]) hr)⟩⟩

section
variable {s s' : Store H} {t' : Thread}

mutual

theorem ReachableRef.good (hsg : StoreGood s t s') (hcg : CfgGood s t (t'.config s'))
    {r : Ref} : ReachableRef s' t' r → Good s t r
  | .code h => hcg.1 _ h
  | .local hf hr => by
    simp only [Thread.frames, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact hcg.2.1.2 _ hr
    · exact (hcg.2.2 _ hf).2 _ hr
  | .global hm hga hg hv => by
    rcases hsg.globals _ _ _ hg hv with ⟨gi, hg0, hv0⟩ | hgood
    · exact .reach (.global (ReachableModule.good hsg hcg hm) hga hg0 hv0)
    · exact hgood
  | .table hm hta ht hr => by
    rcases hsg.tables _ _ _ ht hr with ⟨ti, ht0, hr0⟩ | hgood
    · exact .reach (.table (ReachableModule.good hsg hcg hm) hta ht0 hr0)
    · exact hgood
  | .elem hm hea he hr => by
    obtain ⟨ei, he0, hr0⟩ := hsg.elems _ _ _ he hr
    exact .reach (.elem (ReachableModule.good hsg hcg hm) hea he0 hr0)
  | .structField ha hs hr => by
    rcases hsg.structs _ _ _ hs hr with ⟨si, hs0, hr0⟩ | hgood
    · exact (ReachableRef.good hsg hcg ha).structField hs0 hr0
    · exact hgood
  | .arrayField ha hs hr => by
    rcases hsg.arrays _ _ _ hs hr with ⟨ai, hs0, hr0⟩ | hgood
    · exact (ReachableRef.good hsg hcg ha).arrayField hs0 hr0
    · exact hgood
  | .exnField ha hs hr => by
    rcases hsg.exns _ _ _ hs hr with ⟨e, hs0, hr0⟩ | hgood
    · exact (ReachableRef.good hsg hcg ha).exnField hs0 hr0
    · exact hgood
  | .extern h => (ReachableRef.good hsg hcg h).unextern

theorem ReachableModule.good (hsg : StoreGood s t s') (hcg : CfgGood s t (t'.config s'))
    {m : ModuleInst} : ReachableModule s' t' m → ReachableModule s t m
  | .frame hf => by
    simp only [Thread.frames, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact hcg.2.1.1
    · exact (hcg.2.2 _ hf).1
  | .ref ha hf => (ReachableRef.good hsg hcg ha).funcModule (by rw [← hsg.funcs]; exact hf)
  | .func hm ha hf => .func (ReachableModule.good hsg hcg hm) ha (by rw [← hsg.funcs]; exact hf)

end

end

theorem Internal.good {o : GrowOracle} {s s' : Store H} {t t' : Thread}
    (h : Internal o (s, t) (s', t')) : StoreGood s t s' ∧ CfgGood s t (t'.config s') := by
  obtain ⟨f', code', rfl, hst⟩ := h
  exact Step.good hst (Thread.config_store s t) (CfgGood.init s t)

end StepGood

/-- Reachability is closed under internal steps: whatever the successor thread
can reach was reachable before (new heap objects only point to reachable
references), except for freshly allocated struct/array/exception addresses. -/
theorem Internal.reachableModule_mono {o : GrowOracle} {s s' : Store H} {t t' : Thread}
    {m : ModuleInst} (h : Internal o (s, t) (s', t')) (hm : ReachableModule s' t' m) :
    ReachableModule s t m := by
  obtain ⟨hsg, hcg⟩ := Internal.good h
  exact ReachableModule.good hsg hcg hm

/-- **Milestone (memory locality).** -/
theorem Internal.mem_local {o : GrowOracle} {s s' : Store H} {t t' : Thread} {a : Nat}
    (h : Internal o (s, t) (s', t')) (hna : ¬ ReachableMem s t a) : s'.mems[a]? = s.mems[a]? := by
  apply Internal.mems_active h
  simp only [Thread.activeMems, List.mem_flatMap, not_exists, not_and]
  exact fun f hf ha => hna ⟨_, .frame hf, ha⟩

theorem Internal.table_local {o : GrowOracle} {s s' : Store H} {t t' : Thread} {a : Nat}
    (h : Internal o (s, t) (s', t')) (hna : ¬ ReachableTable s t a) :
    s'.tables[a]? = s.tables[a]? := by
  apply Internal.tables_active h
  simp only [Thread.activeTables, List.mem_flatMap, not_exists, not_and]
  exact fun f hf ha => hna ⟨_, .frame hf, ha⟩

theorem Internal.global_local {o : GrowOracle} {s s' : Store H} {t t' : Thread} {a : Nat}
    (h : Internal o (s, t) (s', t')) (hna : ¬ ReachableGlobal s t a) :
    s'.globals[a]? = s.globals[a]? := by
  apply Internal.globals_active h
  simp only [Thread.activeGlobals, List.mem_flatMap, not_exists, not_and]
  exact fun f hf ha => hna ⟨_, .frame hf, ha⟩

/-! ## Multi-step locality -/

/-- Reachability closure along a run of internal steps. -/
theorem Internal.reachableModule_mono_star {o : GrowOracle} {x y : Store H × Thread}
    (h : Relation.ReflTransGen (Internal o) x y) {m : ModuleInst}
    (hm : ReachableModule y.1 y.2 m) : ReachableModule x.1 x.2 m := by
  induction h with
  | refl => exact hm
  | tail _ hst ih => exact ih (Internal.reachableModule_mono hst hm)

theorem Internal.mem_local_star {o : GrowOracle} {x y : Store H × Thread} {a : Nat}
    (h : Relation.ReflTransGen (Internal o) x y) (hna : ¬ ReachableMem x.1 x.2 a) :
    y.1.mems[a]? = x.1.mems[a]? := by
  induction h with
  | refl => rfl
  | @tail y z hxy hst ih =>
    rw [← ih]
    exact Internal.mem_local hst fun ⟨m, hm, ha⟩ =>
      hna ⟨m, Internal.reachableModule_mono_star hxy hm, ha⟩

theorem Internal.table_local_star {o : GrowOracle} {x y : Store H × Thread} {a : Nat}
    (h : Relation.ReflTransGen (Internal o) x y) (hna : ¬ ReachableTable x.1 x.2 a) :
    y.1.tables[a]? = x.1.tables[a]? := by
  induction h with
  | refl => rfl
  | @tail y z hxy hst ih =>
    rw [← ih]
    exact Internal.table_local hst fun ⟨m, hm, ha⟩ =>
      hna ⟨m, Internal.reachableModule_mono_star hxy hm, ha⟩

theorem Internal.global_local_star {o : GrowOracle} {x y : Store H × Thread} {a : Nat}
    (h : Relation.ReflTransGen (Internal o) x y) (hna : ¬ ReachableGlobal x.1 x.2 a) :
    y.1.globals[a]? = x.1.globals[a]? := by
  induction h with
  | refl => rfl
  | @tail y z hxy hst ih =>
    rw [← ih]
    exact Internal.global_local hst fun ⟨m, hm, ha⟩ =>
      hna ⟨m, Internal.reachableModule_mono_star hxy hm, ha⟩

/-- Function instances are never modified, only appended (no typing needed). -/
theorem Internal.funcs_prefix {o : GrowOracle} {s s' : Store H} {t t' : Thread}
    (h : Internal o (s, t) (s', t')) : s'.funcs = s.funcs :=
  (Internal.framesLocal h).1

theorem hostArity?_congr {s s' : Store H} (h : s'.funcs = s.funcs) :
    hostArity? s' = hostArity? s := by
  funext a
  simp only [hostArity?, h]

/-- `decompose?` depends on the store only through its functions. -/
theorem decompose?_congr {s s' : Store H} (h : s'.funcs = s.funcs) (code : List Admin) :
    decompose? s' code = decompose? s code := by
  induction code using decompose?.induct (s := s)
  all_goals (rw [decompose?, decompose?]; split <;> simp_all [hostArity?_congr h])
  all_goals (obtain ⟨-, rfl, -⟩ := ‹_ ∧ _ ∧ _›; simp_all)

theorem Thread.config_code_congr {s s' : Store H} (h : s'.funcs = s.funcs) (t : Thread) :
    (t.config s').code = (t.config s).code := by
  cases t <;> simp [Thread.config, Execution.Core.invoke, h]

/-- A parked thread's callout is preserved by any other thread's internal step. -/
theorem Internal.preserves_callout {o : GrowOracle} {s s' : Store H} {t t' u : Thread}
    {hc : H} {args : List Val} (h : Internal o (s, t) (s', t'))
    (hu : status o s u = .callout hc args) : status o s' u = .callout hc args := by
  have hf := Internal.funcs_prefix h
  have hc := Thread.config_code_congr hf u
  have hd := decompose?_congr hf (u.config s).code
  unfold status at hu ⊢
  dsimp only at hu ⊢
  rw [hc, hd]
  split_ifs at hu ⊢ <;> revert hu <;>
    rcases decompose? s (Thread.config s u).code with _ | ⟨_, _, _, _⟩ <;> simp

end Silmaril.Wasm.SingleThreaded
