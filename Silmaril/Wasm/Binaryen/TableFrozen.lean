module

public import Silmaril.Wasm.Binaryen.GlobReadRel

@[expose] public section

/-! # Frozen tables: a table that no reachable code can write

A table address `ta` is *frozen* in a configuration when no code that can run writes
it: every Wasm function of the store, and every instruction of the configuration's
code (each under the module of its own frame), writes only table indices that its
module does not map to `ta`. The writing instructions are `table.set`, `table.fill`,
`table.copy` (destination), `table.init` and `table.grow`.

`Step.frozen` shows that every step keeps the configuration frozen and leaves the
table at `ta` unchanged, provided the host keeps it too (`HostKeeps`; the closed host
never returns, `closedHost_keeps`). `Steps.frozen` lifts this to runs. This is the
store invariant of Directize (`Pass/Directize.lean`): a slot of a frozen table holds,
along every run, the reference it held when the invariant started. Any pass that reads
a table at compile time (for example a `call_indirect` inliner) needs the same fact.
-/

namespace Silmaril.Wasm.Binaryen

namespace TableFrozen

open Execution.Core Numerics Validation

variable {H : Type}

/-! ## Instructions that keep a table -/

mutual
/-- Every table index the instruction may write satisfies `W`. -/
def InstrK (W : Nat → Prop) : Instr → Prop
  | .tableSet x | .tableFill x | .tableGrow x => W x.toNat
  | .tableCopy x _ | .tableInit x _ => W x.toNat
  | .block _ b | .loop _ b | .tryTable _ _ b => InstrsK W b
  | .if_ _ b₁ b₂ => InstrsK W b₁ ∧ InstrsK W b₂
  | _ => True
/-- `InstrK` on a sequence. -/
def InstrsK (W : Nat → Prop) : List Instr → Prop
  | [] => True
  | i :: is => InstrK W i ∧ InstrsK W is
end

/-- The table indices that module `mi` does not map to address `ta`. -/
def W (ta : Nat) (mi : ModuleInst) (x : Nat) : Prop := mi.tables[x]? ≠ some ta

@[simp] theorem InstrsK_nil (W : Nat → Prop) : InstrsK W [] ↔ True := by simp [InstrsK]

@[simp] theorem InstrsK_cons (W : Nat → Prop) (i : Instr) (is : List Instr) :
    InstrsK W (i :: is) ↔ InstrK W i ∧ InstrsK W is := by simp [InstrsK]

@[simp] theorem InstrsK_append (W : Nat → Prop) :
    ∀ l₁ l₂ : List Instr, InstrsK W (l₁ ++ l₂) ↔ InstrsK W l₁ ∧ InstrsK W l₂
  | [], _ => by simp
  | a :: l₁, l₂ => by simp [InstrsK_append W l₁ l₂, and_assoc]

/-! ## Administrative code that keeps a table -/

mutual
/-- Every instruction of the administrative instruction, under module `mi` (or the
module of an inner frame), writes only table indices that do not resolve to `ta`. -/
def AdmK (ta : Nat) (mi : ModuleInst) : Admin → Prop
  | .plain i => InstrK (W ta mi) i
  | .label _ cont body => InstrsK (W ta mi) cont ∧ AdmsK ta mi body
  | .handler _ _ body => AdmsK ta mi body
  | .frame _ fr body => AdmsK ta fr.module body
  | _ => True
/-- `AdmK` on a sequence. -/
def AdmsK (ta : Nat) (mi : ModuleInst) : List Admin → Prop
  | [] => True
  | a :: as => AdmK ta mi a ∧ AdmsK ta mi as
end

@[simp] theorem AdmsK_nil (ta : Nat) (mi : ModuleInst) : AdmsK ta mi [] ↔ True := by
  simp [AdmsK]

@[simp] theorem AdmsK_cons (ta : Nat) (mi : ModuleInst) (a : Admin) (as : List Admin) :
    AdmsK ta mi (a :: as) ↔ AdmK ta mi a ∧ AdmsK ta mi as := by simp [AdmsK]

@[simp] theorem AdmK_plain (ta : Nat) (mi : ModuleInst) (i : Instr) :
    AdmK ta mi (.plain i) ↔ InstrK (W ta mi) i := by simp [AdmK]

@[simp] theorem AdmK_label (ta : Nat) (mi : ModuleInst) (n : Nat) (cont : List Instr)
    (body : List Admin) :
    AdmK ta mi (.label n cont body) ↔ InstrsK (W ta mi) cont ∧ AdmsK ta mi body := by
  simp [AdmK]

@[simp] theorem AdmK_handler (ta : Nat) (mi : ModuleInst) (n : Nat) (cs : List Catch)
    (body : List Admin) : AdmK ta mi (.handler n cs body) ↔ AdmsK ta mi body := by
  simp [AdmK]

@[simp] theorem AdmK_frame (ta : Nat) (mi : ModuleInst) (n : Nat) (fr : Frame)
    (body : List Admin) : AdmK ta mi (.frame n fr body) ↔ AdmsK ta fr.module body := by
  simp [AdmK]

@[simp] theorem AdmK_ref (ta : Nat) (mi : ModuleInst) (r : Ref) : AdmK ta mi (.ref r) := by
  simp [AdmK]

@[simp] theorem AdmK_callRefType (ta : Nat) (mi : ModuleInst) (d : DefType) :
    AdmK ta mi (.callRefType d) := by simp [AdmK]

@[simp] theorem AdmK_returnCallRefType (ta : Nat) (mi : ModuleInst) (d : DefType) :
    AdmK ta mi (.returnCallRefType d) := by simp [AdmK]

@[simp] theorem AdmK_trap (ta : Nat) (mi : ModuleInst) : AdmK ta mi .trap := by simp [AdmK]

@[simp] theorem AdmsK_append (ta : Nat) (mi : ModuleInst) :
    ∀ l₁ l₂ : List Admin, AdmsK ta mi (l₁ ++ l₂) ↔ AdmsK ta mi l₁ ∧ AdmsK ta mi l₂
  | [], _ => by simp
  | a :: l₁, l₂ => by simp [AdmsK_append ta mi l₁ l₂, and_assoc]

@[simp] theorem AdmK_val (ta : Nat) (mi : ModuleInst) (v : Val) : AdmK ta mi v.toAdmin := by
  rcases v with ⟨⟨t | t, b⟩⟩ | b | r <;> simp [Val.toAdmin, InstrK]

@[simp] theorem AdmK_constI32 (ta : Nat) (mi : ModuleInst) (c : BitVec 32) :
    AdmK ta mi (constI32 c) := AdmK_val ta mi _

@[simp] theorem AdmsK_vals (ta : Nat) (mi : ModuleInst) : ∀ vs : List Val, AdmsK ta mi (vals vs)
  | [] => by simp [vals]
  | v :: vs => by simpa [vals] using AdmsK_vals ta mi vs

@[simp] theorem AdmsK_expression (ta : Nat) (mi : ModuleInst) :
    ∀ is : List Instr, AdmsK ta mi (expression is) ↔ InstrsK (W ta mi) is
  | [] => by simp [expression]
  | i :: is => by
    have ih := AdmsK_expression ta mi is
    simp only [expression, List.map_cons, AdmsK_cons, AdmK_plain, InstrsK_cons] at ih ⊢
    rw [ih]

theorem AdmsK_of_mem {ta : Nat} {mi : ModuleInst} :
    ∀ {l : List Admin}, (∀ a ∈ l, AdmK ta mi a) → AdmsK ta mi l
  | [], _ => by simp
  | a :: l, h => (AdmsK_cons ..).mpr ⟨h a (by simp), AdmsK_of_mem fun b hb => h b (by simp [hb])⟩

theorem AdmsK_refs_slice (ta : Nat) (mi : ModuleInst) (rs : List Ref) (i n : Nat) :
    AdmsK ta mi (((rs.map Admin.ref).drop i).take n) :=
  AdmsK_of_mem fun a ha => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop (List.mem_of_mem_take ha))
    simp

theorem AdmsK_result (ta : Nat) (mi : ModuleInst) (r : Result) : AdmsK ta mi r.toAdmin := by
  cases r <;> simp [Result.toAdmin, InstrK]

/-! ## Stores and configurations -/

/-- Every Wasm function of the store keeps table `ta` under its own module. -/
def StoreK (ta : Nat) (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, ∀ code : Func, fi.code = .wasm code → InstrsK (W ta fi.module) code.body

/-- **Table `ta` is frozen in configuration `c`**: no code of the store or of `c`
writes it. -/
structure Frozen (ta : Nat) (c : Config H) : Prop where
  store : StoreK ta c.store
  code : AdmsK ta c.frame.module c.code

/-- A host keeps table `ta` frozen when a returning host call keeps the store's code
frozen and leaves the table at `ta` unchanged. -/
def HostKeeps (ta : Nat) (host : HostSemantics H) : Prop :=
  ∀ h s vs s' r, host h s vs (.returned s' r) → StoreK ta s →
    StoreK ta s' ∧ s'.tables[ta]? = s.tables[ta]?

theorem closedHost_keeps (ta : Nat) : HostKeeps ta (closedHost (H := H)) :=
  fun _ _ _ _ _ h => h.elim

/-! ## Steps keep a frozen table -/

section steps

variable {P : Profile} {host : HostSemantics H}

theorem tableStep_frozen {ta : Nat} {c c' : Config H} (h : TableStep P c c')
    (hc : AdmsK ta c.frame.module c.code) :
    c'.store.funcs = c.store.funcs ∧ c'.store.tables[ta]? = c.store.tables[ta]? ∧
      c'.frame = c.frame ∧ AdmsK ta c'.frame.module c'.code := by
  have keep : ∀ {s : Store H} {f : Frame} {x : TableIdx} {ta' : Nat} {ti ti' : TableInst},
      s.table? f x = some (ta', ti) → W ta f.module x.toNat →
        (s.setTable ta' ti').tables[ta]? = s.tables[ta]? := by
    intro s f x ta' ti ti' ht hw
    simp only [Store.table?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨a, hx, ti₀, -, rfl, -⟩ := ht
    have hne : a ≠ ta := fun e => hw (e ▸ hx)
    simp [Store.setTable, List.getElem?_set_ne hne]
  cases h with
  | setVal ht _ => exact ⟨rfl, keep ht (by simp_all [InstrK]), rfl, by simp⟩
  | growSucceed ht _ _ => exact ⟨rfl, keep ht (by simp_all [InstrK]), rfl, by simp [InstrK]⟩
  | _ => exact ⟨rfl, rfl, rfl, by simp_all [InstrK]⟩

theorem memoryStep_frozen {ta : Nat} {c c' : Config H} (h : MemoryStep P c c') :
    c'.store.funcs = c.store.funcs ∧ c'.store.tables = c.store.tables ∧
      c'.frame = c.frame ∧ AdmsK ta c'.frame.module c'.code := by
  cases h <;> exact ⟨rfl, rfl, rfl, by simp [InstrK, store8, load8u]⟩

theorem aggregateStep_frozen {ta : Nat} {c c' : Config H} (h : AggregateStep c c') :
    c'.store.funcs = c.store.funcs ∧ c'.store.tables = c.store.tables ∧
      c'.frame = c.frame ∧ AdmsK ta c'.frame.module c'.code := by
  cases h <;> exact ⟨rfl, rfl, rfl, by simp [InstrK, AdmsK_refs_slice]⟩

theorem refStep_frozen {ta : Nat} {c c' : Config H} (h : RefStep c c') :
    c'.store = c.store ∧ c'.frame = c.frame ∧ AdmsK ta c'.frame.module c'.code := by
  cases h <;> exact ⟨rfl, rfl, by simp⟩

theorem variableStep_frozen {ta : Nat} {c c' : Config H} (h : VariableStep c c') :
    c'.store.funcs = c.store.funcs ∧ c'.store.tables = c.store.tables ∧
      c'.frame.module = c.frame.module ∧ AdmsK ta c'.frame.module c'.code := by
  cases h <;> exact ⟨rfl, rfl, rfl, by simp [InstrK]⟩

theorem parametricStep_frozen {ta : Nat} {mi : ModuleInst} {is is' : List Admin}
    (h : ParametricStep is is') : AdmsK ta mi is' := by
  cases h <;> simp

theorem numericStep_frozen {ta : Nat} {mi : ModuleInst} {is is' : List Admin}
    (h : NumericStep P is is') : AdmsK ta mi is' := by
  cases h <;> simp [InstrK]

theorem vectorStep_frozen {ta : Nat} {mi : ModuleInst} {is is' : List Admin}
    (h : VectorStep P is is') : AdmsK ta mi is' := by
  cases h <;> simp [InstrK]

theorem StoreK.of_funcs {ta : Nat} {s s' : Store H} (e : s'.funcs = s.funcs) (h : StoreK ta s) :
    StoreK ta s' := by
  intro fi hfi
  exact h fi (e ▸ hfi)

theorem AdmK_isCallRef {ta : Nat} {mi : ModuleInst} {c : Admin} (h : c.IsCallRef) :
    AdmK ta mi c := by
  rcases isCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> simp [InstrK]

theorem AdmK_isReturnCallRef {ta : Nat} {mi : ModuleInst} {c : Admin} (h : c.IsReturnCallRef) :
    AdmK ta mi c := by
  rcases isReturnCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> simp [InstrK]

theorem AdmK_retToCallIn {ta : Nat} {mi : ModuleInst} {c : Admin} (h : c.IsReturnCallRef)
    (m : ModuleInst) : AdmK ta mi (c.retToCallIn m) := by
  rcases retToCallIn_cases h m with ⟨y, e⟩ | ⟨d, e⟩ <;> rw [e] <;> simp [InstrK]

/-- **A step keeps a frozen table frozen and unchanged.** -/
theorem Step.frozen {ta : Nat} (hh : HostKeeps ta host) {c c' : Config H}
    (h : Step P host c c') :
    Frozen ta c → Frozen ta c' ∧ c'.store.tables[ta]? = c.store.tables[ta]? := by
  induction h with
  | parametric h => intro hf; exact ⟨⟨hf.store, parametricStep_frozen h⟩, rfl⟩
  | numeric h => intro hf; exact ⟨⟨hf.store, numericStep_frozen h⟩, rfl⟩
  | vector h => intro hf; exact ⟨⟨hf.store, vectorStep_frozen h⟩, rfl⟩
  | «variable» h =>
    intro hf
    obtain ⟨e₁, e₂, -, hc⟩ := variableStep_frozen (ta := ta) h
    exact ⟨⟨hf.store.of_funcs e₁, hc⟩, by rw [e₂]⟩
  | table h =>
    intro hf
    obtain ⟨e₁, e₂, -, hc⟩ := tableStep_frozen h hf.code
    exact ⟨⟨hf.store.of_funcs e₁, hc⟩, e₂⟩
  | memory h =>
    intro hf
    obtain ⟨e₁, e₂, -, hc⟩ := memoryStep_frozen (ta := ta) h
    exact ⟨⟨hf.store.of_funcs e₁, hc⟩, by rw [e₂]⟩
  | reference h =>
    intro hf
    obtain ⟨e₁, -, hc⟩ := refStep_frozen (ta := ta) h
    exact ⟨⟨hf.store.of_funcs (by rw [e₁]), hc⟩, by rw [e₁]⟩
  | aggregate h =>
    intro hf
    obtain ⟨e₁, e₂, -, hc⟩ := aggregateStep_frozen (ta := ta) h
    exact ⟨⟨hf.store.of_funcs e₁, hc⟩, by rw [e₂]⟩
  | ctxtInstrs h _ ih =>
    intro hf
    have hm := GlobRead.step_frame_module h
    have hc := hf.code
    simp only [AdmsK_append, AdmsK_vals, true_and] at hc
    obtain ⟨⟨hs, hc'⟩, e⟩ := ih ⟨hf.store, hc.1⟩
    refine ⟨⟨hs, ?_⟩, e⟩
    simp only at hm hc' ⊢
    simp only [AdmsK_append, AdmsK_vals, true_and, hm]
    exact ⟨by simpa [hm] using hc', hc.2⟩
  | ctxtLabel h ih =>
    intro hf
    have hm := GlobRead.step_frame_module h
    have hc := hf.code
    simp only [AdmsK_cons, AdmsK_nil, and_true, AdmK_label] at hc
    obtain ⟨⟨hs, hc'⟩, e⟩ := ih ⟨hf.store, hc.2⟩
    refine ⟨⟨hs, ?_⟩, e⟩
    simp only at hm hc' ⊢
    simp only [AdmsK_cons, AdmsK_nil, and_true, AdmK_label, hm] at hc' ⊢
    exact ⟨hc.1, hc'⟩
  | ctxtHandler h ih =>
    intro hf
    have hm := GlobRead.step_frame_module h
    have hc := hf.code
    simp only [AdmsK_cons, AdmsK_nil, and_true, AdmK_handler] at hc
    obtain ⟨⟨hs, hc'⟩, e⟩ := ih ⟨hf.store, hc⟩
    refine ⟨⟨hs, ?_⟩, e⟩
    simp only at hm hc' ⊢
    simpa [hm] using hc'
  | ctxtFrame h ih =>
    intro hf
    have hc := hf.code
    simp only [AdmsK_cons, AdmsK_nil, and_true, AdmK_frame] at hc
    obtain ⟨⟨hs, hc'⟩, e⟩ := ih ⟨hf.store, hc⟩
    exact ⟨⟨hs, by simpa using hc'⟩, e⟩
  | callRefFunc _ hfa _ _ hcode =>
    intro hf
    refine ⟨⟨hf.store, ?_⟩, rfl⟩
    have := hf.store _ (List.mem_of_getElem? hfa) _ hcode
    simpa [Frame.forCall] using this
  | callRefHost _ hfa _ _ _ hhost =>
    intro hf
    obtain ⟨hs, e⟩ := hh _ _ _ _ _ hhost hf.store
    exact ⟨⟨hs, AdmsK_result ..⟩, e⟩
  | returnCallRefLabel hc =>
    intro hf; exact ⟨⟨hf.store, by simp [AdmK_isReturnCallRef hc]⟩, rfl⟩
  | returnCallRefHandler hc =>
    intro hf; exact ⟨⟨hf.store, by simp [AdmK_isReturnCallRef hc]⟩, rfl⟩
  | returnCallRefFrameAddr hc =>
    intro hf; exact ⟨⟨hf.store, by simp [AdmK_retToCallIn hc]⟩, rfl⟩
  | _ =>
    intro hf
    refine ⟨⟨hf.store, ?_⟩, rfl⟩
    have := hf.code
    simp_all [InstrK]

/-- **A run keeps a frozen table frozen and unchanged.** -/
theorem Steps.frozen {ta : Nat} (hh : HostKeeps ta host) {c c' : Config H}
    (h : Steps P host c c') (hf : Frozen ta c) :
    Frozen ta c' ∧ c'.store.tables[ta]? = c.store.tables[ta]? := by
  induction h with
  | refl => exact ⟨hf, rfl⟩
  | tail _ hs ih =>
    obtain ⟨hf', e⟩ := ih
    obtain ⟨hf'', e'⟩ := Step.frozen hh hs hf'
    exact ⟨hf'', e'.trans e⟩

end steps

end TableFrozen

end Silmaril.Wasm.Binaryen
