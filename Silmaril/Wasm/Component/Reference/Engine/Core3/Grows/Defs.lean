module

public import Silmaril.Wasm.SingleThreaded.Exec.Driver
public import Silmaril.Wasm.SingleThreaded.Exec.Status
public import Silmaril.Wasm.SingleThreaded.Interface

@[expose] public section

/-!
# Untyped store growth of the Core 3.0 machine

`Grows s s'` is the part of store extension that the component runtime observes
(`CoreEngine.Extends`, Engine/Laws.lean), stated for the concrete Core 3.0 store
`Execution.Core.Store` without any typing:

* the function instances of `s` are a prefix of those of `s'`;
* every memory of `s` still exists in `s'`, with the same address type and at least as many
  bytes (`memory.grow` only appends pages, stores keep the size);
* every table of `s` still exists in `s'`, with the same address type.

Unlike `Execution.Core.Extend` (the typed store extension of the soundness proof), `Grows`
needs no `StoreOk`: every reduction rule of the host-free machine grows the store
(`Step.grows`, one lemma per family; `Step.grows_of_host` for host relations that grow the
store), and so do runs (`Steps.grows`), head steps (`Head.grows`) and internal steps of the
single-threaded machine (`Internal.grows`). Allocation grows the store (`Grows.of_prefix`), and
so does typed extension (`Grows.of_extend`).

Callout statuses persist under `Grows`: `decompose?` reads the store only through
`hostArity?`, which is stable under function prefixes (`decompose?_prefix`); the code of a
thread is stable once its callee is allocated (`Thread.config_code_prefix`), and a thread
with a host-call redex has its callee allocated (`Thread.loaded_of_decompose?`). Hence
`statusC_callout_grows`, for any step function. The fields of `CoreEngine.Extends` over the
raw store functions are `Grows.funcType`, `Grows.memAddrType`, `Grows.memSize`,
`Grows.tableAddrType` and `Grows.status_callout_of` (for any status built from `statusC`
that is a callout only on `statusC` callouts).
-/

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ## The relation -/

/-- Untyped store growth: functions are a prefix, memories keep their address type and do not
shrink, tables keep their address type. -/
structure Grows (s s' : Store H) : Prop where
  funcs : s.funcs <+: s'.funcs
  mems : ∀ (a : Nat) (mi : MemInst), s.mems[a]? = some mi →
    ∃ mi' : MemInst, s'.mems[a]? = some mi' ∧
      mi'.type.address = mi.type.address ∧ mi.bytes.size ≤ mi'.bytes.size
  tables : ∀ (a : Nat) (ti : TableInst), s.tables[a]? = some ti →
    ∃ ti' : TableInst, s'.tables[a]? = some ti' ∧ ti'.type.address = ti.type.address

theorem Grows.refl (s : Store H) : Grows s s :=
  ⟨List.prefix_refl _, fun _ mi h => ⟨mi, h, rfl, Nat.le_refl _⟩, fun _ ti h => ⟨ti, h, rfl⟩⟩

theorem Grows.trans {s₁ s₂ s₃ : Store H} (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) :
    Grows s₁ s₃ where
  funcs := h₁.funcs.trans h₂.funcs
  mems a mi h := by
    obtain ⟨mi₂, e₂, a₂, b₂⟩ := h₁.mems a mi h
    obtain ⟨mi₃, e₃, a₃, b₃⟩ := h₂.mems a mi₂ e₂
    exact ⟨mi₃, e₃, a₃.trans a₂, Nat.le_trans b₂ b₃⟩
  tables a ti h := by
    obtain ⟨ti₂, e₂, a₂⟩ := h₁.tables a ti h
    obtain ⟨ti₃, e₃, a₃⟩ := h₂.tables a ti₂ e₂
    exact ⟨ti₃, e₃, a₃.trans a₂⟩

/-! ## Store accessors and growth of single instances -/

/-! ## Reduction families -/

section Variable

end Variable

section Table

end Table

section Memory

end Memory

section Reference

end Reference

section Aggregate

end Aggregate

/-! ## Steps, head steps, runs and internal steps -/

/-! ## Callouts persist -/

/-- The callee of a pending thread is allocated; active threads carry their own code. -/
def Thread.Loaded (s : Store H) : Thread → Prop
  | .pending a _ => a < s.funcs.length
  | .active _ _ => True

/-! ## What `CoreEngine.Extends` needs, over the raw store functions -/

end Silmaril.Wasm.Component.Engine.Core3

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
variable {H : Type}

theorem getElem?_of_prefix {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : Nat} {x : α}
    (he : l₁[i]? = some x) : l₂[i]? = some x := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp he).1]
  exact he

/-- A store with the same functions, memories and tables. -/
theorem Grows.of_eq {s s' : Store H} (hf : s'.funcs = s.funcs) (hm : s'.mems = s.mems)
    (ht : s'.tables = s.tables) : Grows s s' :=
  ⟨hf ▸ List.prefix_refl _, fun _ mi h => ⟨mi, hm ▸ h, rfl, Nat.le_refl _⟩,
    fun _ ti h => ⟨ti, ht ▸ h, rfl⟩⟩

/-- Allocation: functions, memories and tables are prefixes. -/
theorem Grows.of_prefix {s s' : Store H} (hf : s.funcs <+: s'.funcs) (hm : s.mems <+: s'.mems)
    (ht : s.tables <+: s'.tables) : Grows s s' :=
  ⟨hf, fun _ mi h => ⟨mi, getElem?_of_prefix hm h, rfl, Nat.le_refl _⟩,
    fun _ ti h => ⟨ti, getElem?_of_prefix ht h, rfl⟩⟩

theorem Grows.setMem {s : Store H} {ma : Nat} {mi mi' : MemInst} (hm : s.mems[ma]? = some mi)
    (ha : mi'.type.address = mi.type.address) (hb : mi.bytes.size ≤ mi'.bytes.size) :
    Grows s (s.setMem ma mi') := by
  refine ⟨List.prefix_refl _, fun a mi₀ h => ?_, fun _ ti h => ⟨ti, h, rfl⟩⟩
  by_cases e : ma = a
  · subst e
    rw [hm] at h
    cases h
    have hlt := (List.getElem?_eq_some_iff.mp hm).1
    exact ⟨mi', by simp [Store.setMem, hlt], ha, hb⟩
  · exact ⟨mi₀, by simp [Store.setMem, List.getElem?_set_ne e, h], rfl, Nat.le_refl _⟩

theorem Grows.setTable {s : Store H} {ta : Nat} {ti ti' : TableInst}
    (ht : s.tables[ta]? = some ti) (ha : ti'.type.address = ti.type.address) :
    Grows s (s.setTable ta ti') := by
  refine ⟨List.prefix_refl _, fun _ mi h => ⟨mi, h, rfl, Nat.le_refl _⟩, fun a ti₀ h => ?_⟩
  by_cases e : ta = a
  · subst e
    rw [ht] at h
    cases h
    have hlt := (List.getElem?_eq_some_iff.mp ht).1
    exact ⟨ti', by simp [Store.setTable, hlt], ha⟩
  · exact ⟨ti₀, by simp [Store.setTable, List.getElem?_set_ne e, h], rfl⟩

theorem Grows.setGlobal (s : Store H) (a : Nat) (v : Val) : Grows s (s.setGlobal a v) :=
  .of_eq rfl rfl rfl

theorem Grows.setElem (s : Store H) (a : Nat) (refs : List Ref) : Grows s (s.setElem a refs) :=
  .of_eq rfl rfl rfl

theorem Grows.setData (s : Store H) (a : Nat) (bytes : ByteArray) :
    Grows s (s.setData a bytes) := .of_eq rfl rfl rfl

theorem Grows.addExn (s : Store H) (e : ExnInst) : Grows s (s.addExn e) := .of_eq rfl rfl rfl

theorem mem?_some {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst}
    (h : s.mem? f x = some (ma, mi)) : s.mems[ma]? = some mi := by
  unfold Store.mem? at h
  cases ha : f.module.mems[x.toNat]? with
  | none => simp [ha] at h
  | some b =>
    cases hb : s.mems[b]? with
    | none => simp [ha, hb] at h
    | some c =>
      simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hb

theorem table?_some {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
    (h : s.table? f x = some (ta, ti)) : s.tables[ta]? = some ti := by
  unfold Store.table? at h
  cases ha : f.module.tables[x.toNat]? with
  | none => simp [ha] at h
  | some b =>
    cases hb : s.tables[b]? with
    | none => simp [ha, hb] at h
    | some c =>
      simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hb

/-- A successful store keeps the byte size. -/
theorem memoryStore_size {m b : ByteArray} {start count : Nat} {w : BitVec (8 * count)}
    (h : Silmaril.Wasm.Execution.Memory.store m start w = some b) : b.size = m.size :=
  Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ h

/-- `$growmem` keeps the address type and does not shrink. -/
theorem memInst_grow?_grows {mi mi' : MemInst} {n : Nat} (h : mi.grow? n = some mi') :
    mi'.type.address = mi.type.address ∧ mi.bytes.size ≤ mi'.bytes.size := by
  unfold MemInst.grow? at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨rfl, by simp [ByteArray.size_append]⟩
  · cases h

/-- `$growtable` keeps the address type. -/
theorem tableInst_grow?_address {ti ti' : TableInst} {n : Nat} {r : Ref}
    (h : ti.grow? n r = some ti') : ti'.type.address = ti.type.address := by
  unfold TableInst.grow? at h
  dsimp only at h
  split at h
  · cases h
    rfl
  · cases h

section Variable

theorem VariableStep.grows {c c' : Config H} (h : VariableStep c c') :
    Grows c.store c'.store := by
  cases h with
  | globalSet => exact Grows.setGlobal _ _ _
  | _ => exact Grows.refl _

end Variable

section Table

theorem TableStep.grows {P : Numerics.Profile} {c c' : Config H} (h : TableStep P c c') :
    Grows c.store c'.store := by
  cases h with
  | setVal ht => exact Grows.setTable (table?_some ht) rfl
  | growSucceed ht hg => exact Grows.setTable (table?_some ht) (tableInst_grow?_address hg)
  | elemDrop => exact Grows.setElem _ _ _
  | _ => exact Grows.refl _

end Table

section Memory

theorem MemoryStep.grows {P : Numerics.Profile} {c c' : Config H} (h : MemoryStep P c c') :
    Grows c.store c'.store := by
  cases h with
  | storeIntVal hm hs => exact Grows.setMem (mem?_some hm) rfl (memoryStore_size hs).ge
  | storePackVal hm hs => exact Grows.setMem (mem?_some hm) rfl (memoryStore_size hs).ge
  | storeFloatVal hm hs => exact Grows.setMem (mem?_some hm) rfl (memoryStore_size hs).ge
  | vecStoreVal hm hs => exact Grows.setMem (mem?_some hm) rfl (memoryStore_size hs).ge
  | vecStoreLaneVal hm hs => exact Grows.setMem (mem?_some hm) rfl (memoryStore_size hs).ge
  | growSucceed hm hg =>
    exact Grows.setMem (mem?_some hm) (memInst_grow?_grows hg).1 (memInst_grow?_grows hg).2
  | dataDrop => exact Grows.setData _ _ _
  | _ => exact Grows.refl _

end Memory

section Reference

theorem RefStep.grows {c c' : Config H} (h : RefStep c c') : Grows c.store c'.store := by
  cases h <;> exact Grows.refl _

end Reference

section Aggregate

theorem AggregateStep.grows {c c' : Config H} (h : AggregateStep c c') :
    Grows c.store c'.store := by
  cases h <;> exact Grows.of_eq rfl rfl rfl

end Aggregate

/-- Every reduction step grows the store when the host calls do (no typing needed). -/
theorem Step.grows_of_host {P : Numerics.Profile} {host : HostSemantics H}
    (hhost : ∀ h s vs s' r, host h s vs (.returned s' r) → Grows s s') {c c' : Config H}
    (h : Step P host c c') : Grows c.store c'.store := by
  induction h with
  | «variable» h => exact VariableStep.grows h
  | table h => exact TableStep.grows h
  | memory h => exact MemoryStep.grows h
  | reference h => exact RefStep.grows h
  | aggregate h => exact AggregateStep.grows h
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | ctxtFrame _ ih => exact ih
  | callRefHost _ _ _ _ _ hh => exact hhost _ _ _ _ _ hh
  | throw => exact Grows.addExn _ _
  | _ => exact Grows.refl _

/-- Every host-free reduction step grows the store (no typing needed). -/
theorem Step.grows {P : Numerics.Profile} {c c' : Config H} (h : Step P noHost c c') :
    Grows c.store c'.store :=
  Step.grows_of_host (fun _ _ _ _ _ hh => False.elim hh) h

/-- Head steps of the decomposition toolkit grow the store. -/
theorem Head.grows {P : Numerics.Profile} {s : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c : Config H} (h : Head P s f args e c) : Grows s c.store :=
  Step.grows h.toStep

theorem Steps.grows_of_host {P : Numerics.Profile} {host : HostSemantics H}
    (hhost : ∀ h s vs s' r, host h s vs (.returned s' r) → Grows s s') {c c' : Config H}
    (h : Steps P host c c') : Grows c.store c'.store := by
  induction h with
  | refl => exact Grows.refl _
  | tail _ step ih => exact ih.trans (Step.grows_of_host hhost step)

theorem Steps.grows {P : Numerics.Profile} {c c' : Config H} (h : Steps P noHost c c') :
    Grows c.store c'.store :=
  Steps.grows_of_host (fun _ _ _ _ _ hh => False.elim hh) h

theorem hostArity?_prefix {s s' : Store H} (h : s.funcs <+: s'.funcs) {a : Nat} {p : H × Nat}
    (hh : hostArity? s a = some p) : hostArity? s' a = some p := by
  unfold hostArity? at hh ⊢
  cases e : s.funcs[a]? with
  | none => rw [e] at hh; cases hh
  | some fi =>
    rw [e] at hh
    rw [getElem?_of_prefix h e]
    exact hh

theorem topRedex_prefix {s s' : Store H} (h : s.funcs <+: s'.funcs) {vs : List Val}
    {rest : List Admin} {x : Ctx × Nat × H × List Val} (ht : topRedex s vs rest = some x) :
    topRedex s' vs rest = some x := by
  unfold topRedex at ht ⊢
  split at ht
  · split at ht
    · rename_i hc n hh
      rw [hostArity?_prefix h hh]
      exact ht
    · cases ht
  · cases ht

/-- A lookup that a larger store keeps survives `Option.map`. -/
theorem map_eq_some_of_imp {α β : Type} {f : α → β} {o o' : Option α} {x : β}
    (hi : ∀ y, o = some y → o' = some y) (h : o.map f = some x) : o'.map f = some x := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
  exact Option.map_eq_some_iff.mpr ⟨y, hi y hy, rfl⟩

/-- A host-call redex found in a store is found in every store with more functions. -/
theorem decompose?_prefix {s s' : Store H} (h : s.funcs <+: s'.funcs) {code : List Admin}
    {x : Ctx × Nat × H × List Val} (hd : decompose? s code = some x) :
    decompose? s' code = some x := by
  rcases hsp : splitVals code with ⟨vs, _ | ⟨d, rest⟩⟩
  · have hn : decompose? s code = none := decompose?_of_split_nil hsp
    exact absurd (hn.symm.trans hd) (by simp)
  have hsz : sizeOf (d :: rest) ≤ sizeOf code := by
    simpa only [hsp] using splitVals_snd_sizeOf code
  have hh : decompHead s vs d rest = some x := (decompose?_of_split hsp).symm.trans hd
  rw [decompose?_of_split hsp]
  cases d with
  | label n cont body =>
    have : sizeOf body < sizeOf code := by
      simp only [List.cons.sizeOf_spec, Admin.label.sizeOf_spec] at hsz; omega
    exact map_eq_some_of_imp (fun _ hy => decompose?_prefix h hy) hh
  | handler n cs body =>
    have : sizeOf body < sizeOf code := by
      simp only [List.cons.sizeOf_spec, Admin.handler.sizeOf_spec] at hsz; omega
    exact map_eq_some_of_imp (fun _ hy => decompose?_prefix h hy) hh
  | frame n f body =>
    have : sizeOf body < sizeOf code := by
      simp only [List.cons.sizeOf_spec, Admin.frame.sizeOf_spec] at hsz; omega
    exact map_eq_some_of_imp (fun _ hy => decompose?_prefix h hy) hh
  | _ =>
    simp only [decompHead] at hh ⊢
    split_ifs at hh ⊢
    exact topRedex_prefix h hh
termination_by sizeOf code

/-- A thread at a host-call redex has its callee allocated. -/
theorem Thread.loaded_of_decompose? {s : Store H} {t : Thread} {x : Ctx × Nat × H × List Val}
    (h : decompose? s (t.config s).code = some x) : Thread.Loaded s t := by
  cases t with
  | active => trivial
  | pending a args =>
    simp only [Thread.Loaded]
    simp only [Thread.config, Execution.Core.invoke] at h
    have e : vals args ++ [Admin.ref (.func a),
        .callRefType ((s.funcs[a]?.map FuncInst.type).getD default)] =
        vals (args ++ [.ref (.func a)]) ++
          [.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)] := by
      simp only [vals_append, List.append_assoc]
      rfl
    rw [e, decompose?_of_split (SingleThreaded.splitVals_vals_cons rfl []),
      decompHead_of_IsCallRef (d := .callRefType _) trivial] at h
    obtain ⟨a', hc, n, hl, hh⟩ := topRedex_some h
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq, Val.ref.injEq, Ref.func.injEq] at hl
    subst hl
    obtain ⟨fi, -, -, hf, -⟩ := hostArity?_eq_some hh
    exact (List.getElem?_eq_some_iff.mp hf).1

/-- The code of a loaded thread does not depend on functions allocated later. -/
theorem Thread.config_code_prefix {s s' : Store H} (h : s.funcs <+: s'.funcs) {t : Thread}
    (ht : Thread.Loaded s t) : (t.config s').code = (t.config s).code := by
  cases t with
  | active => rfl
  | pending a args =>
    simp only [Thread.Loaded] at ht
    have hfi : s.funcs[a]? = some s.funcs[a] := List.getElem?_eq_getElem ht
    simp only [Thread.config, Execution.Core.invoke, hfi, getElem?_of_prefix h hfi]

theorem decompose?_of_statusC_callout {stepC : Config H → Option (Config H)} {s : Store H}
    {t : Thread} {hc : H} {args : List Val} (h : statusC stepC s t = .callout hc args) :
    ∃ E a, decompose? s (t.config s).code = some (E, a, hc, args) := by
  unfold statusC at h
  dsimp only at h
  split_ifs at h <;> revert h <;>
    rcases decompose? s (t.config s).code with _ | ⟨E, a, h', args'⟩ <;> simp

/-- A callout status persists in every store with more functions, for any step functions. -/
theorem statusC_callout_prefix {stepC stepC' : Config H → Option (Config H)} {s s' : Store H}
    (hg : s.funcs <+: s'.funcs) {t : Thread} {hc : H} {args : List Val}
    (h : statusC stepC s t = .callout hc args) : statusC stepC' s' t = .callout hc args := by
  obtain ⟨E, a, hd⟩ := decompose?_of_statusC_callout h
  have hc := Thread.config_code_prefix hg (Thread.loaded_of_decompose? hd)
  have hd' := decompose?_prefix hg hd
  unfold statusC at h ⊢
  dsimp only at h ⊢
  rw [hc, hd']
  rw [hd] at h
  dsimp only at h ⊢
  exact h

theorem statusC_callout_grows {stepC stepC' : Config H → Option (Config H)} {s s' : Store H}
    (hg : Grows s s') {t : Thread} {hc : H} {args : List Val}
    (h : statusC stepC s t = .callout hc args) : statusC stepC' s' t = .callout hc args :=
  statusC_callout_prefix hg.funcs h

theorem Grows.funcType {s s' : Store H} (hg : Grows s s') {a : Nat} {d : Validation.DefType}
    (h : s.funcs[a]?.map FuncInst.type = some d) : s'.funcs[a]?.map FuncInst.type = some d := by
  cases e : s.funcs[a]? with
  | none => rw [e] at h; cases h
  | some fi =>
    rw [e] at h
    rw [getElem?_of_prefix hg.funcs e]
    exact h

theorem Grows.memAddrType {s s' : Store H} (hg : Grows s s') {m : Nat} {at_ : AddrType}
    (h : memAddrType? s m = some at_) : memAddrType? s' m = some at_ := by
  unfold memAddrType? at h ⊢
  cases e : s.mems[m]? with
  | none => rw [e] at h; cases h
  | some mi =>
    obtain ⟨mi', e', ha, -⟩ := hg.mems m mi e
    rw [e] at h
    rw [e', Option.map_some, ha]
    exact h

theorem Grows.memSize {s s' : Store H} (hg : Grows s s') {m n : Nat}
    (h : memSize? s m = some n) : ∃ n', memSize? s' m = some n' ∧ n ≤ n' := by
  unfold memSize? at h ⊢
  cases e : s.mems[m]? with
  | none => rw [e] at h; cases h
  | some mi =>
    obtain ⟨mi', e', -, hb⟩ := hg.mems m mi e
    rw [e, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨mi'.bytes.size, by rw [e', Option.map_some], hb⟩

theorem Grows.tableAddrType {s s' : Store H} (hg : Grows s s') {t : Nat} {at_ : AddrType}
    (h : tableAddrType? s t = some at_) : tableAddrType? s' t = some at_ := by
  unfold tableAddrType? at h ⊢
  cases e : s.tables[t]? with
  | none => rw [e] at h; cases h
  | some ti =>
    obtain ⟨ti', e', ha⟩ := hg.tables t ti e
    rw [e] at h
    rw [e', Option.map_some, ha]
    exact h

/-- The callout field of `CoreEngine.Extends` for a status `F ∘ statusC stepC` whose value `b`
is reached only from `statusC` callouts (e.g. a flat wrapper mapping non-flat callouts to
`stuck`). -/
theorem Grows.status_callout_of {β : Type} {stepC stepC' : Config H → Option (Config H)}
    {s s' : Store H} (hg : Grows s s') (F : Silmaril.Wasm.SingleThreaded.Status H → β) {b : β}
    (hF : ∀ st, F st = b → ∃ hc args, st = .callout hc args) {t : Thread}
    (h : F (statusC stepC s t) = b) : F (statusC stepC' s' t) = b := by
  obtain ⟨hc, args, e⟩ := hF _ h
  rw [statusC_callout_grows (stepC' := stepC') hg e, ← e]
  exact h

end Silmaril.Wasm.Component.Engine.Core3
