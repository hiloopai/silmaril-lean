module

public import Silmaril.Wasm.Component.Reference.Engine.Lime1.Defs
public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Runtime.Host.Defs
public import Silmaril.Wasm.Execution.Memory
import Silmaril.Wasm.Component.Reference.Wasm.Lime1.Execution.Callout.Progress.Defs

/-!
# The Lime1 core engine: laws and bridges

Properties of `lime1` (`Engine/Lime1.lean`):

* `Grows s s'`: the store relation that internal steps, host allocation, memory writes and
  preparation establish (functions are kept, tables and memories only grow, with the same
  maximum), and `Grows.extends`: it implies the engine-level `CoreEngine.Extends`. The callout
  field of `Extends` holds because a callout found by `decompose?` stays located in any store
  that keeps the existing functions (`status_callout_of_funcs`).
* `lawful : CoreEngine.Lawful lime1`.
* `HostStep host`: the component-level interleaving of `lime1` internal steps and callouts, each
  answered by the host relation (`host h s args (.returned s' r)`) and then resumed.
  `steps_bridge`: its finite runs are exactly the runs of `Lime1.Execution.Steps host` (from the
  `step_iff`, `Answer.iff` and `decompose?_complete`); `diverges_bridge`: an infinite
  `Lime1.Execution.Step host` trace is an infinite `HostStep` trace or reaches a callout whose
  host answer diverges (the machine's `invokeHostDiverges` self-loop), and conversely.
* `instantiation_bridge`: `Lime1.Execution.Instantiation host before m imports after inst outcome`
  holds iff the module is valid, the imports match, `lime1.prepare?` succeeds with instance `inst`,
  and the start thread (if any) runs by `HostStep host` to the outcome (no start: the prepared
  store with no values). The start code runs under the frame `⟨[], inst⟩` in `Lime1.Execution`
  and under the empty frame in the engine (`lime1.invoke`); `steps_reframe` shows that code
  made of values, traps, invocations and frames does not observe the outer frame.
* `instantiationDiverges_bridge`: `Lime1.Execution.InstantiationDiverges host before m imports`
  holds iff the module is valid, the imports match, `lime1.prepare?` returns a start function
  `a`, and the machine diverges from the start thread `lime1.invoke a []` (by
  `diverges_bridge`: an infinite `HostStep` trace or a run to a diverging host answer);
  `diverges_reframe` is the frame irrelevance of infinite traces.
* Tests: the inline adder module (`local.get 0; local.get 1; i32.add`) runs to `[x + y]` with
  `lime1Exec` (kernel `rfl`, for all `x y`, no memory); a function calling a host import pauses
  with status `callout` and the right arguments, and resumes to its result (kernel `rfl`).

Not claimed: `ResumeLawful lime1` (false for ill-typed host results), determinism of internal
steps (NaN results and `memory.grow` failure are nondeterministic), and any import typing of
`prepare?` (import matching is the separate `ImportsMatch` premise).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Lime1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Semantics (MemoryView WasmSemantics)

/-! ## Store growth -/

theorem extendsList_append_right {α : Type} {R : α → α → Prop} (hr : ∀ a, R a a)
    (xs ys : List α) : ExtendsList R xs (xs ++ ys) where
  length := by simp
  entry i x hx := ⟨x, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1, hx],
    hr x⟩

theorem extendsList_set_right {α : Type} {R : α → α → Prop} (hr : ∀ a, R a a)
    {xs : List α} {i : Nat} {y : α} (hy : ∀ x, xs[i]? = some x → R x y) :
    ExtendsList R xs (xs.set i y) where
  length := by simp
  entry j x hx := by
    by_cases e : i = j
    · subst e
      exact ⟨y, List.getElem?_set_self (List.getElem?_eq_some_iff.1 hx).1, hy x hx⟩
    · exact ⟨x, by rw [List.getElem?_set_ne e, hx], hr x⟩

theorem extendsList_modify_right {α : Type} {R : α → α → Prop} (hr : ∀ a, R a a)
    {f : α → α} (hf : ∀ a, R a (f a)) (xs : List α) (i : Nat) :
    ExtendsList R xs (xs.modify i f) where
  length := by simp
  entry j x hx := by
    rw [List.getElem?_modify, hx]
    by_cases e : i = j
    · exact ⟨f x, by simp [e], hf x⟩
    · exact ⟨x, by simp [e], hr x⟩

/-- What the engine operations do to a Lime1 store: the existing functions are kept, tables and
memories keep their maximum and may only grow. -/
structure Grows {H : Type} (s s' : Wasm.Lime1.Execution.Store H) : Prop where
  funcs : ExtendsList Eq s.funcs s'.funcs
  tables : ExtendsList TableExtends s.tables s'.tables
  memories : ExtendsList MemoryExtends s.memories s'.memories

private theorem tableExtends_refl (t : TableInst) : TableExtends t t := ⟨rfl, Nat.le_refl _⟩

private theorem memoryExtends_refl (m : MemInst) : MemoryExtends m m := ⟨rfl, Nat.le_refl _⟩

theorem Grows.refl {H : Type} (s : Wasm.Lime1.Execution.Store H) : Grows s s :=
  ⟨.refl (fun _ => rfl) _, .refl tableExtends_refl _, .refl memoryExtends_refl _⟩

theorem Grows.trans {H : Type} {s₁ s₂ s₃ : Wasm.Lime1.Execution.Store H}
    (h₁ : Grows s₁ s₂)
    (h₂ : Grows s₂ s₃) : Grows s₁ s₃ where
  funcs := h₁.funcs.trans (R := Eq) (fun _ _ _ e e' => e.trans e') h₂.funcs
  tables := h₁.tables.trans
    (fun _ _ _ ⟨hm, hl⟩ ⟨hm', hl'⟩ => ⟨hm.trans hm', hl.trans hl'⟩)
    h₂.tables
  memories := h₁.memories.trans
    (fun _ _ _ ⟨hm, hl⟩ ⟨hm', hl'⟩ => ⟨hm.trans hm', hl.trans hl'⟩)
    h₂.memories

/-- Replacing an existing memory by one with the same maximum and at least its size. -/
theorem grows_setMemory {H : Type} {s : Wasm.Lime1.Execution.Store H} {a : MemAddr}
    {m m' : MemInst} (hm : s.memories[a.value]? = some m) (hmax : m.max = m'.max)
    (hsize : m.data.size ≤ m'.data.size) : Grows s (Wasm.Lime1.Execution.setMemory s a m') where
  funcs := .refl (fun _ => rfl) _
  tables := .refl tableExtends_refl _
  memories := extendsList_set_right memoryExtends_refl fun x hx => by
    rw [hm] at hx
    cases hx
    exact ⟨hmax, hsize⟩

theorem frameMemory_found {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (h : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) :
    s.memories[a.value]? = some m := by
  simp only [Wasm.Lime1.Execution.frameMemory, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a', -, m', hm', rfl, rfl⟩ := h
  exact hm'

theorem storeInt_size {t : IntType} {packed : Option Wasm.Lime1.PackSize}
    {data bytes : Memory.Bytes}
    {start : Nat} {x : BitVec t.width}
    (h : Wasm.Lime1.Execution.storeInt t packed data start x = some bytes) :
    bytes.size = data.size :=
  Memory.writeBytes_size _ _ _ _ h

theorem storeFloat_size {t : FloatType} {data bytes : Memory.Bytes} {start : Nat}
    {x : BitVec t.width} (h : Wasm.Lime1.Execution.storeFloat t data start x = some bytes) :
    bytes.size = data.size :=
  Memory.writeBytes_size _ _ _ _ h

theorem grow_size_le {data bytes : Memory.Bytes} {max : Option Nat} {delta : Nat} {r : BitVec 32}
    (h : Memory.Grow data max delta bytes r) : data.size ≤ bytes.size := by
  cases h with
  | success after h => rw [Memory.grow_size _ _ _ _ h]; omega
  | failure => exact Nat.le_refl _

/-- Host-free steps grow the store. -/
theorem internal_grows {H : Type} {a b : Wasm.Lime1.Execution.Config H}
    (h : Wasm.Lime1.Execution.Internal a b) : Grows a.store b.store := by
  induction h with
  | context _ _ _ ih => exact ih
  | label _ _ _ ih => exact ih
  | frame _ _ _ ih => exact ih
  | globalSet s => exact ⟨.refl (fun _ => rfl) s.funcs, .refl tableExtends_refl s.tables,
      .refl memoryExtends_refl s.memories⟩
  | intStore _ _ _ _ _ _ _ _ _ _ memory stored =>
    exact grows_setMemory (frameMemory_found memory) rfl (storeInt_size stored).ge
  | floatStore _ _ _ _ _ _ _ _ _ memory stored =>
    exact grows_setMemory (frameMemory_found memory) rfl (storeFloat_size stored).ge
  | memoryGrow _ _ _ _ _ _ _ memory grown =>
    exact grows_setMemory (frameMemory_found memory) rfl (grow_size_le grown)
  | memoryCopy _ _ _ _ _ _ _ _ memory copied =>
    exact grows_setMemory (frameMemory_found memory) rfl (Memory.copy_size _ _ _ _ _ copied).ge
  | memoryFill _ _ _ _ _ _ _ _ memory filled =>
    exact grows_setMemory (frameMemory_found memory) rfl (Memory.fill_size _ _ _ _ _ filled).ge
  | invokeHost _ _ _ _ _ _ _ _ _ _ hb => exact hb.elim
  | invokeHostDiverges _ _ _ _ _ _ _ _ hb => exact hb.elim
  | _ => exact .refl _

/-! ## Status -/

/-- Final code has no callout. -/
theorem decompose?_of_terminal {H : Type} {cfg : Wasm.Lime1.Execution.Config H} {r : Result}
    (h : Wasm.Lime1.Execution.terminal? cfg.code = some r) :
    Wasm.Lime1.Execution.decompose? cfg = none := by
  obtain ⟨s, f, code⟩ := cfg
  have hc : code = Wasm.Lime1.Execution.result r := Wasm.Lime1.Execution.terminal?_sound h
  subst hc
  cases r with
  | values vs =>
    simp only [Wasm.Lime1.Execution.decompose?, Wasm.Lime1.Execution.result,
      Wasm.Lime1.Execution.decomposeFrom?_values]
  | trap =>
    simp only [Wasm.Lime1.Execution.decompose?, Wasm.Lime1.Execution.result,
      Wasm.Lime1.Execution.decomposeFrom?_trap_cons]

/-- Final code takes no executable step. -/
theorem step?_result {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame) (r : Result) :
    Wasm.Lime1.Execution.step? ⟨s, f, Wasm.Lime1.Execution.result r⟩ = none := by
  cases r with
  | values vs =>
    have e := Wasm.Lime1.Execution.stepFrom?_values_append s f [] vs []
    rw [List.append_nil] at e
    simp only [Wasm.Lime1.Execution.step?, Wasm.Lime1.Execution.result, e]
    rfl
  | trap => rfl

theorem status_eq_callout {H : Type} {s : Wasm.Lime1.Execution.Store H} {t : Thread H} {h : H}
    {args : List FlatValue} :
    status s t = .callout h args ↔ ∃ c, Wasm.Lime1.Execution.decompose? (toConfig (s, t)) =
      some c ∧ c.host = h ∧ c.args = args := by
  unfold status
  cases ht : Wasm.Lime1.Execution.terminal? t.code with
  | some r =>
    have hd := decompose?_of_terminal (cfg := toConfig (s, t)) ht
    simp [hd]
  | none =>
    cases hd : Wasm.Lime1.Execution.decompose? (toConfig (s, t)) with
    | some c => simp
    | none => simp only [reduceCtorEq, false_and, exists_false, iff_false]; split <;> simp

theorem status_eq_returned {H : Type} {s : Wasm.Lime1.Execution.Store H} {t : Thread H}
    {r : CallResult} (h : status s t = .returned r) :
    Wasm.Lime1.Execution.terminal? t.code = some (toResult r) := by
  unfold status at h
  split at h
  · next r' e =>
    cases h
    simpa using e
  · split at h
    · cases h
    · split at h <;> cases h

theorem status_eq_stuck {H : Type} {s : Wasm.Lime1.Execution.Store H} {t : Thread H}
    (h : status s t = .stuck) : Wasm.Lime1.Execution.step? (toConfig (s, t)) = none := by
  unfold status at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · next e => simpa using e

/-- A callout stays a callout in every store that keeps the existing functions. -/
theorem status_callout_of_funcs {H : Type} {s s' : Wasm.Lime1.Execution.Store H}
    (hf : ExtendsList Eq s.funcs s'.funcs) {t : Thread H} {h : H} {args : List FlatValue}
    (hs : status s t = .callout h args) : status s' t = .callout h args := by
  obtain ⟨c, hc, rfl, rfl⟩ := status_eq_callout.mp hs
  obtain ⟨plugged, found, arity⟩ := Wasm.Lime1.Execution.decompose?_sound hc
  obtain ⟨y, hy, rfl⟩ := hf.entry _ _ found
  have hc' : Wasm.Lime1.Execution.CalloutAt (toConfig (s', t)) c := ⟨plugged, hy, arity⟩
  obtain ⟨c', hd, -, -, hh, ha, -⟩ := Wasm.Lime1.Execution.decompose?_complete hc'
  exact status_eq_callout.mpr ⟨c', hd, hh, ha⟩

/-- Store growth keeps the type of every function. -/
theorem Grows.funcType {H : Type} {s s' : Wasm.Lime1.Execution.Store H} (h : Grows s s') :
    ∀ a ft, lime1.funcType? s a = some ft → lime1.funcType? s' a = some ft := by
  intro a ft e
  change (s.funcs[a.value]?).map FuncInst.type = some ft at e
  change (s'.funcs[a.value]?).map FuncInst.type = some ft
  obtain ⟨fn, hfn, rfl⟩ := Option.map_eq_some_iff.mp e
  obtain ⟨y, hy, rfl⟩ := h.funcs.entry _ _ hfn
  simp [hy]

/-- Store growth is engine-level store extension. -/
theorem Grows.extends {H : Type} {s s' : Wasm.Lime1.Execution.Store H} (h : Grows s s') :
    lime1.Extends s s' where
  funcType := h.funcType
  memAddrType m at_ e := by
    change (s.memories[m.value]?).map (fun _ => AddrType.i32) = some at_ at e
    change (s'.memories[m.value]?).map (fun _ => AddrType.i32) = some at_
    obtain ⟨mi, hmi, rfl⟩ := Option.map_eq_some_iff.mp e
    obtain ⟨y, hy, -⟩ := h.memories.entry _ _ hmi
    simp [hy]
  memSize m n e := by
    change (s.memories[m.value]?).map (fun mi => mi.data.size) = some n at e
    change ∃ n', (s'.memories[m.value]?).map (fun mi => mi.data.size) = some n' ∧ n ≤ n'
    obtain ⟨mi, hmi, rfl⟩ := Option.map_eq_some_iff.mp e
    obtain ⟨y, hy, -, hle⟩ := h.memories.entry _ _ hmi
    exact ⟨y.data.size, by simp [hy], hle⟩
  tableAddrType t at_ e := by
    change (s.tables[t.value]?).map (fun _ => AddrType.i32) = some at_ at e
    change (s'.tables[t.value]?).map (fun _ => AddrType.i32) = some at_
    obtain ⟨ti, hti, rfl⟩ := Option.map_eq_some_iff.mp e
    obtain ⟨y, hy, -⟩ := h.tables.entry _ _ hti
    simp [hy]
  callout _ _ _ e := status_callout_of_funcs h.funcs e

/-! ## Preparation, allocation and memory writes grow the store -/

theorem allocate?_grows {H : Type} {s a : Wasm.Lime1.Execution.Store H} {m : Wasm.Lime1.Module}
    {imports : List ExternVal} {mod : ModuleInst}
    (h : Wasm.Lime1.Execution.allocate? s m imports = some (a, mod)) : Grows s a := by
  simp only [Wasm.Lime1.Execution.allocate?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, -, _, -, _, -, rfl, -⟩ := h
  exact ⟨extendsList_append_right (fun _ => rfl) _ _,
    extendsList_append_right tableExtends_refl _ _,
    extendsList_append_right memoryExtends_refl _ _⟩

theorem applyElem_grows {H : Type} (s : Wasm.Lime1.Execution.Store H)
    (w : Wasm.Lime1.Execution.ElemWrite) : Grows s (Wasm.Lime1.Execution.applyElem s w) where
  funcs := .refl (fun _ => rfl) _
  tables := by
    unfold Wasm.Lime1.Execution.applyElem
    exact extendsList_modify_right (f := fun table : TableInst => {table with
      refs := table.refs.take w.offset ++ w.values.map some ++
        table.refs.drop (w.offset + w.values.length)}) tableExtends_refl (fun t => ⟨rfl, by
      simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
      omega⟩) _ _
  memories := .refl memoryExtends_refl _

theorem copySlice_size_ge (bytes data : ByteArray) (offset : Nat) :
    data.size ≤ (bytes.copySlice 0 data offset bytes.size).size := by
  rw [ByteArray.copySlice_eq_append]
  simp only [ByteArray.size_append, ByteArray.size_extract]
  have : bytes.data.size = bytes.size := rfl
  have : data.data.size = data.size := rfl
  omega

theorem applyData_grows {H : Type} (s : Wasm.Lime1.Execution.Store H)
    (w : Wasm.Lime1.Execution.DataWrite) : Grows s (Wasm.Lime1.Execution.applyData s w) where
  funcs := .refl (fun _ => rfl) _
  tables := .refl tableExtends_refl _
  memories := by
    unfold Wasm.Lime1.Execution.applyData
    exact extendsList_modify_right (f := fun memory : MemInst => {memory with
      data := w.bytes.copySlice 0 memory.data w.offset w.bytes.size}) memoryExtends_refl
      (fun m => ⟨rfl, copySlice_size_ge _ _ _⟩) _ _

theorem foldl_grows {H : Type} {α : Type} (g : Wasm.Lime1.Execution.Store H → α →
    Wasm.Lime1.Execution.Store H) (hg : ∀ s w, Grows s (g s w)) (ws : List α)
    (s : Wasm.Lime1.Execution.Store H) : Grows s (ws.foldl g s) := by
  induction ws generalizing s with
  | nil => exact .refl s
  | cons w ws ih => exact (hg s w).trans (ih _)

theorem prepare?_grows {H : Type} {s : Wasm.Lime1.Execution.Store H} {m : Wasm.Lime1.Module}
    {imports : List ExternVal} {p : Wasm.Lime1.Execution.Prepared H}
    (h : Wasm.Lime1.Execution.prepare? s m imports = some p) : Grows s p.store := by
  simp only [Wasm.Lime1.Execution.prepare?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def] at h
  obtain ⟨⟨a, mod⟩, ha, _, -, _, -, h⟩ := h
  split at h <;>
  · obtain ⟨_, -, e⟩ := Option.bind_eq_some_iff.mp h
    rw [← Option.some.inj e]
    exact (allocate?_grows ha).trans ((foldl_grows _ applyElem_grows _ _).trans
      (foldl_grows _ applyData_grows _ _))

theorem memWrite?_eq_some {H : Type} {s s' : Wasm.Lime1.Execution.Store H} {m : MemAddr}
    {st : Nat} {bs : ByteArray} (h : memWrite? s m st bs = some s') :
    ∃ mi d, s.memories[m.value]? = some mi ∧ Memory.writeBytes mi.data st bs = some d ∧
      s' = Wasm.Lime1.Execution.setMemory s m {mi with data := d} := by
  simp only [memWrite?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨mi, hmi, d, hd, rfl⟩ := h
  exact ⟨mi, d, hmi, hd, rfl⟩

theorem memWrite?_grows {H : Type} {s s' : Wasm.Lime1.Execution.Store H} {m : MemAddr}
    {st : Nat} {bs : ByteArray} (h : memWrite? s m st bs = some s') : Grows s s' := by
  obtain ⟨mi, d, hmi, hd, rfl⟩ := memWrite?_eq_some h
  exact grows_setMemory hmi rfl (Memory.writeBytes_size _ _ _ _ hd).ge

/-! ## Lawfulness -/

/-- The Lime1 memory view is coherent: `setMemory` is a `List.set` on `Store.memories`, and
`{mi with data := d}` replaces the buffer and keeps the (constant) address type. These four
facts discharge eight of the nine `CoreEngine.Lawful` memory laws, generically. -/
instance memoryView_lawful : memoryView.Lawful where
  inst?_setInst_self {_ _ _ _ _} hmi :=
    List.getElem?_set_self (List.getElem?_eq_some_iff.1 hmi).1
  inst?_setInst_ne {_ _ m _ m'} e := by
    refine List.getElem?_set_ne fun e' => e ?_
    cases m; cases m'
    subst e'
    rfl
  data_withData _ _ := rfl
  addrType_withData _ _ := rfl

/-- The Lime1 semantics is lawful. All twenty-three `CoreEngine.Lawful` fields follow
(`lawful`, below). -/
instance semanticsLawful : WasmSemantics.Lawful lime1Semantics where
  flatType?_ofFlatType _ := rfl
  internal_running {H s t c'} step := by
    cases hs : status s t with
    | running => exact hs
    | returned r =>
      have e := Wasm.Lime1.Execution.terminal?_sound (status_eq_returned hs)
      have hp := Wasm.Lime1.Execution.step?_progress step
      change (Wasm.Lime1.Execution.step? ⟨s, t.frame, t.code⟩).isSome at hp
      rw [e, step?_result] at hp
      exact absurd hp (by simp)
    | callout h args =>
      obtain ⟨c, hc, -⟩ := status_eq_callout.mp hs
      exact absurd step (Wasm.Lime1.Execution.decompose?_sound hc).not_internal
    | stuck =>
      have hp := Wasm.Lime1.Execution.step?_progress step
      rw [status_eq_stuck hs] at hp
      exact absurd hp (by simp)
  externSub_refl := CoreExternType.Sub.refl
  externSub_trans := CoreExternType.Sub.trans
  asFunc?_ofFunc _ := rfl
  internal_extends h := (internal_grows h).extends
  prepare_extends {H s s' m imps i st} h := by
    change ((Wasm.Lime1.Execution.prepare? s m imps).map fun p =>
      (p.store, p.module, startAddr? p.start)) = some (s', i, st) at h
    obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.mp h
    cases e
    exact (prepare?_grows hp).extends
  allocHost_extends {H s s' ft h a} e := by
    cases e
    exact Grows.extends ⟨extendsList_append_right (fun _ => rfl) _ _,
      .refl tableExtends_refl _, .refl memoryExtends_refl _⟩
  allocHost_fresh {H s s' ft h a} e := by
    cases e
    change (s.funcs[s.funcs.length]?).map FuncInst.type = none
    simp
  allocHost_frame {H s s' ft h a b} e hb := by
    cases e
    change ((s.funcs ++ [.host ft h])[b.value]?).map FuncInst.type =
      (s.funcs[b.value]?).map FuncInst.type
    have hb' : b.value ≠ s.funcs.length := fun e => hb (by cases b; simp_all)
    rw [List.getElem?_append]
    split
    · rfl
    · rename_i hlt
      have : b.value - s.funcs.length ≠ 0 := by omega
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hlt), this]
  allocHost_funcType {H s s' ft h a} e := by
    cases e
    change ((s.funcs ++ [.host ft h])[s.funcs.length]?).map FuncInst.type = some ft
    simp [FuncInst.type]
  allocHost_callout {H s s' ft h a args} e hl := by
    cases e
    apply status_eq_callout.mpr
    refine ⟨⟨.seq [] .hole [], ⟨s.funcs.length⟩, ft, h, args⟩, ?_, rfl, rfl⟩
    simp only [Wasm.Lime1.Execution.decompose?, toConfig, invoke,
      Wasm.Lime1.Execution.decomposeFrom?_values_append, List.nil_append,
      Wasm.Lime1.Execution.decomposeFrom?_invoke_cons, decomposeHead?]
    simp [hl]
  memView := memoryView_lawful
  memWrite_extends h := (memWrite?_grows h).extends

/-- The Lime1 engine is lawful: every field comes from `semanticsLawful` through the single
`WasmSemantics` adapter. -/
instance lawful : CoreEngine.Lawful lime1 := WasmSemantics.toCoreEngine_lawful lime1Semantics

/-! ## Component-level runs with a host relation -/

/-- One component-level step of a `lime1` configuration under a host relation: an internal step,
or a callout answered by the host (`host h s args (.returned s' r)`) and resumed in the host's
store. Diverging host answers are not steps (see `diverges_bridge`). -/
inductive HostStep {H : Type} (host : Wasm.Lime1.Execution.HostSemantics H) :
    lime1.Config H → lime1.Config H → Prop where
  | internal {c c' : lime1.Config H} (h : lime1.Internal c c') : HostStep host c c'
  | answer {s : Wasm.Lime1.Execution.Store H} {t : Thread H} {h : H} {args : List FlatValue}
      {s' : Wasm.Lime1.Execution.Store H} {r : Result} (hc : lime1.status s t = .callout h args)
      (hr : host h s args (.returned s' r)) :
      HostStep host (s, t) (s', lime1.resume s t (ofResult r))

/-- Finite component-level runs. -/
abbrev HostSteps {H : Type} (host : Wasm.Lime1.Execution.HostSemantics H) :
    lime1.Config H → lime1.Config H → Prop :=
  Relation.ReflTransGen (HostStep host)

/-! ## Code that does not observe the outer frame -/

/-- Administrative instructions that may occur at the top of a start activation: values,
traps, invocations and frames (never a bare source instruction or label). -/
def topAdmin : Wasm.Lime1.Execution.Admin → Bool
  | .source i => (Wasm.Lime1.Execution.asValue? (.source i)).isSome
  | .invoke _ => true
  | .label _ _ _ => false
  | .frame _ _ _ => true
  | .trap => true

/-- Code built from `topAdmin` instructions. -/
def TopCode (code : List Wasm.Lime1.Execution.Admin) : Prop := ∀ x ∈ code, topAdmin x = true

@[simp] theorem topAdmin_value (v : Value) : topAdmin (Wasm.Lime1.Execution.value v) = true := by
  rcases v with ⟨(t | t), b⟩ <;> rfl

/-! ## Instantiation -/

/-- The start run of a prepared instance: no start function leaves the prepared store and no
values; a start function `a` runs `lime1.invoke a []` by `HostStep host` to the outcome. -/
def StartRun {H : Type} (host : Wasm.Lime1.Execution.HostSemantics H)
    (s : Wasm.Lime1.Execution.Store H) : Option FuncAddr → Wasm.Lime1.Execution.Store H →
    Result → Prop
  | none, after, outcome => after = s ∧ outcome = .values []
  | some a, after, outcome => ∃ t : Thread H,
      HostSteps host (s, lime1.invoke a []) (after, t) ∧
        t.code = Wasm.Lime1.Execution.result outcome

/-! ## Tests -/

namespace Examples

open Wasm.Lime1.Execution (values)

/-- `(func (param i32 i32) (result i32))`. -/
def binaryType : V1.FuncType := ⟨[.i32, .i32], [.i32]⟩

/-- `local.get 0; local.get 1; i32.add`. -/
def adderCode : Wasm.Lime1.Func :=
  ⟨⟨0⟩, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 .add]⟩

/-- The inline adder module, exporting its function as `"add"`; no memory. -/
def adderModule : Wasm.Lime1.Module where
  types := [binaryType]
  funcs := [adderCode]
  exports := [⟨"add", .func ⟨0⟩⟩]

def adderInst : ModuleInst where
  types := [binaryType]
  funcs := [⟨0⟩]
  exports := [⟨"add", .func ⟨0⟩⟩]

def adderStore : Wasm.Lime1.Execution.Store String where
  funcs := [.wasm binaryType adderInst adderCode]

/-- `(func (param i32) (result i32))`. -/
def unaryType : V1.FuncType := ⟨[.i32], [.i32]⟩

/-- `(import "env" "f" (func (param i32) (result i32)))` and an exported function
`local.get 0; call 0`. -/
def callerModule : Wasm.Lime1.Module where
  types := [unaryType]
  imports := [⟨"env", "f", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨0⟩]⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

def callerInst : ModuleInst where
  types := [unaryType]
  funcs := [⟨0⟩, ⟨1⟩]
  exports := [⟨"run", .func ⟨1⟩⟩]

def callerStore : Wasm.Lime1.Execution.Store String where
  funcs := [.host unaryType "f",
    .wasm unaryType callerInst ⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨0⟩]⟩]

/-- The configuration reached by running the exported function on `x`. -/
def parked (x : BitVec 32) : lime1.Config String :=
  lime1Exec.runCore 8 (callerStore, lime1.invoke ⟨1⟩ [.int .i32 x]) |>.1

end Examples

end Silmaril.Wasm.Component.Engine.Lime1
