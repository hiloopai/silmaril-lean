module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Execution
public import Silmaril.Wasm.Execution.Core.Instantiation

@[expose] public section

/-! # Lime1 instantiation is simulated by Core 3.0 instantiation (milestones)

Lime1's instantiation (preparation, segment initialisation, start function) is
Core `Instantiate` followed by Core execution, related by `ModuleInstSim` and
`Store.erase`; a divergent Lime1 instantiation diverges in Core.

## Side conditions (`InstantiationBounds`)

The milestones as first stated are false in general; they hold under the
following side conditions, which are bundled in `InstantiationBounds`:

* `noGlobals`: SpecTec 3.0 `$instantiate` evaluates global initializers with
  `$evalglobals`, which *allocates* every global into the store, and then
  `$allocmodule` allocates the module's globals a second time in that store. The
  Core store therefore contains `|global*|` unreachable auxiliary globals before
  the module's own ones, so neither `Store.erase c'.store = after.toCore` nor
  `ModuleInstSim` (global addresses shift by `|global*|`) can hold when the module
  defines globals. Lifting this needs a simulation up to a global-address renaming.
* `storeWF`: `Sim` (via `ConfigWF`) requires a well-formed Lime1 store.
* `tables`: tables of the initial store have fewer than `2^32` entries. Otherwise
  the Core table type (a `Fin (2^64)` minimum) or the 32-bit `table.init`
  counters of `$runelem_` wrap.
* `data`: every data segment has fewer than `2^32` bytes (`$rundata_` emits
  `CONST I32 |b*|`, which wraps for a `2^32`-byte segment into a 65536-page memory).
* `elemSize`: every element segment has fewer than `2^32` initialisers
  (`$runelem_` emits `CONST I32 |e*|`, so `$instantiate` is undefined otherwise).
* `elemCount`/`dataCount`: `$runelem_`/`$rundata_` use `ElemIdx`/`DataIdx`
  (32-bit) segment indices.
-/

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution (Runtime.Result Runtime.ExternVal Runtime.ModuleInst Runtime.ExportInst
  Runtime.FuncInst Runtime.TableInst Runtime.MemInst Runtime.GlobalInst)
open Silmaril.Wasm.Execution.Runtime (Value Value.toCore GlobalInst GlobalInst.toCore)

variable {H : Type}

/-- Side conditions under which Core instantiation simulates Lime1 instantiation
(see the module documentation for why each is needed). -/
structure InstantiationBounds (before : Store H) (m : Module) : Prop where
  storeWF : StoreWF before
  noGlobals : m.globals = []
  tables : ∀ t ∈ before.tables, t.refs.length < 2 ^ 32
  data : ∀ d ∈ m.data, d.bytes.size < 2 ^ 32
  elemSize : ∀ e ∈ m.elems, e.init.length < 2 ^ 32
  elemCount : m.elems.length ≤ 2 ^ 32
  dataCount : m.data.length ≤ 2 ^ 32

/-! ## Core steps never change the frame's module -/

theorem coreStep_frame_module {P : Profile} {tgt : ToCore.CHostSemantics H}
    {c c' : ToCore.CConfig H} (h : Silmaril.Wasm.Execution.Core.Step P tgt c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | «variable» h => cases h <;> rfl
  | table h => cases h <;> rfl
  | memory h => cases h <;> rfl
  | reference h => cases h <;> rfl
  | aggregate h => cases h <;> rfl
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | _ => rfl

theorem coreSteps_frame_module {P : Profile} {tgt : ToCore.CHostSemantics H}
    {c c' : ToCore.CConfig H} (h : Silmaril.Wasm.Execution.Core.Steps P tgt c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [coreStep_frame_module hs, ih]

/-! ## Import matching is Core `Externaddr_ok` -/

theorem limitsSub_of_match {size : Nat} {maximum : Option Nat} {l : V1.Limits}
    (hsize : size < 2 ^ 64) (h : LimitsMatch size maximum l) :
    Wasm.Validation.LimitsSub ⟨Fin.ofNat _ size, maximum.map (Fin.ofNat _)⟩ l.toCore := by
  obtain ⟨hmin, hmax⟩ := h
  have hmin' : (V1.widen32 l.min).val ≤ (Fin.ofNat (2 ^ 64) size).val := by
    simp only [V1.widen32, Fin.val_ofNat, Nat.mod_eq_of_lt hsize]; exact hmin
  rcases hl : l.max with _ | b
  · rcases hm : maximum with _ | a
    · simpa [V1.Limits.toCore, hl] using Wasm.Validation.LimitsSub.eps hmin'
    · simpa [V1.Limits.toCore, hl] using
        (Wasm.Validation.LimitsSub.max (m₁ := Fin.ofNat _ a) (m₂ := none) hmin' (by simp))
  · obtain ⟨a, ha, hab⟩ := hmax b (by simp [hl])
    have ha' : maximum = some a := ha
    have hb := b.isLt
    have := Wasm.Validation.LimitsSub.max (m₁ := Fin.ofNat (2 ^ 64) a)
      (m₂ := some (V1.widen32 b)) hmin' (by
        intro m hm
        simp only [Option.some.injEq] at hm
        subst hm
        simp only [V1.widen32, Fin.val_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]; exact hab)
    simpa [V1.Limits.toCore, hl, ha'] using this

theorem externAddrOk_import {before : Store H} {types : List FuncType} {i : Import}
    {e : Runtime.ExternVal} (hwf : StoreWF before)
    (htab : ∀ t ∈ before.tables, t.refs.length < 2 ^ 32)
    (hv : Validation.ImportValid types i)
    (h : ∃ et, Validation.importType? types i.desc = some et ∧ ExternMatches before e et) :
    Silmaril.Wasm.Execution.Core.ExternAddrOk before.toCore e.toCore
      (Validation.importC types i.desc) := by
  obtain ⟨et, het, hm⟩ := h
  obtain ⟨et', het', hval⟩ := hv
  rw [het] at het'
  cases het'
  rcases i with ⟨mn, n, d⟩
  cases d with
  | func x =>
    simp only [Validation.importType?, Option.map_eq_some_iff] at het
    obtain ⟨ft, hft, rfl⟩ := het
    cases hm with
    | func a fn ft found typed =>
      have hc : before.toCore.funcs[a.value]? = some fn.toCore := by
        simp [Silmaril.Wasm.Execution.Runtime.Store.toCore, found]
      have := Silmaril.Wasm.Execution.Core.ExternAddrOk.func hc
      have hty : fn.toCore.type = ft.toDefType := by
        subst typed; cases fn <;> rfl
      simpa [Validation.importC, hft, hty, Silmaril.Wasm.Execution.Runtime.ExternVal.toCore]
        using this
  | table tt =>
    simp only [Validation.importType?, Option.some.injEq] at het
    subst het
    cases hm with
    | table a table tt found limits =>
      have hc : before.toCore.tables[a.value]? = some table.toCore := by
        simp [Silmaril.Wasm.Execution.Runtime.Store.toCore, found]
      have hlen : table.refs.length < 2 ^ 32 := htab _ (List.mem_of_getElem? found)
      refine Silmaril.Wasm.Execution.Core.ExternAddrOk.sub
        (Silmaril.Wasm.Execution.Core.ExternAddrOk.table hc)
        (.table (Validation.tableTypeOk_toCore _ hval)) (.table ?_)
      simp only [Silmaril.Wasm.Execution.Runtime.TableInst.toCore,
        Validation.tableToC]
      refine Wasm.Validation.TableSub.mk ?_ (Wasm.Validation.Sub.refl _ (k := .ref) trivial _)
        (Wasm.Validation.Sub.refl _ (k := .ref) trivial _)
      have := limitsSub_of_match (by omega) limits
      simpa [List.length_map] using this
  | memory mt =>
    simp only [Validation.importType?, Option.some.injEq] at het
    subst het
    cases hm with
    | memory a memory mt found limits =>
      have hc : before.toCore.mems[a.value]? = some memory.toCore := by
        simp [Silmaril.Wasm.Execution.Runtime.Store.toCore, found]
      have hsz : memory.data.size ≤ 2 ^ 32 := (hwf.2 _ _ found).1
      refine Silmaril.Wasm.Execution.Core.ExternAddrOk.sub
        (Silmaril.Wasm.Execution.Core.ExternAddrOk.mem hc)
        (.mem (Validation.memTypeOk_toCore hval)) (.mem ?_)
      simp only [Silmaril.Wasm.Execution.Runtime.MemInst.toCore,
        V1.MemoryType.toCore]
      refine Wasm.Validation.MemSub.mk ?_
      have hp : memory.data.size / Silmaril.Wasm.Execution.Memory.pageSize < 2 ^ 64 :=
        lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      exact limitsSub_of_match hp limits
  | global gt =>
    simp only [Validation.importType?, Option.some.injEq] at het
    subst het
    cases hm with
    | global a g gt found type mutability =>
      have hc : before.toCore.globals[a.value]? = some g.toCore := by
        simp [Silmaril.Wasm.Execution.Runtime.Store.toCore, found]
      have := Silmaril.Wasm.Execution.Core.ExternAddrOk.global hc
      simpa [Validation.importC, Validation.globalToC,
        Silmaril.Wasm.Execution.Runtime.GlobalInst.toCore, type, mutability,
        Silmaril.Wasm.Execution.Runtime.ExternVal.toCore] using this

theorem instantiate_valid {before : Store H} {m : Module}
    {imports : List Runtime.ExternVal} (bounds : InstantiationBounds before m)
    (hv : Validation.ModuleValid m) (hi : ImportsMatch before m imports) :
    ∃ xtE xtI, Wasm.Validation.ModuleOk m.toCore ⟨xtI, xtE⟩ ∧
      List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk before.toCore)
        (imports.map Runtime.ExternVal.toCore) xtI := by
  obtain ⟨xtE, hok⟩ := Validation.ModuleValid.toCore_ok hv
  refine ⟨xtE, _, hok, ?_⟩
  have key : ∀ (imps : List Import) (es : List Runtime.ExternVal),
      (∀ i ∈ imps, Validation.ImportValid m.types i) →
      List.Forall₂ (fun i e => ∃ et, Validation.importType? m.types i.desc = some et ∧
        ExternMatches before e et) imps es →
      List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk before.toCore)
        (es.map Runtime.ExternVal.toCore) (imps.map fun i => Validation.importC m.types i.desc) := by
    intro imps es hvs hf
    induction hf with
    | nil => exact .nil
    | cons hh _ ih =>
      exact .cons (externAddrOk_import bounds.storeWF bounds.tables (hvs _ (by simp)) hh)
        (ih (fun i hi => hvs i (by simp [hi])))
  exact key _ _ hv.imports hi

/-! ## Inverting Lime1 preparation -/

/-- The allocated module instance, before exports are recorded. -/
def baseInst (s : Store H) (m : Module) (imports : List Runtime.ExternVal) : Runtime.ModuleInst where
  types := m.types
  funcs := (importedInstance imports).funcs ++ addresses .func s.funcs.length m.funcs.length
  tables := (importedInstance imports).tables ++ addresses .table s.tables.length m.tables.length
  memories := (importedInstance imports).memories ++
    addresses .memory s.memories.length m.memories.length
  globals := (importedInstance imports).globals

@[simp] theorem addresses_zero (k : Silmaril.Wasm.Execution.Runtime.AddrKind) (n : Nat) :
    addresses k n 0 = [] := rfl

theorem allocate?_inv {s : Store H} {m : Module} {imports : List Runtime.ExternVal}
    {st : Store H} {mod : Runtime.ModuleInst} (hg : m.globals = [])
    (h : allocate? s m imports = some (st, mod)) :
    ∃ (exports : List Runtime.ExportInst) (funcs : List (Runtime.FuncInst Func H)),
      m.exports.mapM (fun e => (exportValue? (baseInst s m imports) e.index).bind
        fun v => some (⟨e.name, v⟩ : Runtime.ExportInst)) = some exports ∧
      m.funcs.mapM (fun f => (m.types[f.type.toNat]?).bind
        fun ft => some (Runtime.FuncInst.wasm ft { baseInst s m imports with exports := exports } f)) =
        some funcs ∧
      mod = { baseInst s m imports with exports := exports } ∧
      st = ⟨s.funcs ++ funcs, s.tables ++ m.tables.map (fun t =>
          Runtime.TableInst.mk (List.replicate t.limits.min.val none) (t.limits.max.map Fin.val)),
        s.memories ++ m.memories.map (fun t => Runtime.MemInst.mk
          ⟨Array.replicate (t.limits.min.val * Silmaril.Wasm.Execution.Memory.pageSize) 0⟩
          (t.limits.max.map Fin.val)),
        s.globals⟩ := by
  simp only [allocate?, hg, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Option.bind_eq_some_iff, List.length_nil, addresses_zero,
    List.append_nil] at h
  obtain ⟨exports, hex, funcs, hfn, h⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨exports, funcs, ?_, ?_, rfl, ?_⟩
  · rw [← hex]; rfl
  · rw [← hfn]; rfl
  · simp

theorem mapM_forall₂ {α β : Type _} {f : α → Option β} :
    {xs : List α} → {ys : List β} → xs.mapM f = some ys →
      List.Forall₂ (fun x y => f x = some y) xs ys
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact .nil
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    exact .cons hy (mapM_forall₂ hys)

theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | cons hr _ ih =>
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, by simp, hr⟩
    · obtain ⟨a, ha, hr'⟩ := ih hb
      exact ⟨a, by simp [ha], hr'⟩

theorem forall₂_getElem? {α β : Type _} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {i : Nat} {a : α} (ha : l₁[i]? = some a) :
    ∃ b, l₂[i]? = some b ∧ R a b := by
  induction h generalizing i with
  | nil => simp at ha
  | cons hr _ ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at ha ⊢; subst ha; exact ⟨_, rfl, hr⟩
    | succ i => simpa using ih (by simpa using ha)

theorem prepare?_inv {s : Store H} {m : Module} {imports : List Runtime.ExternVal}
    {p : Prepared H} (h : prepare? s m imports = some p) :
    ∃ allocated elems data, allocate? s m imports = some (allocated, p.module) ∧
      m.elems.mapM (resolveElem? allocated p.module) = some elems ∧
      m.data.mapM (resolveData? allocated p.module) = some data ∧
      p.store = data.foldl applyData (elems.foldl applyElem allocated) := by
  simp only [prepare?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨allocated, module⟩, ha, elems, he, data, hd, h⟩ := h
  have hp : p.store = data.foldl applyData (elems.foldl applyElem allocated) ∧
      p.module = module := by
    cases hs : m.start with
    | none =>
      simp only [hs, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      subst h; exact ⟨rfl, rfl⟩
    | some i =>
      simp only [hs, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨_, -, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  obtain ⟨h1, h2⟩ := hp
  subst h2
  exact ⟨allocated, elems, data, ha, he, hd, h1⟩

@[simp] theorem foldl_applyElem_funcs (ws : List ElemWrite) (st : Store H) :
    (ws.foldl applyElem st).funcs = st.funcs := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => simp only [List.foldl_cons, ih]; rfl

@[simp] theorem foldl_applyData_funcs (ws : List DataWrite) (st : Store H) :
    (ws.foldl applyData st).funcs = st.funcs := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => simp only [List.foldl_cons, ih]; rfl

@[simp] theorem foldl_applyElem_memories (ws : List ElemWrite) (st : Store H) :
    (ws.foldl applyElem st).memories = st.memories := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => simp only [List.foldl_cons, ih]; rfl

@[simp] theorem foldl_applyElem_globals (ws : List ElemWrite) (st : Store H) :
    (ws.foldl applyElem st).globals = st.globals := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => simp only [List.foldl_cons, ih]; rfl

@[simp] theorem foldl_applyData_globals (ws : List DataWrite) (st : Store H) :
    (ws.foldl applyData st).globals = st.globals := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => simp only [List.foldl_cons, ih]; rfl

@[simp] theorem foldl_applyData_tables (ws : List DataWrite) (st : Store H) :
    (ws.foldl applyData st).tables = st.tables := by
  induction ws generalizing st with
  | nil => rfl
  | cons w ws ih => simp only [List.foldl_cons, ih]; rfl

theorem copySlice_size {mem bytes : ByteArray} {off : Nat} (h : off + bytes.size ≤ mem.size) :
    (bytes.copySlice 0 mem off bytes.size).size = mem.size :=
  Silmaril.Wasm.Execution.Memory.writeBytes_size mem bytes _ off (by
    simp [Silmaril.Wasm.Execution.Memory.writeBytes, h])

/-- The size and maximum of a memory. -/
def memShape (mi : Runtime.MemInst) : Nat × Option Nat := (mi.data.size, mi.max)

/-- Data writes preserve memory sizes and maxima, given their bounds against the
original store. -/
theorem foldl_applyData_memories (st : Store H) :
    (ws : List DataWrite) → (st' : Store H) →
    (∀ i : Nat, (st'.memories[i]?).map memShape =
      (st.memories[i]?).map memShape) →
    (∀ w ∈ ws, ∃ mi, st.memories[w.address.value]? = some mi ∧
      w.offset + w.bytes.size ≤ mi.data.size) →
    ∀ i : Nat, ((ws.foldl applyData st').memories[i]?).map memShape =
      (st.memories[i]?).map memShape
  | [], st', h, _ => h
  | w :: ws, st', h, hb => by
    refine foldl_applyData_memories st ws (applyData st' w) ?_ (fun w' hw' => hb w' (by simp [hw']))
    intro i
    obtain ⟨mi, hmi, hbd⟩ := hb w (by simp)
    rw [← h i]
    simp only [applyData, List.getElem?_modify]
    split
    · next heq =>
      subst heq
      have h' := h w.address.value
      rw [hmi] at h'
      cases hc : st'.memories[w.address.value]? with
      | none => rw [hc] at h'; cases h'
      | some mi' =>
        rw [hc] at h'
        simp only [memShape, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
        simp only [memShape, Option.map_some, Option.some.injEq, Prod.mk.injEq, Functor.map]
        exact ⟨copySlice_size (by omega), trivial⟩
    · simp

/-! ## Constant expressions evaluate in Core -/

/-- A Lime1 constant stack (top at the head) as Core value instructions. -/
def stk (st : List Value) : List ToCore.CAdmin :=
  Silmaril.Wasm.Execution.Core.vals (st.map Value.toCore).reverse

@[simp] theorem stk_cons (v : Value) (st : List Value) :
    stk (v :: st) = stk st ++ [(Value.toCore v).toAdmin] := by
  simp [stk, Silmaril.Wasm.Execution.Core.vals]

theorem constBinary_inv {t : IntType} {op : IntBinOp} {st st' : List Value}
    (h : constBinary? t op st = some st') :
    ∃ (x y z : BitVec t.width) (rest : List Value),
      st = ⟨.int t, y⟩ :: ⟨.int t, x⟩ :: rest ∧ Numerics.intBinOp t op x y = .ok z ∧
      st' = ⟨.int t, z⟩ :: rest := by
  cases t with
  | i32 =>
    simp only [constBinary?] at h
    split at h
    · rename_i y x rest
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      refine ⟨x, y, z, rest, rfl, ?_, rfl⟩
      cases e : Numerics.intBinOp .i32 op x y <;> simp_all [Except.toOption]
    · cases h
  | i64 =>
    simp only [constBinary?] at h
    split at h
    · rename_i y x rest
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      refine ⟨x, y, z, rest, rfl, ?_, rfl⟩
      cases e : Numerics.intBinOp .i64 op x y <;> simp_all [Except.toOption]
    · cases h

section ConstEval

variable {P : Profile} {tgt : ToCore.CHostSemantics H} {S : ToCore.CStore H}
  {F : ToCore.CFrame} {s : Store H} {module : Runtime.ModuleInst}

theorem binop_core {t : IntType} {op : IntBinOp} {st st' : List Value}
    (h : constBinary? t op st = some st') (rest : List ToCore.CAdmin) :
    Silmaril.Wasm.Execution.Core.Steps P tgt
      ⟨S, F, stk st ++ [.plain (.intBinOp t op)] ++ rest⟩ ⟨S, F, stk st' ++ rest⟩ := by
  obtain ⟨x, y, z, r, rfl, hz, rfl⟩ := constBinary_inv h
  have := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs (P := P) (host := tgt)
    (vs := (r.map Value.toCore).reverse) (rest := rest)
    (Silmaril.Wasm.Execution.Core.Step.steps
      (Silmaril.Wasm.Execution.Core.Step.numeric (s := S) (f := F)
        (Silmaril.Wasm.Execution.Core.NumericStep.intBinOp hz)))
  simpa [stk, Silmaril.Wasm.Execution.Core.vals, Value.toCore,
    Silmaril.Wasm.Execution.Core.Val.toAdmin] using this

theorem constStep_core (hG : S.globals = s.globals.map GlobalInst.toCore)
    (hF : F.module.globals = module.globals.map (·.value))
    {i : Instr} {st st' : List Value} (h : constStep? s module i st = some st')
    (rest : List ToCore.CAdmin) :
    Silmaril.Wasm.Execution.Core.Steps P tgt
      ⟨S, F, stk st ++ [.plain i.toCore] ++ rest⟩ ⟨S, F, stk st' ++ rest⟩ := by
  cases i with
  | intConst t x =>
    simp only [constStep?, constInstr?, Option.map_some, Option.some.injEq] at h
    subst h
    simp only [stk_cons, List.append_assoc]
    exact Relation.ReflTransGen.refl
  | floatConst t x =>
    simp only [constStep?, constInstr?, Option.map_some, Option.some.injEq] at h
    subst h
    simp only [stk_cons, List.append_assoc]
    exact Relation.ReflTransGen.refl
  | globalGet x =>
    simp only [constStep?, constInstr?, Option.bind_eq_bind, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨v, ⟨a, ha, g, hg, rfl⟩, rfl⟩ := h
    have hgl : S.global? F x = some (a.value, g.toCore) := by
      simp [Silmaril.Wasm.Execution.Core.Store.global?, hF, hG, ha, hg]
    have := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs (P := P) (host := tgt)
      (vs := (st.map Value.toCore).reverse) (rest := rest)
      (Silmaril.Wasm.Execution.Core.Step.steps
        (Silmaril.Wasm.Execution.Core.Step.variable
          (Silmaril.Wasm.Execution.Core.VariableStep.globalGet hgl)))
    simpa [stk, Silmaril.Wasm.Execution.Core.vals, GlobalInst.toCore, Instr.toCore] using this
  | intBinOp t op =>
    cases op <;> first
      | (simp [constStep?, constInstr?] at h; done)
      | exact binop_core (by simpa [constStep?] using h) rest
  | _ => simp [constStep?, constInstr?] at h

theorem constFold_core (hG : S.globals = s.globals.map GlobalInst.toCore)
    (hF : F.module.globals = module.globals.map (·.value)) :
    (es : Expr) → (st st' : List Value) →
    es.foldlM (fun stack i => constStep? s module i stack) st = some st' →
    (rest : List ToCore.CAdmin) →
    Silmaril.Wasm.Execution.Core.Steps P tgt
      ⟨S, F, stk st ++ Silmaril.Wasm.Execution.Core.expression (Expr.toCore es) ++ rest⟩
      ⟨S, F, stk st' ++ rest⟩
  | [], st, st', h, rest => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simpa [Expr.toCore, Silmaril.Wasm.Execution.Core.expression] using
      (Relation.ReflTransGen.refl : Silmaril.Wasm.Execution.Core.Steps P tgt _ _)
  | i :: es, st, st', h, rest => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st₁, h₁, h₂⟩ := h
    have e1 := constStep_core (P := P) (tgt := tgt) hG hF h₁
      (Silmaril.Wasm.Execution.Core.expression (Expr.toCore es) ++ rest)
    have e2 := constFold_core hG hF es st₁ st' h₂ rest
    simp only [Expr.toCore, Silmaril.Wasm.Execution.Core.expression, List.map_cons,
      List.append_assoc, List.cons_append] at e1 e2 ⊢
    exact e1.trans e2

/-- A Lime1 offset expression evaluates in Core to its `i32` value. -/
theorem offset_core (hG : S.globals = s.globals.map GlobalInst.toCore)
    (hF : F.module.globals = module.globals.map (·.value)) {es : Expr} {off : Nat}
    (h : offset? s module es = some off) (rest : List ToCore.CAdmin) :
    ∃ x : BitVec 32, x.toNat = off ∧ Silmaril.Wasm.Execution.Core.Steps P tgt
      ⟨S, F, Silmaril.Wasm.Execution.Core.expression (Expr.toCore es) ++ rest⟩
      ⟨S, F, Silmaril.Wasm.Execution.Core.constI32 x :: rest⟩ := by
  simp only [offset?, constExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, ⟨vs, hvs, hv⟩, hoff⟩ := h
  match vs, hv with
  | [v'], hv =>
    simp only [Option.some.injEq] at hv
    subst hv
    rcases v' with ⟨ty, bits⟩
    cases ty with
    | int t =>
      cases t with
      | i32 =>
        simp only [Option.some.injEq] at hoff
        refine ⟨bits, hoff, ?_⟩
        have := constFold_core (P := P) (tgt := tgt) hG hF es [] _ hvs rest
        simpa [stk, Silmaril.Wasm.Execution.Core.vals, Value.toCore,
          Silmaril.Wasm.Execution.Core.Val.toAdmin, Silmaril.Wasm.Execution.Core.constI32,
          Silmaril.Wasm.Execution.Core.Val.i32] using this
      | i64 => simp at hoff
    | float t => simp at hoff

end ConstEval

/-! ## The `table.init` loop -/

theorem list_set_self {α : Type _} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    l.set i a = l := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_set]
  split
  · next hk =>
    subst hk
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
    simp [hlt]
  · rfl

theorem table?_inv {S : ToCore.CStore H} {F : ToCore.CFrame} {x : TableIdx} {ta : Nat}
    {ti : Silmaril.Wasm.Execution.Core.TableInst} (h : S.table? F x = some (ta, ti)) :
    F.module.tables[x.toNat]? = some ta ∧ S.tables[ta]? = some ti := by
  simp only [Silmaril.Wasm.Execution.Core.Store.table?, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a, ha, t, ht, rfl, rfl⟩ := h
  exact ⟨ha, ht⟩

theorem table?_setTable {S : ToCore.CStore H} {F : ToCore.CFrame} {x : TableIdx} {ta : Nat}
    {ti ti' : Silmaril.Wasm.Execution.Core.TableInst} (h : S.table? F x = some (ta, ti)) :
    (S.setTable ta ti').table? F x = some (ta, ti') := by
  obtain ⟨h1, h2⟩ := table?_inv h
  have hlt : ta < S.tables.length := (List.getElem?_eq_some_iff.mp h2).1
  simp [Silmaril.Wasm.Execution.Core.Store.table?, Silmaril.Wasm.Execution.Core.Store.setTable,
    h1, List.getElem?_set_self hlt]

theorem elem?_setTable {S : ToCore.CStore H} {F : ToCore.CFrame} {y : ElemIdx} {ta : Nat}
    {ti' : Silmaril.Wasm.Execution.Core.TableInst} :
    (S.setTable ta ti').elem? F y = S.elem? F y := rfl

theorem setTable_setTable (S : ToCore.CStore H) (ta : Nat)
    (a b : Silmaril.Wasm.Execution.Core.TableInst) :
    (S.setTable ta a).setTable ta b = S.setTable ta b := by
  simp [Silmaril.Wasm.Execution.Core.Store.setTable, List.set_set]

theorem tableInit_core {P : Profile} {tgt : ToCore.CHostSemantics H} {F : ToCore.CFrame}
    {x : TableIdx} {y : ElemIdx} {ea : Nat} {ei : Silmaril.Wasm.Execution.Core.ElemInst} :
    (n : Nat) → (S : ToCore.CStore H) → (ta : Nat) →
    (ti : Silmaril.Wasm.Execution.Core.TableInst) → (i j : BitVec 32) →
    S.table? F x = some (ta, ti) → S.elem? F y = some (ea, ei) →
    ti.refs.length < 2 ^ 32 → ei.refs.length < 2 ^ 32 →
    i.toNat + n ≤ ti.refs.length → j.toNat + n ≤ ei.refs.length →
    (rest : List ToCore.CAdmin) →
    Silmaril.Wasm.Execution.Core.Steps P tgt
      ⟨S, F, [Silmaril.Wasm.Execution.Core.aconst .i32 i, Silmaril.Wasm.Execution.Core.constI32 j,
        Silmaril.Wasm.Execution.Core.constI32 (BitVec.ofNat 32 n), .plain (.tableInit x y)] ++ rest⟩
      ⟨S.setTable ta { ti with refs := (ti.refs.take i.toNat ++ (ei.refs.drop j.toNat).take n ++
          ti.refs.drop (i.toNat + n)) }, F, rest⟩
  | 0, S, ta, ti, i, j, ht, he, hti, hei, hi, hj, rest => by
    have hstep := Silmaril.Wasm.Execution.Core.Step.table (P := P) (host := tgt)
      (Silmaril.Wasm.Execution.Core.TableStep.initZero (a := .i32) (i := i) (j := j) ht he
        ⟨(show i.toNat ≤ ti.refs.length by omega), (show j.toNat ≤ ei.refs.length by omega)⟩)
    have := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs (vs := []) (rest := rest)
      (Relation.ReflTransGen.single hstep)
    have hS : S.setTable ta { ti with refs := (ti.refs.take i.toNat ++
        (ei.refs.drop j.toNat).take 0 ++ ti.refs.drop (i.toNat + 0)) } = S := by
      simp only [List.take_zero, List.append_nil, Nat.add_zero, List.take_append_drop]
      exact congrArg (fun l => { S with tables := l }) (list_set_self (table?_inv ht).2)
    rw [hS]
    simpa [Silmaril.Wasm.Execution.Core.vals] using this
  | n + 1, S, ta, ti, i, j, ht, he, hti, hei, hi, hj, rest => by
    obtain ⟨r, hr⟩ : ∃ r, ei.refs[j.toNat]? = some r :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    have hN : (BitVec.ofNat 32 (n + 1)).toNat = n + 1 := by
      simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    have hn : BitVec.ofNat 32 (n + 1) ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [hN] at this
      simp at this
    have s1 := Silmaril.Wasm.Execution.Core.Step.table (P := P) (host := tgt)
      (Silmaril.Wasm.Execution.Core.TableStep.initSucc (a := .i32) (i := i) (j := j)
        (n := BitVec.ofNat 32 (n + 1)) ht he
        ⟨(show i.toNat + (BitVec.ofNat 32 (n + 1)).toNat ≤ ti.refs.length by rw [hN]; omega),
         (show j.toNat + (BitVec.ofNat 32 (n + 1)).toNat ≤ ei.refs.length by rw [hN]; omega)⟩
        hn hr)
    have s1' := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs (vs := []) (rest := rest)
      (Relation.ReflTransGen.single s1)
    have s2 := Silmaril.Wasm.Execution.Core.Step.table (P := P) (host := tgt)
      (Silmaril.Wasm.Execution.Core.TableStep.setVal (a := .i32) (i := i) (r := r) ht
        (show i.toNat < ti.refs.length by omega))
    have s2' := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs (vs := [])
      (rest := [Silmaril.Wasm.Execution.Core.aconst .i32 (i + 1 : BitVec 32),
        Silmaril.Wasm.Execution.Core.constI32 (j + 1),
        Silmaril.Wasm.Execution.Core.constI32 (BitVec.ofNat 32 (n + 1) - 1),
        .plain (.tableInit x y)] ++ rest)
      (Relation.ReflTransGen.single s2)
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
    have hsub : BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, hN, h1, BitVec.toNat_ofNat]
      omega
    have hlen : (ti.refs.set i.toNat r).length = ti.refs.length := List.length_set ..
    have s3 := tableInit_core (P := P) (tgt := tgt) n (S.setTable ta { ti with refs := ti.refs.set i.toNat r }) ta
      { ti with refs := ti.refs.set i.toNat r } (i + 1) (j + 1) (table?_setTable ht)
      (by rw [elem?_setTable]; exact he) (by simpa using hti) hei
      (show (i + 1).toNat + n ≤ (ti.refs.set i.toNat r).length by rw [hi1, hlen]; omega)
      (show (j + 1).toNat + n ≤ ei.refs.length by rw [hj1]; omega) rest
    rw [setTable_setTable] at s3
    dsimp only at s3
    rw [hsub] at s1' s2'
    simp only [Silmaril.Wasm.Execution.Core.vals, List.map_nil, List.nil_append,
      List.cons_append] at s1' s2'
    have hlist : (ti.refs.set i.toNat r).take (i + 1).toNat ++
        (ei.refs.drop (j + 1).toNat).take n ++ (ti.refs.set i.toNat r).drop ((i + 1).toNat + n) =
        ti.refs.take i.toNat ++ (ei.refs.drop j.toNat).take (n + 1) ++
          ti.refs.drop (i.toNat + (n + 1)) := by
      rw [hi1, hj1]
      have hk : i.toNat < ti.refs.length := by omega
      have hdj : ei.refs.drop j.toNat = r :: ei.refs.drop (j.toNat + 1) := by
        rw [List.drop_eq_getElem_cons (by omega)]
        obtain ⟨_, hr'⟩ := List.getElem?_eq_some_iff.mp hr
        rw [hr']
      have ht1 : (ti.refs.set i.toNat r).take (i.toNat + 1) = ti.refs.take i.toNat ++ [r] := by
        rw [List.take_add_one, List.take_set, List.getElem?_set_self hk,
          List.set_eq_of_length_le (by simp)]
        rfl
      have hd1 : (ti.refs.set i.toNat r).drop (i.toNat + 1 + n) =
          ti.refs.drop (i.toNat + (n + 1)) := by
        rw [List.drop_set, ite_eq_left (by omega)]; congr 1; omega
      rw [ht1, hd1, hdj, List.take_succ_cons]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hlist] at s3
    have e := (s1'.trans s2').trans s3
    simpa only [List.cons_append, List.nil_append] using e

/-! ## Byte-level helpers -/

theorem copySlice_toList {src dest : ByteArray} {off len : Nat} (hl : src.size = len)
    (h : off + len ≤ dest.size) :
    (src.copySlice 0 dest off len).data.toList =
      dest.data.toList.take off ++ src.data.toList ++ dest.data.toList.drop (off + len) := by
  subst hl
  have hs : src.size = src.data.size := rfl
  have hd : dest.size = dest.data.size := rfl
  have e1 : (src.data.toList.drop 0).take (0 + src.size - 0) = src.data.toList := by
    rw [List.drop_zero, Nat.zero_add, Nat.sub_zero]
    exact List.take_of_length_le (by rw [Array.length_toList]; exact le_refl _)
  have e2 : (dest.data.toList.drop (off + min src.size (src.data.size - 0))).take
      (dest.data.size - (off + min src.size (src.data.size - 0))) =
      dest.data.toList.drop (off + src.size) := by
    rw [← hs, Nat.sub_zero, Nat.min_self]
    exact List.take_of_length_le (by simp)
  have e0 : (dest.data.toList.drop 0).take (off - 0) = dest.data.toList.take off := by simp
  simp only [ByteArray.copySlice, Array.toList_append, Array.toList_extract,
    List.extract_eq_take_drop]
  rw [e0, e1, e2]

theorem store8_eq (mem : ByteArray) (k : Nat) (byte : UInt8) (hk : k < mem.size) :
    Silmaril.Wasm.Execution.Memory.store mem
      (Silmaril.Wasm.Execution.Core.effAddr k Silmaril.Wasm.Execution.Core.memarg0)
      (count := PackSize.i8.width / 8) ((BitVec.ofNat 32 byte.toNat).setWidth _) =
      some ⟨(mem.data.toList.set k byte).toArray⟩ := by
  have e1 : Silmaril.Wasm.Execution.Core.effAddr k Silmaril.Wasm.Execution.Core.memarg0 = k := rfl
  have e2 : Silmaril.Wasm.Execution.Memory.encodeLE (PackSize.i8.width / 8)
      ((BitVec.ofNat 32 byte.toNat).setWidth (8 * (PackSize.i8.width / 8))).toNat =
      ⟨#[byte]⟩ := by
    apply ByteArray.ext
    simp [Silmaril.Wasm.Execution.Memory.encodeLE, PackSize.width]
  simp only [Silmaril.Wasm.Execution.Memory.store, e1, e2, Silmaril.Wasm.Execution.Memory.writeBytes]
  have hsz : (⟨#[byte]⟩ : ByteArray).size = 1 := rfl
  rw [ite_eq_left (by rw [hsz]; omega)]
  congr 1
  apply ByteArray.ext
  apply Array.ext'
  rw [copySlice_toList rfl (by rw [hsz]; omega), List.set_eq_take_append_cons_drop,
    ite_eq_left (by rw [Array.length_toList]; exact hk), hsz]
  simp

/-! ## The `memory.init` loop -/

theorem mem?_inv {S : ToCore.CStore H} {F : ToCore.CFrame} {x : MemIdx} {ma : Nat}
    {mi : Silmaril.Wasm.Execution.Core.MemInst} (h : S.mem? F x = some (ma, mi)) :
    F.module.mems[x.toNat]? = some ma ∧ S.mems[ma]? = some mi := by
  simp only [Silmaril.Wasm.Execution.Core.Store.mem?, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a, ha, t, ht, rfl, rfl⟩ := h
  exact ⟨ha, ht⟩

theorem mem?_setMem {S : ToCore.CStore H} {F : ToCore.CFrame} {x : MemIdx} {ma : Nat}
    {mi mi' : Silmaril.Wasm.Execution.Core.MemInst} (h : S.mem? F x = some (ma, mi)) :
    (S.setMem ma mi').mem? F x = some (ma, mi') := by
  obtain ⟨h1, h2⟩ := mem?_inv h
  have hlt : ma < S.mems.length := (List.getElem?_eq_some_iff.mp h2).1
  simp [Silmaril.Wasm.Execution.Core.Store.mem?, Silmaril.Wasm.Execution.Core.Store.setMem,
    h1, List.getElem?_set_self hlt]

theorem data?_setMem {S : ToCore.CStore H} {F : ToCore.CFrame} {y : DataIdx} {ma : Nat}
    {mi' : Silmaril.Wasm.Execution.Core.MemInst} :
    (S.setMem ma mi').data? F y = S.data? F y := rfl

theorem setMem_setMem (S : ToCore.CStore H) (ma : Nat)
    (a b : Silmaril.Wasm.Execution.Core.MemInst) :
    (S.setMem ma a).setMem ma b = S.setMem ma b := by
  simp [Silmaril.Wasm.Execution.Core.Store.setMem, List.set_set]

theorem memInit_core {P : Profile} {tgt : ToCore.CHostSemantics H} {F : ToCore.CFrame}
    {x : MemIdx} {y : DataIdx} {da : Nat} {di : Silmaril.Wasm.Execution.Core.DataInst} :
    (n : Nat) → (S : ToCore.CStore H) → (ma : Nat) →
    (mi : Silmaril.Wasm.Execution.Core.MemInst) → (i j : BitVec 32) →
    S.mem? F x = some (ma, mi) → S.data? F y = some (da, di) →
    mi.bytes.size ≤ 2 ^ 32 → di.bytes.size < 2 ^ 32 →
    i.toNat + n ≤ mi.bytes.size → j.toNat + n ≤ di.bytes.size →
    (rest : List ToCore.CAdmin) →
    Silmaril.Wasm.Execution.Core.Steps P tgt
      ⟨S, F, [Silmaril.Wasm.Execution.Core.aconst .i32 i, Silmaril.Wasm.Execution.Core.constI32 j,
        Silmaril.Wasm.Execution.Core.constI32 (BitVec.ofNat 32 n), .plain (.memoryInit x y)] ++ rest⟩
      ⟨S.setMem ma { mi with bytes := ⟨(mi.bytes.data.toList.take i.toNat ++
          (di.bytes.data.toList.drop j.toNat).take n ++
          mi.bytes.data.toList.drop (i.toNat + n)).toArray⟩ }, F, rest⟩
  | 0, S, ma, mi, i, j, hm, hd, hmi, hdi, hi, hj, rest => by
    have hstep := Silmaril.Wasm.Execution.Core.Step.memory (P := P) (host := tgt)
      (Silmaril.Wasm.Execution.Core.MemoryStep.initZero (a := .i32) (i := i) (j := j) hm hd
        ⟨(show i.toNat ≤ mi.bytes.size by omega), (show j.toNat ≤ di.bytes.size by omega)⟩)
    have := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs (vs := []) (rest := rest)
      (Relation.ReflTransGen.single hstep)
    have hS : S.setMem ma { mi with bytes := ⟨(mi.bytes.data.toList.take i.toNat ++
        (di.bytes.data.toList.drop j.toNat).take 0 ++
        mi.bytes.data.toList.drop (i.toNat + 0)).toArray⟩ } = S := by
      simp only [List.take_zero, List.append_nil, Nat.add_zero, List.take_append_drop,
        Array.toArray_toList]
      exact congrArg (fun l => { S with mems := l }) (list_set_self (mem?_inv hm).2)
    rw [hS]
    simpa [Silmaril.Wasm.Execution.Core.vals] using this
  | n + 1, S, ma, mi, i, j, hm, hd, hmi, hdi, hi, hj, rest => by
    have hjlt : j.toNat < di.bytes.data.size := by
      have : di.bytes.size = di.bytes.data.size := rfl
      omega
    obtain ⟨byte, hb⟩ : ∃ b, di.bytes.data[j.toNat]? = some b :=
      ⟨_, Array.getElem?_eq_getElem hjlt⟩
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    have hN : (BitVec.ofNat 32 (n + 1)).toNat = n + 1 := by
      simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    have hn : BitVec.ofNat 32 (n + 1) ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [hN] at this
      simp at this
    have s1 := Silmaril.Wasm.Execution.Core.Step.memory (P := P) (host := tgt)
      (Silmaril.Wasm.Execution.Core.MemoryStep.initSucc (a := .i32) (i := i) (j := j)
        (n := BitVec.ofNat 32 (n + 1)) hm hd
        ⟨(show i.toNat + (BitVec.ofNat 32 (n + 1)).toNat ≤ mi.bytes.size by rw [hN]; omega),
         (show j.toNat + (BitVec.ofNat 32 (n + 1)).toNat ≤ di.bytes.size by rw [hN]; omega)⟩
        hn hb)
    have s1' := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs (vs := []) (rest := rest)
      (Relation.ReflTransGen.single s1)
    have hk : i.toNat < mi.bytes.size := by omega
    have s2 := Silmaril.Wasm.Execution.Core.Step.memory (P := P) (host := tgt)
      (Silmaril.Wasm.Execution.Core.MemoryStep.storePackVal (t := .i32) (sz := .i8)
        (arg := Silmaril.Wasm.Execution.Core.memarg0) (a := .i32) (i := i)
        (c := BitVec.ofNat 32 byte.toNat) hm (store8_eq mi.bytes i.toNat byte hk))
    have s2' := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs (vs := [])
      (rest := [Silmaril.Wasm.Execution.Core.aconst .i32 (i + 1 : BitVec 32),
        Silmaril.Wasm.Execution.Core.constI32 (j + 1),
        Silmaril.Wasm.Execution.Core.constI32 (BitVec.ofNat 32 (n + 1) - 1),
        .plain (.memoryInit x y)] ++ rest)
      (Relation.ReflTransGen.single s2)
    have hi1 : (i + 1).toNat ≤ i.toNat + 1 := by
      rw [BitVec.toNat_add, h1]; exact Nat.mod_le _ _
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
    have hsub : BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, hN, h1, BitVec.toNat_ofNat]
      omega
    have hlen : (⟨(mi.bytes.data.toList.set i.toNat byte).toArray⟩ : ByteArray).size =
        mi.bytes.size := by
      show (mi.bytes.data.toList.set i.toNat byte).toArray.size = mi.bytes.data.size
      simp
    have s3 := memInit_core (P := P) (tgt := tgt) n
      (S.setMem ma { mi with bytes := ⟨(mi.bytes.data.toList.set i.toNat byte).toArray⟩ }) ma
      { mi with bytes := ⟨(mi.bytes.data.toList.set i.toNat byte).toArray⟩ } (i + 1) (j + 1)
      (mem?_setMem hm) (by rw [data?_setMem]; exact hd) (by rw [hlen]; exact hmi) hdi
      (show (i + 1).toNat + n ≤ _ by rw [hlen]; omega)
      (show (j + 1).toNat + n ≤ di.bytes.size by rw [hj1]; omega) rest
    rw [setMem_setMem] at s3
    dsimp only at s3
    rw [hsub] at s1' s2'
    simp only [Silmaril.Wasm.Execution.Core.vals, List.map_nil, List.nil_append,
      List.cons_append] at s1' s2'
    have hlist : ((mi.bytes.data.toList.set i.toNat byte).toArray.toList.take (i + 1).toNat ++
        (di.bytes.data.toList.drop (j + 1).toNat).take n ++
        (mi.bytes.data.toList.set i.toNat byte).toArray.toList.drop ((i + 1).toNat + n)) =
        mi.bytes.data.toList.take i.toNat ++ (di.bytes.data.toList.drop j.toNat).take (n + 1) ++
          mi.bytes.data.toList.drop (i.toNat + (n + 1)) := by
      simp only
      have hkl : i.toNat < mi.bytes.data.toList.length := by
        rw [Array.length_toList]; exact hk
      have hdj : di.bytes.data.toList.drop j.toNat =
          byte :: di.bytes.data.toList.drop (j.toNat + 1) := by
        rw [List.drop_eq_getElem_cons (by rw [Array.length_toList]; exact hjlt)]
        obtain ⟨_, hb'⟩ := Array.getElem?_eq_some_iff.mp hb
        simp [hb']
      rw [hdj, List.take_succ_cons]
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp only [List.take_zero, List.append_nil, Nat.add_zero, List.take_append_drop,
          List.set_eq_take_append_cons_drop, ite_eq_left hkl]
        simp
      · have hi1' : (i + 1).toNat = i.toNat + 1 := by
          rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
        rw [hi1', hj1]
        have ht1 : (mi.bytes.data.toList.set i.toNat byte).take (i.toNat + 1) =
            mi.bytes.data.toList.take i.toNat ++ [byte] := by
          rw [List.take_add_one, List.take_set, List.getElem?_set_self hkl,
            List.set_eq_of_length_le (by simp)]
          rfl
        have hd1 : (mi.bytes.data.toList.set i.toNat byte).drop (i.toNat + 1 + n) =
            mi.bytes.data.toList.drop (i.toNat + (n + 1)) := by
          rw [List.drop_set, ite_eq_left (by omega)]; congr 1; omega
        rw [ht1, hd1]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hlist] at s3
    have e := (s1'.trans s2').trans s3
    simpa only [List.cons_append, List.nil_append] using e

/-! ## Core allocation and initializer evaluation -/

theorem resolveElem?_inv {s : Store H} {module : Runtime.ModuleInst} {e : Elem} {w : ElemWrite}
    (h : resolveElem? s module e = some w) :
    ∃ a table, offset? s module e.offset = some w.offset ∧
      module.tables[e.table.toNat]? = some a ∧ s.tables[a.value]? = some table ∧
      e.init.mapM (fun i => module.funcs[i.toNat]?) = some w.values ∧
      w.offset + w.values.length ≤ table.refs.length ∧ w.address = a := by
  simp only [resolveElem?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨off, hoff, a, ha, table, ht, refs, hrefs, h⟩ := h
  split at h
  · simp only [Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨a, table, hoff, ha, ht, hrefs, by assumption, rfl⟩
  · cases h

theorem resolveData?_inv {s : Store H} {module : Runtime.ModuleInst} {d : Data} {w : DataWrite}
    (h : resolveData? s module d = some w) :
    ∃ a memory, offset? s module d.offset = some w.offset ∧
      module.memories[d.memory.toNat]? = some a ∧ s.memories[a.value]? = some memory ∧
      w.bytes = d.bytes ∧ w.offset + d.bytes.size ≤ memory.data.size ∧ w.address = a := by
  simp only [resolveData?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨off, hoff, a, ha, memory, hm, h⟩ := h
  split at h
  · simp only [Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨a, memory, hoff, ha, hm, rfl, by assumption, rfl⟩
  · cases h

theorem mapM_of_forall₂ {α β : Type _} {f : α → Option β} :
    {xs : List α} → {ys : List β} → List.Forall₂ (fun x y => f x = some y) xs ys →
      xs.mapM f = some ys
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp [List.mapM_cons, h, mapM_of_forall₂ hs]

theorem externAddr_funcs_toCore : (imports : List Runtime.ExternVal) →
    Silmaril.Wasm.Execution.Core.ExternAddr.funcs (imports.map Runtime.ExternVal.toCore) =
      (importedInstance imports).funcs.map (·.value)
  | [] => rfl
  | e :: es => by
    have ih := externAddr_funcs_toCore es
    simp only [importedInstance] at ih ⊢
    cases e <;> simp [Silmaril.Wasm.Execution.Core.ExternAddr.funcs,
      Silmaril.Wasm.Execution.Runtime.ExternVal.toCore, ih]

theorem externAddr_tables_toCore : (imports : List Runtime.ExternVal) →
    Silmaril.Wasm.Execution.Core.ExternAddr.tables (imports.map Runtime.ExternVal.toCore) =
      (importedInstance imports).tables.map (·.value)
  | [] => rfl
  | e :: es => by
    have ih := externAddr_tables_toCore es
    simp only [importedInstance] at ih ⊢
    cases e <;> simp [Silmaril.Wasm.Execution.Core.ExternAddr.tables,
      Silmaril.Wasm.Execution.Runtime.ExternVal.toCore, ih]

theorem externAddr_mems_toCore : (imports : List Runtime.ExternVal) →
    Silmaril.Wasm.Execution.Core.ExternAddr.mems (imports.map Runtime.ExternVal.toCore) =
      (importedInstance imports).memories.map (·.value)
  | [] => rfl
  | e :: es => by
    have ih := externAddr_mems_toCore es
    simp only [importedInstance] at ih ⊢
    cases e <;> simp [Silmaril.Wasm.Execution.Core.ExternAddr.mems,
      Silmaril.Wasm.Execution.Runtime.ExternVal.toCore, ih]

theorem externAddr_globals_toCore : (imports : List Runtime.ExternVal) →
    Silmaril.Wasm.Execution.Core.ExternAddr.globals (imports.map Runtime.ExternVal.toCore) =
      (importedInstance imports).globals.map (·.value)
  | [] => rfl
  | e :: es => by
    have ih := externAddr_globals_toCore es
    simp only [importedInstance] at ih ⊢
    cases e <;> simp [Silmaril.Wasm.Execution.Core.ExternAddr.globals,
      Silmaril.Wasm.Execution.Runtime.ExternVal.toCore, ih]

theorem externAddr_tags_toCore : (imports : List Runtime.ExternVal) →
    Silmaril.Wasm.Execution.Core.ExternAddr.tags (imports.map Runtime.ExternVal.toCore) = []
  | [] => rfl
  | e :: es => by
    cases e <;> simp [Silmaril.Wasm.Execution.Core.ExternAddr.tags,
      Silmaril.Wasm.Execution.Runtime.ExternVal.toCore, externAddr_tags_toCore es]

theorem range_map_succ (L n : Nat) :
    (List.range (n + 1)).map (L + ·) = L :: (List.range n).map ((L + 1) + ·) := by
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  omega

theorem allocMany_eq {α β : Type} (get : ToCore.CStore H → List β)
    (set : ToCore.CStore H → List β → ToCore.CStore H) (g : α → β)
    (alloc : ToCore.CStore H → α → ToCore.CStore H × Nat)
    (halloc : ∀ s x, alloc s x = (set s (get s ++ [g x]), (get s).length))
    (hgs : ∀ s l, get (set s l) = l) (hss : ∀ s l l', set (set s l) l' = set s l')
    (hsg : ∀ s, set s (get s) = s) :
    ∀ (xs : List α) (s : ToCore.CStore H), Silmaril.Wasm.Execution.Core.allocMany alloc s xs =
      (set s (get s ++ xs.map g), (List.range xs.length).map ((get s).length + ·))
  | [], s => by simp [Silmaril.Wasm.Execution.Core.allocMany, hsg]
  | x :: xs, s => by
    have ih := allocMany_eq get set g alloc halloc hgs hss hsg xs (set s (get s ++ [g x]))
    simp only [Silmaril.Wasm.Execution.Core.allocMany, halloc, ih, hgs, hss, List.length_append,
      List.map_cons, List.length_cons, range_map_succ,
      List.append_assoc, List.singleton_append, List.length_nil, Nat.zero_add]

section Eval

variable {P : Profile} {tgt : ToCore.CHostSemantics H}

theorem evalExprs_tables (s : ToCore.CStore H) (f : ToCore.CFrame) :
    (ts : List TableType) →
    Silmaril.Wasm.Execution.Core.EvalExprs P tgt s f ((ts.map tableToCore).map Wasm.Table.init)
      s f (ts.map fun _ => .null)
  | [] => .nil
  | _ :: ts => by
    refine .cons ?_ (evalExprs_tables s f ts)
    exact Relation.ReflTransGen.single (Silmaril.Wasm.Execution.Core.Step.reference
      (Silmaril.Wasm.Execution.Core.RefStep.refNull _))

theorem evalExprs_refs (s : ToCore.CStore H) (f : ToCore.CFrame) {module : Runtime.ModuleInst}
    (hf : f.module.funcs = module.funcs.map (·.value)) :
    (xs : List FuncIdx) → (as : List Silmaril.Wasm.Execution.Runtime.FuncAddr) →
    xs.mapM (fun i => module.funcs[i.toNat]?) = some as →
    Silmaril.Wasm.Execution.Core.EvalExprs P tgt s f (xs.map funcRef) s f
      (as.map fun a => .func a.value)
  | [], as, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact .nil
  | x :: xs, as, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, as', has, rfl⟩ := h
    refine .cons ?_ (evalExprs_refs s f hf xs as' has)
    have hx : f.module.funcs[x.toNat]? = some a.value := by rw [hf, List.getElem?_map, ha]; rfl
    exact Relation.ReflTransGen.single (Silmaril.Wasm.Execution.Core.Step.reference
      (Silmaril.Wasm.Execution.Core.RefStep.refFunc hx))

theorem evalExprss_elems (s : ToCore.CStore H) (f : ToCore.CFrame) {sL : Store H}
    {module : Runtime.ModuleInst} (hf : f.module.funcs = module.funcs.map (·.value)) :
    {es : List Elem} → {ws : List ElemWrite} →
    List.Forall₂ (fun e w => resolveElem? sL module e = some w) es ws →
    Silmaril.Wasm.Execution.Core.EvalExprss P tgt s f ((es.map Elem.toCore).map Wasm.Elem.init)
      s f (ws.map fun w => w.values.map fun a => .func a.value)
  | [], [], .nil => .nil
  | e :: es, w :: ws, .cons h hs => by
    obtain ⟨-, -, -, -, -, hrefs, -, -⟩ := resolveElem?_inv h
    exact .cons (evalExprs_refs s f hf e.init w.values hrefs) (evalExprss_elems s f hf hs)

end Eval

theorem funcTypes_eq {types : List FuncType} {mod : Runtime.ModuleInst} :
    {fs : List Func} → {fis : List (Runtime.FuncInst Func H)} →
    List.Forall₂ (fun f fi => (types[f.type.toNat]?).bind
      (fun ft => some (Runtime.FuncInst.wasm ft mod f)) = some fi) fs fis →
    (fs.map Func.toCore).mapM (fun fn => (types.map V1.FuncType.toDefType)[fn.type.toNat]?) =
      some (fis.map fun fi => fi.type.toDefType)
  | [], [], .nil => rfl
  | f :: fs, fi :: fis, .cons h hs => by
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ft, hft, rfl⟩ := h
    have ih := funcTypes_eq hs
    simp only [List.getElem?_map] at ih
    simp only [List.map_cons, List.mapM_cons, List.getElem?_map, Func.toCore, hft,
      Option.map_some, Option.pure_def, Option.bind_eq_bind, Option.bind_some, ih]
    rfl

theorem allocExports_eq {EI : ToCore.CModuleInst} {base : Runtime.ModuleInst}
    (hf : EI.funcs = base.funcs.map (·.value)) (ht : EI.tables = base.tables.map (·.value))
    (hm : EI.mems = base.memories.map (·.value)) (hg : EI.globals = base.globals.map (·.value)) :
    (es : List Export) → (xs : List Runtime.ExportInst) →
    es.mapM (fun e => (exportValue? base e.index).bind
      fun v => some (⟨e.name, v⟩ : Runtime.ExportInst)) = some xs →
    (es.map V1.Export.toCore).mapM (Silmaril.Wasm.Execution.Core.allocExport? EI) =
      some (xs.map fun e => ⟨e.name, e.value.toCore⟩)
  | [], xs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | e :: es, xs, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    have ih := allocExports_eq hf ht hm hg es xs' hxs
    obtain ⟨v, hv, rfl⟩ := hx
    have hx' : Silmaril.Wasm.Execution.Core.allocExport? EI (V1.Export.toCore e) =
        some ⟨e.name, v.toCore⟩ := by
      rcases e with ⟨nm, idx⟩
      cases idx with
      | func i =>
        simp only [exportValue?, Option.map_eq_some_iff] at hv
        obtain ⟨a, ha, rfl⟩ := hv
        simp [Silmaril.Wasm.Execution.Core.allocExport?, V1.Export.toCore, V1.ExternIdx.toCore,
          hf, ha, Silmaril.Wasm.Execution.Runtime.ExternVal.toCore]
      | table i =>
        simp only [exportValue?, Option.map_eq_some_iff] at hv
        obtain ⟨a, ha, rfl⟩ := hv
        simp [Silmaril.Wasm.Execution.Core.allocExport?, V1.Export.toCore, V1.ExternIdx.toCore,
          ht, ha, Silmaril.Wasm.Execution.Runtime.ExternVal.toCore]
      | memory i =>
        simp only [exportValue?, Option.map_eq_some_iff] at hv
        obtain ⟨a, ha, rfl⟩ := hv
        simp [Silmaril.Wasm.Execution.Core.allocExport?, V1.Export.toCore, V1.ExternIdx.toCore,
          hm, ha, Silmaril.Wasm.Execution.Runtime.ExternVal.toCore]
      | global i =>
        simp only [exportValue?, Option.map_eq_some_iff] at hv
        obtain ⟨a, ha, rfl⟩ := hv
        simp [Silmaril.Wasm.Execution.Core.allocExport?, V1.Export.toCore, V1.ExternIdx.toCore,
          hg, ha, Silmaril.Wasm.Execution.Runtime.ExternVal.toCore]
    simp only [List.map_cons, List.mapM_cons, hx', ih, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some]

section AllocMany

open Silmaril.Wasm.Execution.Core (allocMany allocMem allocTable allocData allocElem allocFunc)

theorem allocMany_mem (s : ToCore.CStore H) (ms : List Wasm.MemoryType) :
    allocMany allocMem s ms = ({ s with mems := s.mems ++ ms.map fun mt =>
      (⟨mt, ByteArray.mk (Array.replicate (mt.limits.min.val *
        Silmaril.Wasm.Execution.Memory.pageSize) 0)⟩ : Silmaril.Wasm.Execution.Core.MemInst) },
      (List.range ms.length).map (s.mems.length + ·)) :=
  allocMany_eq (·.mems) (fun s l => { s with mems := l }) _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) ms s

theorem allocMany_table (s : ToCore.CStore H)
    (ps : List (Silmaril.Wasm.Validation.CTableType × Silmaril.Wasm.Execution.Core.Ref)) :
    allocMany (fun s p => allocTable s p.1 p.2) s ps = ({ s with tables := s.tables ++ ps.map fun p =>
      (⟨p.1, List.replicate p.1.limits.min.val p.2⟩ : Silmaril.Wasm.Execution.Core.TableInst) },
      (List.range ps.length).map (s.tables.length + ·)) :=
  allocMany_eq (·.tables) (fun s l => { s with tables := l }) _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) ps s

theorem allocMany_data (s : ToCore.CStore H) (bs : List ByteArray) :
    allocMany allocData s bs = ({ s with datas := s.datas ++ bs.map fun b =>
      (⟨b⟩ : Silmaril.Wasm.Execution.Core.DataInst) },
      (List.range bs.length).map (s.datas.length + ·)) :=
  allocMany_eq (·.datas) (fun s l => { s with datas := l }) _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) bs s

theorem allocMany_elem (s : ToCore.CStore H)
    (ps : List (Silmaril.Wasm.Validation.CRefType × List Silmaril.Wasm.Execution.Core.Ref)) :
    allocMany (fun s p => allocElem s p.1 p.2) s ps = ({ s with elems := s.elems ++ ps.map fun p =>
      (⟨p.1, p.2⟩ : Silmaril.Wasm.Execution.Core.ElemInst) },
      (List.range ps.length).map (s.elems.length + ·)) :=
  allocMany_eq (·.elems) (fun s l => { s with elems := l }) _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) ps s

theorem allocMany_func (s : ToCore.CStore H) (mi : ToCore.CModuleInst)
    (ps : List (Silmaril.Wasm.Validation.DefType × Wasm.Func)) :
    allocMany (fun s p => allocFunc s p.1 (.wasm p.2) mi) s ps =
      ({ s with funcs := s.funcs ++ ps.map fun p =>
        (⟨p.1, mi, .wasm p.2⟩ : Silmaril.Wasm.Execution.Core.FuncInst H) },
      (List.range ps.length).map (s.funcs.length + ·)) :=
  allocMany_eq (·.funcs) (fun s l => { s with funcs := l }) _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) ps s

@[simp] theorem allocMany_nil' {α : Type} (alloc : ToCore.CStore H → α → ToCore.CStore H × Nat)
    (s : ToCore.CStore H) : allocMany alloc s [] = (s, []) := rfl

end AllocMany

theorem tables_new_toCore (dts : List Silmaril.Wasm.Validation.DefType) :
    (ts : List TableType) →
    List.map (fun p : Silmaril.Wasm.Validation.CTableType × Silmaril.Wasm.Execution.Core.Ref =>
        (⟨p.1, List.replicate p.1.limits.min.val p.2⟩ : Silmaril.Wasm.Execution.Core.TableInst))
      ((List.map (fun t : Wasm.Table => (⟨t.type.address, t.type.limits,
          Silmaril.Wasm.Validation.Ty.substAll (Silmaril.Wasm.Validation.liftRef t.type.element)
            (dts.map Silmaril.Wasm.Validation.Ty.dt)⟩ : Silmaril.Wasm.Validation.CTableType))
        (List.map tableToCore ts)).zip (List.map (fun _ => Silmaril.Wasm.Execution.Core.Ref.null) ts)) =
    (ts.map fun t => Runtime.TableInst.mk (List.replicate t.limits.min.val none)
      (t.limits.max.map Fin.val)).map Silmaril.Wasm.Execution.Runtime.TableInst.toCore
  | [] => rfl
  | t :: ts => by
    simp only [List.map_cons, List.zip_cons_cons, tables_new_toCore dts ts, List.cons.injEq, and_true]
    have hmin := t.limits.min.isLt
    simp only [Silmaril.Wasm.Execution.Runtime.TableInst.toCore, tableToCore, V1.TableType.toCore,
      V1.Limits.toCore, List.length_replicate, List.map_replicate, V1.widen32, Option.map_map]
    congr 2
    · congr 1
      · apply Fin.ext; simp only [Fin.val_ofNat]; exact (Nat.mod_eq_of_lt (by omega)).symm
      · congr 1; funext b; apply Fin.ext
        have := b.isLt
        simp only [V1.widen32]; exact (Nat.mod_eq_of_lt (by omega)).symm

theorem mems_new_toCore : (ms : List MemoryType) →
    List.map (fun mt : Wasm.MemoryType => (⟨mt, ⟨Array.replicate
        (mt.limits.min.val * Silmaril.Wasm.Execution.Memory.pageSize) 0⟩⟩ :
          Silmaril.Wasm.Execution.Core.MemInst)) (List.map V1.MemoryType.toCore ms) =
    (ms.map fun t => Runtime.MemInst.mk
          ⟨Array.replicate (t.limits.min.val * Silmaril.Wasm.Execution.Memory.pageSize) 0⟩
          (t.limits.max.map Fin.val)).map Silmaril.Wasm.Execution.Runtime.MemInst.toCore
  | [] => rfl
  | t :: ts => by
    simp only [List.map_cons, mems_new_toCore ts, List.cons.injEq, and_true]
    have hmin := t.limits.min.isLt
    have hps : Silmaril.Wasm.Execution.Memory.pageSize > 0 := by
      simp [Silmaril.Wasm.Execution.Memory.pageSize]
    simp only [Silmaril.Wasm.Execution.Runtime.MemInst.toCore, V1.MemoryType.toCore,
      V1.Limits.toCore, V1.widen32, Option.map_map, ByteArray.size, Array.size_replicate,
      Nat.mul_div_cancel _ hps]
    congr 3
    · apply Fin.ext; simp only [Fin.val_ofNat]; exact (Nat.mod_eq_of_lt (by omega)).symm
    · congr 1; funext b; apply Fin.ext
      have := b.isLt
      simp only [V1.widen32]; exact (Nat.mod_eq_of_lt (by omega)).symm

theorem funcs_new_toCore {types : List FuncType} {mod : Runtime.ModuleInst}
    {mi : ToCore.CModuleInst} (hmi : ToCore.ModuleInst.erase mi = mod.toCore) :
    {fs : List Func} → {fis : List (Runtime.FuncInst Func H)} →
    List.Forall₂ (fun f fi => (types[f.type.toNat]?).bind
      (fun ft => some (Runtime.FuncInst.wasm ft mod f)) = some fi) fs fis →
    (List.map (fun p : Silmaril.Wasm.Validation.DefType × Wasm.Func =>
        (⟨p.1, mi, .wasm p.2⟩ : Silmaril.Wasm.Execution.Core.FuncInst H))
      ((fis.map fun fi => fi.type.toDefType).zip (fs.map Func.toCore))).map
      (fun fi => { fi with module := ToCore.ModuleInst.erase fi.module }) =
    fis.map Silmaril.Wasm.Execution.Runtime.FuncInst.toCore
  | [], [], .nil => rfl
  | f :: fs, fi :: fis, .cons h hs => by
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ft, -, rfl⟩ := h
    simp only [List.map_cons, List.zip_cons_cons, funcs_new_toCore hmi hs, List.cons.injEq, and_true]
    simp [Silmaril.Wasm.Execution.Runtime.FuncInst.toCore, hmi,
      Silmaril.Wasm.Execution.Runtime.FuncInst.type]

theorem funcs_before_erase (fs : List (Runtime.FuncInst Func H)) :
    (fs.map Silmaril.Wasm.Execution.Runtime.FuncInst.toCore).map
      (fun fi => { fi with module := ToCore.ModuleInst.erase fi.module }) =
    fs.map Silmaril.Wasm.Execution.Runtime.FuncInst.toCore := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro fi _
  cases fi <;> rfl

theorem globals_before_erase (gs : List Runtime.GlobalInst) :
    (gs.map GlobalInst.toCore).map ToCore.GlobalInst.erase = gs.map GlobalInst.toCore := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro g _
  rfl

theorem allocModule_core {before : Store H} {m : Module} {imports : List Runtime.ExternVal}
    {exports : List Runtime.ExportInst} {funcs : List (Runtime.FuncInst Func H)}
    {refsE : List (List Silmaril.Wasm.Execution.Core.Ref)}
    (hg : m.globals = [])
    (hex : m.exports.mapM (fun e => (exportValue? (baseInst before m imports) e.index).bind
      fun v => some (⟨e.name, v⟩ : Runtime.ExportInst)) = some exports)
    (hfn : m.funcs.mapM (fun f => (m.types[f.type.toNat]?).bind
      fun ft => some (Runtime.FuncInst.wasm ft { baseInst before m imports with exports := exports } f)) =
        some funcs)
    (hlenE : refsE.length = m.elems.length) :
    ∃ Sa mi, Silmaril.Wasm.Execution.Core.allocModule? before.toCore m.toCore
        (imports.map Runtime.ExternVal.toCore) [] (m.tables.map fun _ => .null) refsE =
        some (Sa, mi) ∧
      ToCore.ModuleInst.erase mi =
        ({ baseInst before m imports with exports := exports } : Runtime.ModuleInst).toCore ∧
      mi.elems = List.range m.elems.length ∧ mi.datas = List.range m.data.length ∧
      Sa.elems.map (·.refs) = refsE ∧ Sa.datas.map (·.bytes) = m.data.map (·.bytes) ∧
      Sa.globals = before.toCore.globals ∧
      ToCore.Store.erase Sa = (⟨before.funcs ++ funcs, before.tables ++ m.tables.map (fun t =>
          Runtime.TableInst.mk (List.replicate t.limits.min.val none) (t.limits.max.map Fin.val)),
        before.memories ++ m.memories.map (fun t => Runtime.MemInst.mk
          ⟨Array.replicate (t.limits.min.val * Silmaril.Wasm.Execution.Memory.pageSize) 0⟩
          (t.limits.max.map Fin.val)),
        before.globals⟩ : Store H).toCore := by
  have hT : Silmaril.Wasm.Execution.Core.allocTypes (m.types.map V1.FuncType.toCoreRec) =
      m.types.map V1.FuncType.toDefType :=
    Silmaril.Wasm.Execution.Core.allocTypes_eq (Validation.typesOk_map m.types {})
  have hfn2 := mapM_forall₂ hfn
  have hF := funcTypes_eq hfn2
  simp only [Silmaril.Wasm.Execution.Core.allocModule?, Module.toCore, hg, hT, hF,
    List.mapM_nil, List.map_nil, List.zip_nil_right, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, allocMany_nil', allocMany_mem, allocMany_table, allocMany_data,
    allocMany_elem, allocMany_func]
  rw [allocExports_eq (base := baseInst before m imports) ?_ ?_ ?_ ?_ m.exports exports hex]
  rotate_left
  · simp [baseInst, externAddr_funcs_toCore, addresses, Silmaril.Wasm.Execution.Runtime.Store.toCore,
      Function.comp_def]
  · simp [baseInst, externAddr_tables_toCore, addresses, Silmaril.Wasm.Execution.Runtime.Store.toCore,
      Function.comp_def]
  · simp [baseInst, externAddr_mems_toCore, addresses, Silmaril.Wasm.Execution.Runtime.Store.toCore,
      Function.comp_def]
  · simp [baseInst, externAddr_globals_toCore]
  simp only [Option.bind_some]
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore, baseInst,
      externAddr_funcs_toCore, externAddr_tables_toCore, externAddr_mems_toCore,
      externAddr_globals_toCore, externAddr_tags_toCore, addresses,
      Silmaril.Wasm.Execution.Runtime.Store.toCore, Function.comp_def]
  · simp [Silmaril.Wasm.Execution.Runtime.Store.toCore, hlenE]
  · simp [Silmaril.Wasm.Execution.Runtime.Store.toCore]
  · simp only [Silmaril.Wasm.Execution.Runtime.Store.toCore, List.nil_append, List.map_map]
    exact List.map_snd_zip (by simp [hlenE])
  · simp [Silmaril.Wasm.Execution.Runtime.Store.toCore, Function.comp_def, Data.toCore]
  · simp only [ToCore.Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toCore, List.map_append,
      funcs_before_erase, globals_before_erase, tables_new_toCore, mems_new_toCore]
    rw [funcs_new_toCore ?_ hfn2]
    simp [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore, baseInst,
      externAddr_funcs_toCore, externAddr_tables_toCore, externAddr_mems_toCore,
      externAddr_globals_toCore, externAddr_tags_toCore, addresses,
      Function.comp_def]

/-! ## Segment programs -/

theorem map_modify_eq_set {α β : Type _} {f : α → α} {g : α → β} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : (l.modify i f).map g = (l.map g).set i (g (f a)) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_modify, List.getElem?_set, List.length_map]
  by_cases hij : i = j
  · subst hij
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
    simp [hlt]
  · simp [hij]

theorem drop_modify_succ {α : Type _} (f : α → α) (l : List α) (k : Nat) :
    (l.modify k f).drop (k + 1) = l.drop (k + 1) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_drop]
  rw [List.getElem?_modify_ne _ _ (by omega)]

theorem getElem?_of_drop_eq_cons {α : Type _} {l : List α} {k : Nat} {x : α} {xs : List α}
    (h : l.drop k = x :: xs) : l[k]? = some x := by
  have := congrArg (·[0]?) h
  simpa [List.getElem?_drop] using this

theorem drop_succ_of_drop_eq_cons {α : Type _} {l : List α} {k : Nat} {x : α} {xs : List α}
    (h : l.drop k = x :: xs) : l.drop (k + 1) = xs := by
  rw [← List.drop_drop, h]; rfl

theorem mapM_length_eq {α β : Type _} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.length = xs.length :=
  (mapM_forall₂ h).length_eq.symm

section Phases

variable {P : Profile} {tgt : ToCore.CHostSemantics H}

/-- The Core image of an element write's references. -/
def elemRefs (w : ElemWrite) : List Silmaril.Wasm.Execution.Core.Ref :=
  w.values.map fun a => .func a.value

theorem tableToCore_refs (t : Runtime.TableInst) :
    (Silmaril.Wasm.Execution.Runtime.TableInst.toCore t).refs =
      t.refs.map fun | none => .null | some a => .func a.value := rfl

/-- The table update of an element write. -/
def elemUpd (w : ElemWrite) (table : Runtime.TableInst) : Runtime.TableInst :=
  {table with refs := table.refs.take w.offset ++ w.values.map some ++
    table.refs.drop (w.offset + w.values.length)}

/-- One element segment program. -/
theorem elemSeg_core {L0 L : Store H} {module : Runtime.ModuleInst} {F : ToCore.CFrame}
    {S : ToCore.CStore H} {e : Elem} {w : ElemWrite} {k : Nat}
    (hw : resolveElem? L0 module e = some w)
    (hG : S.globals = L0.globals.map GlobalInst.toCore)
    (hFg : F.module.globals = module.globals.map (·.value))
    (hFt : F.module.tables = module.tables.map (·.value))
    (hFe : F.module.elems[k]? = some k) (hk : k < 2 ^ 32)
    (hSe : (S.elems[k]?).map (·.refs) = some (elemRefs w))
    (hS : ToCore.Store.erase S = L.toCore)
    (hlen : ∀ i : Nat, (L.tables[i]?).map (fun t : Runtime.TableInst => t.refs.length) =
      (L0.tables[i]?).map (fun t : Runtime.TableInst => t.refs.length))
    (htab : ∀ t ∈ L0.tables, t.refs.length < 2 ^ 32)
    (rest : List ToCore.CAdmin) :
    ∃ S', Silmaril.Wasm.Execution.Core.Steps P tgt
        ⟨S, F, Silmaril.Wasm.Execution.Core.expression
          (Silmaril.Wasm.Execution.Core.runElem k e.toCore) ++ rest⟩ ⟨S', F, rest⟩ ∧
      ToCore.Store.erase S' = (applyElem L w).toCore ∧ S'.globals = S.globals ∧
      S'.datas = S.datas ∧ S'.mems = S.mems ∧
      S'.elems = S.elems.modify k (fun e => { e with refs := [] }) := by
  obtain ⟨a, table, hoff, ha, htable, hrefs, hbnd, hwa⟩ := resolveElem?_inv hw
  have hvlen : w.values.length = e.init.length := mapM_length_eq hrefs
  -- the Lime1 table currently at `a`
  have hl := hlen a.value
  rw [htable] at hl
  obtain ⟨tL, htL, htLlen⟩ : ∃ tL, L.tables[a.value]? = some tL ∧
      tL.refs.length = table.refs.length := by
    cases h : L.tables[a.value]? with
    | none => rw [h] at hl; cases hl
    | some tL => rw [h] at hl; exact ⟨tL, rfl, Option.some.inj hl⟩
  have htbl0 : table.refs.length < 2 ^ 32 := htab _ (List.mem_of_getElem? htable)
  have hStab : S.tables = L.tables.map Silmaril.Wasm.Execution.Runtime.TableInst.toCore := by
    have := congrArg Silmaril.Wasm.Execution.Core.Store.tables hS
    simpa [ToCore.Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toCore] using this
  have hta : S.table? F e.table = some (a.value, tL.toCore) := by
    simp [Silmaril.Wasm.Execution.Core.Store.table?, hFt, ha, hStab, htL]
  obtain ⟨ei, hei, heir⟩ : ∃ ei, S.elems[k]? = some ei ∧ ei.refs = elemRefs w := by
    cases h : S.elems[k]? with
    | none => rw [h] at hSe; cases hSe
    | some ei => rw [h] at hSe; exact ⟨ei, rfl, Option.some.inj hSe⟩
  have hxe : (⟨Fin.ofNat _ k⟩ : ElemIdx).toNat = k := by
    show (Fin.ofNat (2 ^ 32) k).val = k
    rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hk
  have hel : S.elem? F ⟨Fin.ofNat _ k⟩ = some (k, ei) := by
    simp only [Silmaril.Wasm.Execution.Core.Store.elem?]
    rw [hxe, hFe]; simp [hei]
  obtain ⟨x, hx, hsx⟩ := offset_core (P := P) (tgt := tgt) (S := S) (F := F) hG hFg hoff
    ([.plain (.intConst .i32 0), .plain (.intConst .i32 (BitVec.ofNat 32 e.init.length)),
      .plain (.tableInit e.table ⟨Fin.ofNat _ k⟩), .plain (.elemDrop ⟨Fin.ofNat _ k⟩)] ++ rest)
  have htlen : tL.toCore.refs.length = table.refs.length := by
    simp [tableToCore_refs, htLlen]
  have heilen : ei.refs.length = e.init.length := by simp [heir, elemRefs, hvlen]
  have hti := tableInit_core (P := P) (tgt := tgt) (F := F) (x := e.table)
    (y := ⟨Fin.ofNat _ k⟩) e.init.length S a.value tL.toCore x 0 hta hel
    (by rw [htlen]; exact htbl0) (by rw [heilen, ← hvlen]; omega)
    (by rw [hx, htlen, ← hvlen]; exact hbnd) (by rw [heilen]; simp)
    ([.plain (.elemDrop ⟨Fin.ofNat _ k⟩)] ++ rest)
  let ti' : Silmaril.Wasm.Execution.Core.TableInst := ⟨tL.toCore.type,
    tL.toCore.refs.take x.toNat ++ (ei.refs.drop (0 : BitVec 32).toNat).take e.init.length ++
      tL.toCore.refs.drop (x.toNat + e.init.length)⟩
  have hdrop := Silmaril.Wasm.Execution.Core.Step.table (P := P) (host := tgt)
    (Silmaril.Wasm.Execution.Core.TableStep.elemDrop (s := S.setTable a.value ti') (f := F)
      (by rw [elem?_setTable]; exact hel))
  have hdrop' := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs (vs := []) (rest := rest)
    (Relation.ReflTransGen.single hdrop)
  refine ⟨(S.setTable a.value ti').setElem k [], ?_, ?_, rfl, rfl, rfl, rfl⟩
  · have e1 := hsx
    simp only [Silmaril.Wasm.Execution.Core.vals, List.map_nil, List.nil_append] at hdrop'
    have e2 : Silmaril.Wasm.Execution.Core.expression
        (Silmaril.Wasm.Execution.Core.runElem k e.toCore) =
        Silmaril.Wasm.Execution.Core.expression (Expr.toCore e.offset) ++
        [.plain (.intConst .i32 0), .plain (.intConst .i32 (BitVec.ofNat 32 e.init.length)),
          .plain (.tableInit e.table ⟨Fin.ofNat _ k⟩), .plain (.elemDrop ⟨Fin.ofNat _ k⟩)] := by
      simp [Silmaril.Wasm.Execution.Core.runElem, Elem.toCore, Silmaril.Wasm.Execution.Core.expression]
    rw [e2, List.append_assoc]
    refine e1.trans (Relation.ReflTransGen.trans ?_ hdrop')
    exact hti
  · -- the store relation
    have hmod := map_modify_eq_set (f := elemUpd w)
      (g := Silmaril.Wasm.Execution.Runtime.TableInst.toCore) htL
    have hti' : Silmaril.Wasm.Execution.Runtime.TableInst.toCore (elemUpd w tL) = ti' := by
      have hl2 : (tL.refs.take w.offset ++ w.values.map some ++
          tL.refs.drop (w.offset + w.values.length)).length = tL.refs.length := by
        simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
        omega
      simp only [ti', elemUpd, Silmaril.Wasm.Execution.Runtime.TableInst.toCore, hl2]
      congr 1
      simp only [List.map_append, List.map_take, List.map_drop, List.map_map, hx, heir]
      rw [show (0 : BitVec 32).toNat = 0 from rfl, List.drop_zero,
        List.take_of_length_le (show (elemRefs w).length ≤ e.init.length by simp [elemRefs, hvlen])]
      simp [elemRefs, Function.comp_def, hvlen]
    rw [hti'] at hmod
    have hSe' : ToCore.Store.erase ((S.setTable a.value ti').setElem k []) =
        { ToCore.Store.erase S with tables := S.tables.set a.value ti' } := rfl
    rw [hSe', hS, hStab, ← hmod]
    subst hwa
    rfl

/-- One data segment program. -/
theorem dataSeg_core {Lb L : Store H} {module : Runtime.ModuleInst} {F : ToCore.CFrame}
    {S : ToCore.CStore H} {d : Data} {w : DataWrite} {k : Nat}
    (hw : resolveData? Lb module d = some w)
    (hG : S.globals = Lb.globals.map GlobalInst.toCore)
    (hFg : F.module.globals = module.globals.map (·.value))
    (hFm : F.module.mems = module.memories.map (·.value))
    (hFd : F.module.datas[k]? = some k) (hk : k < 2 ^ 32)
    (hSd : (S.datas[k]?).map (·.bytes) = some d.bytes)
    (hS : ToCore.Store.erase S = L.toCore)
    (hlen : ∀ i : Nat, (L.memories[i]?).map (fun t : Runtime.MemInst => t.data.size) =
      (Lb.memories[i]?).map (fun t : Runtime.MemInst => t.data.size))
    (hmem : ∀ t ∈ Lb.memories, t.data.size ≤ 2 ^ 32)
    (hdb : d.bytes.size < 2 ^ 32)
    (rest : List ToCore.CAdmin) :
    ∃ S', Silmaril.Wasm.Execution.Core.Steps P tgt
        ⟨S, F, Silmaril.Wasm.Execution.Core.expression
          (Silmaril.Wasm.Execution.Core.runData k d.toCore) ++ rest⟩ ⟨S', F, rest⟩ ∧
      ToCore.Store.erase S' = (applyData L w).toCore ∧ S'.globals = S.globals ∧
      S'.datas = S.datas.modify k (fun _ => ⟨ByteArray.empty⟩) := by
  obtain ⟨a, memory, hoff, ha, hmemA, hwb, hbnd, hwa⟩ := resolveData?_inv hw
  have hl := hlen a.value
  rw [hmemA] at hl
  obtain ⟨mL, hmL, hmLlen⟩ : ∃ mL, L.memories[a.value]? = some mL ∧
      mL.data.size = memory.data.size := by
    cases h : L.memories[a.value]? with
    | none => rw [h] at hl; cases hl
    | some mL => rw [h] at hl; exact ⟨mL, rfl, Option.some.inj hl⟩
  have hm0 : memory.data.size ≤ 2 ^ 32 := hmem _ (List.mem_of_getElem? hmemA)
  have hSmem : S.mems = L.memories.map Silmaril.Wasm.Execution.Runtime.MemInst.toCore := by
    have := congrArg Silmaril.Wasm.Execution.Core.Store.mems hS
    simpa [ToCore.Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toCore] using this
  have hma : S.mem? F d.memory = some (a.value, mL.toCore) := by
    simp [Silmaril.Wasm.Execution.Core.Store.mem?, hFm, ha, hSmem, hmL]
  obtain ⟨di, hdi, hdib⟩ : ∃ di, S.datas[k]? = some di ∧ di.bytes = d.bytes := by
    cases h : S.datas[k]? with
    | none => rw [h] at hSd; cases hSd
    | some di => rw [h] at hSd; exact ⟨di, rfl, Option.some.inj hSd⟩
  have hxd : (⟨Fin.ofNat _ k⟩ : DataIdx).toNat = k := by
    show (Fin.ofNat (2 ^ 32) k).val = k
    rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hk
  have hda : S.data? F ⟨Fin.ofNat _ k⟩ = some (k, di) := by
    simp only [Silmaril.Wasm.Execution.Core.Store.data?]
    rw [hxd, hFd]; simp [hdi]
  obtain ⟨x, hx, hsx⟩ := offset_core (P := P) (tgt := tgt) (S := S) (F := F) hG hFg hoff
    ([.plain (.intConst .i32 0), .plain (.intConst .i32 (BitVec.ofNat 32 d.bytes.size)),
      .plain (.memoryInit d.memory ⟨Fin.ofNat _ k⟩), .plain (.dataDrop ⟨Fin.ofNat _ k⟩)] ++ rest)
  have hmsz : mL.toCore.bytes.size = memory.data.size := by
    simp [Silmaril.Wasm.Execution.Runtime.MemInst.toCore, hmLlen]
  have hmi := memInit_core (P := P) (tgt := tgt) (F := F) (x := d.memory)
    (y := ⟨Fin.ofNat _ k⟩) d.bytes.size S a.value mL.toCore x 0 hma hda
    (by rw [hmsz]; exact hm0) (by rw [hdib]; exact hdb)
    (by rw [hx, hmsz]; exact hbnd) (by rw [hdib]; simp)
    ([.plain (.dataDrop ⟨Fin.ofNat _ k⟩)] ++ rest)
  let mi' : Silmaril.Wasm.Execution.Core.MemInst := { mL.toCore with bytes :=
    ⟨(mL.toCore.bytes.data.toList.take x.toNat ++
      (di.bytes.data.toList.drop (0 : BitVec 32).toNat).take d.bytes.size ++
      mL.toCore.bytes.data.toList.drop (x.toNat + d.bytes.size)).toArray⟩ }
  have hdrop := Silmaril.Wasm.Execution.Core.Step.memory (P := P) (host := tgt)
    (Silmaril.Wasm.Execution.Core.MemoryStep.dataDrop (s := S.setMem a.value mi') (f := F)
      (by rw [data?_setMem]; exact hda))
  have hdrop' := Silmaril.Wasm.Execution.Core.Steps.ctxtInstrs (vs := []) (rest := rest)
    (Relation.ReflTransGen.single hdrop)
  refine ⟨(S.setMem a.value mi').setData k ByteArray.empty, ?_, ?_, rfl, rfl⟩
  · simp only [Silmaril.Wasm.Execution.Core.vals, List.map_nil, List.nil_append] at hdrop'
    have e2 : Silmaril.Wasm.Execution.Core.expression
        (Silmaril.Wasm.Execution.Core.runData k d.toCore) =
        Silmaril.Wasm.Execution.Core.expression (Expr.toCore d.offset) ++
        [.plain (.intConst .i32 0), .plain (.intConst .i32 (BitVec.ofNat 32 d.bytes.size)),
          .plain (.memoryInit d.memory ⟨Fin.ofNat _ k⟩), .plain (.dataDrop ⟨Fin.ofNat _ k⟩)] := by
      simp [Silmaril.Wasm.Execution.Core.runData, Data.toCore, Silmaril.Wasm.Execution.Core.expression]
    rw [e2, List.append_assoc]
    exact hsx.trans (Relation.ReflTransGen.trans hmi hdrop')
  · have hbnd' : w.offset + w.bytes.size ≤ mL.data.size := by rw [hwb, hmLlen]; exact hbnd
    have hmod := map_modify_eq_set
      (f := fun memory : Runtime.MemInst =>
        {memory with data := w.bytes.copySlice 0 memory.data w.offset w.bytes.size})
      (g := Silmaril.Wasm.Execution.Runtime.MemInst.toCore) hmL
    have hmi' : Silmaril.Wasm.Execution.Runtime.MemInst.toCore
        {mL with data := w.bytes.copySlice 0 mL.data w.offset w.bytes.size} = mi' := by
      have hsz := copySlice_size hbnd'
      simp only [mi', Silmaril.Wasm.Execution.Runtime.MemInst.toCore, hsz]
      congr 1
      apply ByteArray.ext
      apply Array.ext'
      rw [copySlice_toList rfl hbnd']
      simp only [hx, hdib, hwb, show (0 : BitVec 32).toNat = 0 from rfl, List.drop_zero]
      rw [List.take_of_length_le (l := d.bytes.data.toList)
        (by rw [Array.length_toList]; exact le_refl _)]
    rw [hmi'] at hmod
    have hSe' : ToCore.Store.erase ((S.setMem a.value mi').setData k ByteArray.empty) =
        { ToCore.Store.erase S with mems := S.mems.set a.value mi' } := rfl
    rw [hSe', hS, hSmem, ← hmod]
    subst hwa
    rfl

theorem applyElem_len {L0 L : Store H} {module : Runtime.ModuleInst} {e : Elem} {w : ElemWrite}
    (hw : resolveElem? L0 module e = some w)
    (hlen : ∀ i : Nat, (L.tables[i]?).map (fun t : Runtime.TableInst => t.refs.length) =
      (L0.tables[i]?).map (fun t : Runtime.TableInst => t.refs.length)) :
    ∀ i : Nat, ((applyElem L w).tables[i]?).map (fun t : Runtime.TableInst => t.refs.length) =
      (L0.tables[i]?).map (fun t : Runtime.TableInst => t.refs.length) := by
  obtain ⟨a, table, -, -, htable, -, hbnd, hwa⟩ := resolveElem?_inv hw
  subst hwa
  intro i
  rw [← hlen i]
  simp only [applyElem, List.getElem?_modify]
  split
  · next heq =>
    subst heq
    have h' := hlen w.address.value
    rw [htable] at h'
    cases hc : L.tables[w.address.value]? with
    | none => simp
    | some t =>
      rw [hc] at h'
      simp only [Option.map_some, Option.some.injEq] at h'
      simp only [Functor.map, Option.map_some, Option.some.injEq, List.length_append,
        List.length_take, List.length_map, List.length_drop]
      omega
  · simp

theorem applyData_len {Lb L : Store H} {module : Runtime.ModuleInst} {d : Data} {w : DataWrite}
    (hw : resolveData? Lb module d = some w)
    (hlen : ∀ i : Nat, (L.memories[i]?).map (fun t : Runtime.MemInst => t.data.size) =
      (Lb.memories[i]?).map (fun t : Runtime.MemInst => t.data.size)) :
    ∀ i : Nat, ((applyData L w).memories[i]?).map (fun t : Runtime.MemInst => t.data.size) =
      (Lb.memories[i]?).map (fun t : Runtime.MemInst => t.data.size) := by
  obtain ⟨a, memory, -, -, hmemA, hwb, hbnd, hwa⟩ := resolveData?_inv hw
  subst hwa
  intro i
  rw [← hlen i]
  simp only [applyData, List.getElem?_modify]
  split
  · next heq =>
    subst heq
    have h' := hlen w.address.value
    rw [hmemA] at h'
    cases hc : L.memories[w.address.value]? with
    | none => simp
    | some t =>
      rw [hc] at h'
      simp only [Option.map_some, Option.some.injEq] at h'
      simp only [Functor.map, Option.map_some, Option.some.injEq]
      exact copySlice_size (by rw [hwb, h']; exact hbnd)
  · simp

/-- The element segment programs. -/
theorem elemLoop_core {L0 : Store H} {module : Runtime.ModuleInst} {F : ToCore.CFrame}
    (hFg : F.module.globals = module.globals.map (·.value))
    (hFt : F.module.tables = module.tables.map (·.value))
    (htab : ∀ t ∈ L0.tables, t.refs.length < 2 ^ 32) :
    (es : List Elem) → (ws : List ElemWrite) → (k : Nat) → (S : ToCore.CStore H) →
    (L : Store H) →
    List.Forall₂ (fun e w => resolveElem? L0 module e = some w) es ws →
    k + es.length ≤ 2 ^ 32 →
    (∀ i, i < es.length → F.module.elems[k + i]? = some (k + i)) →
    (∀ i, i < es.length → (S.elems[k + i]?).map (·.refs) = (ws[i]?).map elemRefs) →
    S.globals = L0.globals.map GlobalInst.toCore →
    ToCore.Store.erase S = L.toCore →
    (∀ i : Nat, (L.tables[i]?).map (fun t : Runtime.TableInst => t.refs.length) =
      (L0.tables[i]?).map (fun t : Runtime.TableInst => t.refs.length)) →
    (rest : List ToCore.CAdmin) →
    ∃ S', Silmaril.Wasm.Execution.Core.Steps P tgt
        ⟨S, F, Silmaril.Wasm.Execution.Core.expression
          (((List.range' k es.length).zip (es.map Elem.toCore)).flatMap fun (i, e) =>
            Silmaril.Wasm.Execution.Core.runElem i e) ++ rest⟩ ⟨S', F, rest⟩ ∧
      ToCore.Store.erase S' = (ws.foldl applyElem L).toCore ∧ S'.globals = S.globals ∧
      S'.datas = S.datas ∧ S'.mems = S.mems
  | [], [], _, S, _, .nil, _, _, _, _, hS, _, rest =>
    ⟨S, by simpa [Silmaril.Wasm.Execution.Core.expression] using Relation.ReflTransGen.refl,
      hS, rfl, rfl, rfl⟩
  | e :: es, w :: ws, k, S, L, .cons hw hws, hk, hFe, hSe, hG, hS, hlen, rest => by
    simp only [List.length_cons] at hk
    obtain ⟨S1, h1, hS1, hG1, hD1, hM1, hE1⟩ := elemSeg_core (P := P) (tgt := tgt) (k := k)
      hw hG hFg hFt (by simpa using hFe 0 (by simp)) (by omega)
      (by simpa using hSe 0 (by simp)) hS hlen htab
      (Silmaril.Wasm.Execution.Core.expression
        (((List.range' (k + 1) es.length).zip (es.map Elem.toCore)).flatMap fun (i, e) =>
          Silmaril.Wasm.Execution.Core.runElem i e) ++ rest)
    obtain ⟨S2, h2, hS2, hG2, hD2, hM2⟩ := elemLoop_core hFg hFt htab es ws (k + 1) S1
      (applyElem L w) hws (by omega)
      (fun i hi => by
        have := hFe (i + 1) (by simp; omega)
        rwa [show k + (i + 1) = k + 1 + i by omega] at this)
      (fun i hi => by
        rw [hE1, List.getElem?_modify_ne _ _ (by omega)]
        have := hSe (i + 1) (by simp; omega)
        rw [show k + (i + 1) = k + 1 + i by omega] at this
        simpa using this)
      (hG1.trans hG) hS1 (applyElem_len hw hlen) rest
    refine ⟨S2, ?_, hS2, hG2.trans hG1, hD2.trans hD1, hM2.trans hM1⟩
    have e1 : Silmaril.Wasm.Execution.Core.expression
        (((List.range' k (e :: es).length).zip ((e :: es).map Elem.toCore)).flatMap fun (i, e) =>
          Silmaril.Wasm.Execution.Core.runElem i e) ++ rest =
        Silmaril.Wasm.Execution.Core.expression (Silmaril.Wasm.Execution.Core.runElem k e.toCore) ++
        (Silmaril.Wasm.Execution.Core.expression
          (((List.range' (k + 1) es.length).zip (es.map Elem.toCore)).flatMap fun (i, e) =>
            Silmaril.Wasm.Execution.Core.runElem i e) ++ rest) := by
      simp [Silmaril.Wasm.Execution.Core.expression, List.range'_succ]
    rw [e1]
    exact h1.trans h2

/-- The data segment programs. -/
theorem dataLoop_core {Lb : Store H} {module : Runtime.ModuleInst} {F : ToCore.CFrame}
    (hFg : F.module.globals = module.globals.map (·.value))
    (hFm : F.module.mems = module.memories.map (·.value))
    (hmem : ∀ t ∈ Lb.memories, t.data.size ≤ 2 ^ 32) :
    (ds : List Data) → (ws : List DataWrite) → (k : Nat) → (S : ToCore.CStore H) →
    (L : Store H) →
    List.Forall₂ (fun d w => resolveData? Lb module d = some w) ds ws →
    (∀ d ∈ ds, d.bytes.size < 2 ^ 32) →
    k + ds.length ≤ 2 ^ 32 →
    (∀ i, i < ds.length → F.module.datas[k + i]? = some (k + i)) →
    (∀ i, i < ds.length → (S.datas[k + i]?).map (·.bytes) = (ds[i]?).map (·.bytes)) →
    S.globals = Lb.globals.map GlobalInst.toCore →
    ToCore.Store.erase S = L.toCore →
    (∀ i : Nat, (L.memories[i]?).map (fun t : Runtime.MemInst => t.data.size) =
      (Lb.memories[i]?).map (fun t : Runtime.MemInst => t.data.size)) →
    (rest : List ToCore.CAdmin) →
    ∃ S', Silmaril.Wasm.Execution.Core.Steps P tgt
        ⟨S, F, Silmaril.Wasm.Execution.Core.expression
          (((List.range' k ds.length).zip (ds.map Data.toCore)).flatMap fun (i, d) =>
            Silmaril.Wasm.Execution.Core.runData i d) ++ rest⟩ ⟨S', F, rest⟩ ∧
      ToCore.Store.erase S' = (ws.foldl applyData L).toCore
  | [], [], _, S, _, .nil, _, _, _, _, _, hS, _, rest =>
    ⟨S, by simpa [Silmaril.Wasm.Execution.Core.expression] using Relation.ReflTransGen.refl, hS⟩
  | d :: ds, w :: ws, k, S, L, .cons hw hws, hdb, hk, hFd, hSd, hG, hS, hlen, rest => by
    simp only [List.length_cons] at hk
    obtain ⟨S1, h1, hS1, hG1, hD1⟩ := dataSeg_core (P := P) (tgt := tgt) (k := k)
      hw hG hFg hFm (by simpa using hFd 0 (by simp)) (by omega)
      (by simpa using hSd 0 (by simp)) hS hlen hmem (hdb d (by simp))
      (Silmaril.Wasm.Execution.Core.expression
        (((List.range' (k + 1) ds.length).zip (ds.map Data.toCore)).flatMap fun (i, d) =>
          Silmaril.Wasm.Execution.Core.runData i d) ++ rest)
    obtain ⟨S2, h2, hS2⟩ := dataLoop_core hFg hFm hmem ds ws (k + 1) S1
      (applyData L w) hws (fun d' hd' => hdb d' (by simp [hd'])) (by omega)
      (fun i hi => by
        have := hFd (i + 1) (by simp; omega)
        rwa [show k + (i + 1) = k + 1 + i by omega] at this)
      (fun i hi => by
        rw [hD1, List.getElem?_modify_ne _ _ (by omega)]
        have := hSd (i + 1) (by simp; omega)
        rw [show k + (i + 1) = k + 1 + i by omega] at this
        simpa using this)
      (hG1.trans hG) hS1 (applyData_len hw hlen) rest
    refine ⟨S2, ?_, hS2⟩
    have e1 : Silmaril.Wasm.Execution.Core.expression
        (((List.range' k (d :: ds).length).zip ((d :: ds).map Data.toCore)).flatMap fun (i, d) =>
          Silmaril.Wasm.Execution.Core.runData i d) ++ rest =
        Silmaril.Wasm.Execution.Core.expression (Silmaril.Wasm.Execution.Core.runData k d.toCore) ++
        (Silmaril.Wasm.Execution.Core.expression
          (((List.range' (k + 1) ds.length).zip (ds.map Data.toCore)).flatMap fun (i, d) =>
            Silmaril.Wasm.Execution.Core.runData i d) ++ rest) := by
      simp [Silmaril.Wasm.Execution.Core.expression, List.range'_succ]
    rw [e1]
    exact h1.trans h2

end Phases

/-! ## Preparation is Core instantiation followed by the segment programs -/

/-- The Core start code of a module. -/
def startCode (m : Wasm.Module) : List ToCore.CAdmin :=
  match m.start with
  | some x => [.plain (.call x)]
  | none => []

/-- Core instantiation, followed by the element and data segment programs, reaches
the start code on a store whose erasure is the image of the prepared Lime1 store. -/
theorem prepare_core {tgt : ToCore.CHostSemantics H} {before : Store H} {m : Module}
    {imports : List Runtime.ExternVal} {p : Prepared H}
    (bounds : InstantiationBounds before m) (hv : Validation.ModuleValid m)
    (hi : ImportsMatch before m imports) (hp : prepare? before m imports = some p) :
    ∃ c S, Silmaril.Wasm.Execution.Core.Instantiate coreProfile tgt before.toCore m.toCore
        (imports.map Runtime.ExternVal.toCore) c ∧
      Silmaril.Wasm.Execution.Core.Steps coreProfile tgt c ⟨S, c.frame, startCode m.toCore⟩ ∧
      ToCore.Store.erase S = p.store.toCore ∧ ToCore.ModuleInstSim p.module c.frame.module ∧
      c.frame.locals = [] := by
  have hg := bounds.noGlobals
  obtain ⟨allocated, elems, data, ha, he, hd, hst⟩ := prepare?_inv hp
  obtain ⟨exports, funcs, hex, hfn, hmod, halloc⟩ := allocate?_inv hg ha
  have he2 := mapM_forall₂ he
  have hd2 := mapM_forall₂ hd
  obtain ⟨Sa, mi, hAM, hmi, hmiE, hmiD, hSaE, hSaD, hSaG, hSaS⟩ :=
    allocModule_core (refsE := elems.map elemRefs) hg hex hfn
      (by rw [List.length_map]; exact he2.length_eq.symm)
  -- the frame module
  have hFg : mi.globals = p.module.globals.map (·.value) := by
    have := congrArg (·.globals) hmi
    rw [hmod]
    simpa [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore] using this
  have hFt : mi.tables = p.module.tables.map (·.value) := by
    have := congrArg (·.tables) hmi
    rw [hmod]
    simpa [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore] using this
  have hFm : mi.mems = p.module.memories.map (·.value) := by
    have := congrArg (·.mems) hmi
    rw [hmod]
    simpa [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore] using this
  -- the initial store
  have hG0 : Sa.globals = allocated.globals.map GlobalInst.toCore := by
    rw [hSaG, halloc]; rfl
  have hS0 : ToCore.Store.erase Sa = allocated.toCore := by rw [hSaS, halloc]
  have htab : ∀ t ∈ allocated.tables, t.refs.length < 2 ^ 32 := by
    rw [halloc]
    intro t ht
    simp only [List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨tt, -, rfl⟩
    · exact bounds.tables t ht
    · simp only [List.length_replicate]; exact tt.limits.min.isLt
  have hmem : ∀ t ∈ allocated.memories, t.data.size ≤ 2 ^ 32 := by
    rw [halloc]
    intro t ht
    simp only [List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨mt, hmt, rfl⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
      exact (bounds.storeWF.2 i t hi).1
    · have hvt := (hv.memories mt hmt).1
      simp only [ByteArray.size, Array.size_replicate, Silmaril.Wasm.Execution.Memory.pageSize]
      omega
  -- element segments
  obtain ⟨S1, h1, hS1, hG1, hD1, -⟩ := elemLoop_core (P := coreProfile) (tgt := tgt)
    (F := { module := mi }) hFg hFt htab m.elems elems 0 Sa allocated he2
    (by simpa using bounds.elemCount)
    (fun i hi => by simp [hmiE, List.getElem?_range hi])
    (fun i hi => by
      have := congrArg (·[i]?) hSaE
      simpa [List.getElem?_map] using this)
    hG0 hS0 (fun _ => rfl)
    (Silmaril.Wasm.Execution.Core.expression
      (((List.range' 0 m.data.length).zip (m.data.map Data.toCore)).flatMap fun (i, d) =>
        Silmaril.Wasm.Execution.Core.runData i d) ++ startCode m.toCore)
  -- data segments
  obtain ⟨S2, h2, hS2⟩ := dataLoop_core (P := coreProfile) (tgt := tgt)
    (F := { module := mi }) hFg hFm hmem m.data data 0 S1 (elems.foldl applyElem allocated) hd2
    bounds.data (by simpa using bounds.dataCount)
    (fun i hi => by simp [hmiD, List.getElem?_range hi])
    (fun i hi => by
      have := congrArg (·[i]?) hSaD
      rw [hD1]
      simpa [List.getElem?_map] using this)
    (hG1.trans hG0) hS1 (fun i => by rw [foldl_applyElem_memories]) (startCode m.toCore)
  have hinst : Silmaril.Wasm.Execution.Core.Instantiate coreProfile tgt before.toCore m.toCore
      (imports.map Runtime.ExternVal.toCore) ⟨Sa, { module := mi },
        Silmaril.Wasm.Execution.Core.expression
          (((List.range m.toCore.elems.length).zip m.toCore.elems).flatMap fun (i, e) =>
            Silmaril.Wasm.Execution.Core.runElem i e) ++
        Silmaril.Wasm.Execution.Core.expression
          (((List.range m.toCore.data.length).zip m.toCore.data).flatMap fun (i, d) =>
            Silmaril.Wasm.Execution.Core.runData i d) ++
        (match m.toCore.start with | some x => [.plain (.call x)] | none => [])⟩ := by
    refine ⟨instantiate_valid bounds hv hi, ⟨by simpa [Module.toCore] using bounds.elemCount,
      by simpa [Module.toCore] using bounds.dataCount,
      by simpa [Module.toCore, Data.toCore] using bounds.data,
      by simpa [Module.toCore, Elem.toCore] using bounds.elemSize⟩, ?_⟩
    let mi0 := Silmaril.Wasm.Execution.Core.ModuleInst.initial before.toCore m.toCore
      (imports.map Runtime.ExternVal.toCore)
    let f0 : ToCore.CFrame := { module := mi0 }
    refine ⟨before.toCore, before.toCore, before.toCore, Sa, f0, f0, f0, [],
      m.tables.map fun _ => .null, elems.map elemRefs, mi, ?_, ?_, ?_, hAM, rfl⟩
    · simp only [Module.toCore, hg, List.map_nil]; exact .nil
    · exact evalExprs_tables _ _ m.tables
    · have hf0 : (Silmaril.Wasm.Execution.Core.ModuleInst.initial before.toCore m.toCore
          (imports.map Runtime.ExternVal.toCore)).funcs = p.module.funcs.map (·.value) := by
        rw [hmod]
        simp [Silmaril.Wasm.Execution.Core.ModuleInst.initial, baseInst, externAddr_funcs_toCore,
          addresses, Silmaril.Wasm.Execution.Runtime.Store.toCore, Module.toCore, Function.comp_def]
      exact evalExprss_elems _ f0 hf0 he2
  refine ⟨_, S2, hinst, ?_, ?_, ?_, rfl⟩
  · have e1 : Silmaril.Wasm.Execution.Core.expression
          (((List.range m.toCore.elems.length).zip m.toCore.elems).flatMap fun (i, e) =>
            Silmaril.Wasm.Execution.Core.runElem i e) ++
        Silmaril.Wasm.Execution.Core.expression
          (((List.range m.toCore.data.length).zip m.toCore.data).flatMap fun (i, d) =>
            Silmaril.Wasm.Execution.Core.runData i d) ++
        (match m.toCore.start with | some x => [.plain (.call x)] | none => []) =
        Silmaril.Wasm.Execution.Core.expression
          (((List.range' 0 m.elems.length).zip (m.elems.map Elem.toCore)).flatMap fun (i, e) =>
            Silmaril.Wasm.Execution.Core.runElem i e) ++
        (Silmaril.Wasm.Execution.Core.expression
          (((List.range' 0 m.data.length).zip (m.data.map Data.toCore)).flatMap fun (i, d) =>
            Silmaril.Wasm.Execution.Core.runData i d) ++ startCode m.toCore) := by
      simp only [Module.toCore, List.length_map, List.range_eq_range', List.append_assoc]
      rfl
    show Silmaril.Wasm.Execution.Core.Steps coreProfile tgt ⟨Sa, { module := mi }, _⟩ _
    rw [e1]
    exact h1.trans h2
  · rw [hS2, hst]
  · show ToCore.ModuleInst.erase mi = p.module.toCore
    rw [hmod]; exact hmi

/-- The Lime1 start code is `[]` or `[.invoke a]` for the start function's address. -/
theorem prepare_start {before : Store H} {m : Module}
    {imports : List Runtime.ExternVal} {p : Prepared H}
    (hp : prepare? before m imports = some p) :
    (m.start = none ∧ p.start = []) ∨
      ∃ i a, m.start = some i ∧ p.module.funcs[i.toNat]? = some a ∧ p.start = [.invoke a] := by
  simp only [prepare?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨⟨allocated, module⟩, halloc, elems, -, data, -, hp⟩ := hp
  cases hs : m.start with
  | none =>
    simp only [hs, Option.bind_some, Option.pure_def, Option.some.injEq] at hp
    subst hp
    exact Or.inl ⟨rfl, rfl⟩
  | some i =>
    simp only [hs, Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hp
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hp
    exact Or.inr ⟨i, a, rfl, ha, rfl⟩

theorem forall₂_getElem?_right {α β : Type _} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {i : Nat} {b : β} (hb : l₂[i]? = some b) :
    ∃ a, l₁[i]? = some a ∧ R a b := by
  induction h generalizing i with
  | nil => simp at hb
  | cons hr _ ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hb ⊢; subst hb; exact ⟨_, rfl, hr⟩
    | succ i => simpa using ih (by simpa using hb)

theorem importedInstance_funcs_lt {before : Store H} {m : Module}
    {imports : List Runtime.ExternVal} (hi : ImportsMatch before m imports)
    {a : Silmaril.Wasm.Execution.Runtime.FuncAddr} (ha : a ∈ (importedInstance imports).funcs) :
    a.value < before.funcs.length := by
  simp only [importedInstance, List.mem_filterMap] at ha
  obtain ⟨e, he, hea⟩ := ha
  obtain ⟨i, -, et, -, hm⟩ := forall₂_mem_right hi he
  cases e with
  | func a' =>
    simp only [Option.some.injEq] at hea
    subst hea
    cases hm with
    | func _ fn _ found _ => exact (List.getElem?_eq_some_iff.mp found).1
  | table _ => simp at hea
  | memory _ => simp at hea
  | global _ => simp at hea

theorem baseInst_funcs_lt {before : Store H} {m : Module}
    {imports : List Runtime.ExternVal} (hi : ImportsMatch before m imports)
    {a : Silmaril.Wasm.Execution.Runtime.FuncAddr} (ha : a ∈ (baseInst before m imports).funcs) :
    a.value < before.funcs.length + m.funcs.length := by
  simp only [baseInst, List.mem_append] at ha
  rcases ha with ha | ha
  · have := importedInstance_funcs_lt hi ha; omega
  · simp only [addresses, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    simp only; omega

/-- The prepared Lime1 configuration is well formed. -/
theorem prepare_wf {before : Store H} {m : Module}
    {imports : List Runtime.ExternVal} {p : Prepared H}
    (bounds : InstantiationBounds before m) (hv : Validation.ModuleValid m)
    (hi : ImportsMatch before m imports) (hp : prepare? before m imports = some p) :
    ConfigWF (⟨p.store, ⟨[], p.module⟩, p.start⟩ : Config H) := by
  obtain ⟨allocated, elems, data, ha, he, hd, hst⟩ := prepare?_inv hp
  obtain ⟨exports, funcs, hex, hfn, hmod, halloc⟩ := allocate?_inv bounds.noGlobals ha
  have hfn2 := mapM_forall₂ hfn
  have hflen : funcs.length = m.funcs.length := hfn2.length_eq.symm
  have hpf : p.store.funcs = before.funcs ++ funcs := by
    rw [hst, foldl_applyData_funcs, foldl_applyElem_funcs, halloc]
  have hlen : p.store.funcs.length = before.funcs.length + m.funcs.length := by
    rw [hpf, List.length_append, hflen]
  have hmodwf : ∀ ex, ModWF p.store { baseInst before m imports with exports := ex } := by
    intro ex a ha
    rw [hlen]; exact baseInst_funcs_lt hi ha
  have hpmod : ModWF p.store p.module := by rw [hmod]; exact hmodwf _
  refine ⟨⟨?_, ?_⟩, hpmod, ?_⟩
  · -- function module instances
    intro i t mod c hfi
    rw [hpf, List.getElem?_append] at hfi
    split at hfi
    · intro a ha
      have := bounds.storeWF.1 i t mod c hfi a ha
      rw [hlen]; omega
    · obtain ⟨f, -, hf⟩ := forall₂_getElem?_right hfn2 hfi
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hf
      obtain ⟨ft, -, hft⟩ := hf
      cases hft
      exact hmodwf _
  · -- memories
    intro i mi hmi
    have hbounds : ∀ w ∈ data, ∃ mi, (elems.foldl applyElem allocated).memories[w.address.value]? =
        some mi ∧ w.offset + w.bytes.size ≤ mi.data.size := by
      intro w hw
      obtain ⟨d, -, hrd⟩ := forall₂_mem_right (mapM_forall₂ hd) hw
      simpa using resolveData?_bounds hrd
    have hshape := foldl_applyData_memories _ data _ (fun _ => rfl) hbounds i
    rw [← hst, hmi, foldl_applyElem_memories, halloc] at hshape
    simp only at hshape
    rw [List.getElem?_append] at hshape
    split at hshape
    · cases hb : before.memories[i]? with
      | none => rw [hb] at hshape; cases hshape
      | some mb =>
        rw [hb] at hshape
        simp only [memShape, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hshape
        obtain ⟨h1, h2⟩ := hshape
        rw [h1, h2]
        exact bounds.storeWF.2 i mb hb
    · cases hb : (m.memories.map fun t => Runtime.MemInst.mk
          ⟨Array.replicate (t.limits.min.val * Silmaril.Wasm.Execution.Memory.pageSize) 0⟩
          (t.limits.max.map Fin.val))[i - before.memories.length]? with
      | none => rw [hb] at hshape; cases hshape
      | some mb =>
        rw [hb] at hshape
        simp only [memShape, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hshape
        obtain ⟨h1, h2⟩ := hshape
        rw [h1, h2]
        simp only [List.getElem?_map, Option.map_eq_some_iff] at hb
        obtain ⟨t, ht, rfl⟩ := hb
        have hvt := (hv.memories t (List.mem_of_getElem? ht)).1
        refine ⟨?_, ?_⟩
        · simp only [ByteArray.size, Array.size_replicate, Silmaril.Wasm.Execution.Memory.pageSize]
          omega
        · intro j hj
          simp only [Option.map_eq_some_iff] at hj
          obtain ⟨b, -, rfl⟩ := hj
          have := b.isLt; omega
  · rcases prepare_start hp with ⟨-, hps⟩ | ⟨i, a, -, ha', hps⟩
    · rw [hps]; trivial
    · rw [hps]
      exact ⟨hpmod a (List.mem_of_getElem? ha'), trivial⟩

/-- From the start code, one Core `call` (if any) reaches a configuration simulating
the prepared Lime1 configuration. -/
theorem start_sim {tgt : ToCore.CHostSemantics H} {before : Store H} {m : Module}
    {imports : List Runtime.ExternVal} {p : Prepared H}
    (bounds : InstantiationBounds before m) (hv : Validation.ModuleValid m)
    (hi : ImportsMatch before m imports) (hp : prepare? before m imports = some p)
    {S : ToCore.CStore H} {F : ToCore.CFrame}
    (hS : ToCore.Store.erase S = p.store.toCore) (hF : ToCore.ModuleInstSim p.module F.module)
    (hl : F.locals = []) :
    ∃ c₁, Silmaril.Wasm.Execution.Core.Steps coreProfile tgt ⟨S, F, startCode m.toCore⟩ c₁ ∧
      c₁.frame = F ∧ Sim (⟨p.store, ⟨[], p.module⟩, p.start⟩ : Config H) c₁ := by
  have hwf := prepare_wf bounds hv hi hp
  have hFe : ToCore.Frame.erase F = (⟨[], p.module⟩ : Silmaril.Wasm.Execution.Runtime.Frame).toCore := by
    rcases F with ⟨locals, mod⟩
    simp only at hl hF
    subst hl
    simp only [ToCore.Frame.erase, Silmaril.Wasm.Execution.Runtime.Frame.toCore, List.map_nil]
    rw [show ToCore.ModuleInst.erase mod = p.module.toCore from hF]
  rcases prepare_start hp with ⟨hs, hps⟩ | ⟨i, a, hs, ha, hps⟩
  · refine ⟨⟨S, F, []⟩, ?_, rfl, ?_, hwf⟩
    · simp only [startCode, Module.toCore, hs]
      exact Relation.ReflTransGen.refl
    · rw [ToCore.Config.norm_eq_toCore_iff]
      refine ⟨hS, hFe, ?_⟩
      simp [hps]
  · -- the invoked address is allocated
    have hwfa : a.value < p.store.funcs.length := by
      have := hwf.2.2
      rw [hps] at this
      exact this.1
    obtain ⟨fnL, hfnL⟩ : ∃ fn, p.store.funcs[a.value]? = some fn :=
      ⟨_, List.getElem?_eq_getElem hwfa⟩
    have hfuncs : S.funcs.map (fun fi => { fi with module := ToCore.ModuleInst.erase fi.module })
        = p.store.funcs.map Silmaril.Wasm.Execution.Runtime.FuncInst.toCore := by
      have := congrArg (·.funcs) hS
      simpa [ToCore.Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toCore] using this
    obtain ⟨fi, hfi, hfity⟩ : ∃ fi, S.funcs[a.value]? = some fi ∧
        fi.type = fnL.type.toDefType := by
      have h1 := congrArg (·[a.value]?) hfuncs
      simp only [List.getElem?_map, hfnL, Option.map_some] at h1
      cases hS' : S.funcs[a.value]? with
      | none => rw [hS'] at h1; cases h1
      | some fi =>
        rw [hS'] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        refine ⟨fi, rfl, ?_⟩
        have := congrArg Silmaril.Wasm.Execution.Core.FuncInst.type h1
        cases fnL <;> simpa [Silmaril.Wasm.Execution.Runtime.FuncInst.toCore, Silmaril.Wasm.Execution.Runtime.FuncInst.type]
          using this
    have hmf : F.module.funcs[i.toNat]? = some a.value := by
      have := congrArg (·.funcs) hF
      simp only [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore]
        at this
      rw [this, List.getElem?_map, ha]; rfl
    refine ⟨⟨S, F, [.ref (.func a.value), .callRefType fi.type]⟩, ?_, rfl, ?_, hwf⟩
    · have hsc : startCode m.toCore = [.plain (.call i)] := by
        simp [startCode, Module.toCore, hs]
      rw [hsc]
      exact Relation.ReflTransGen.single (Silmaril.Wasm.Execution.Core.Step.call hmf hfi)
    · rw [ToCore.Config.norm_eq_toCore_iff]
      refine ⟨hS, hFe, ?_⟩
      simp [hps, Silmaril.Wasm.Execution.Runtime.Store.funcDefType, hfnL, hfity]

/-- **Milestone.** Lime1 instantiation (preparation, segment initialisation and the
start function) is simulated by Core instantiation followed by Core execution.
Stated under `InstantiationBounds` (see the module documentation). -/
theorem Instantiation.toCore {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {before after : Store H} {m : Module}
    {imports : List Runtime.ExternVal} {module : Runtime.ModuleInst} {outcome : Runtime.Result}
    (bounds : InstantiationBounds before m)
    (h : Instantiation src before m imports after module outcome) :
    ∃ c c', Silmaril.Wasm.Execution.Core.Instantiate coreProfile tgt before.toCore m.toCore
        (imports.map Runtime.ExternVal.toCore) c ∧
      Silmaril.Wasm.Execution.Core.Steps coreProfile tgt c c' ∧
      c'.code = outcome.toCore.toAdmin ∧ ToCore.Store.erase c'.store = after.toCore ∧
      ToCore.ModuleInstSim module c.frame.module ∧ c'.frame.module = c.frame.module := by
  obtain ⟨hv, hi, p, hp, rfl, hrun⟩ := h
  obtain ⟨c, S, hinst, hsteps, hS, hF, hl⟩ := prepare_core (tgt := tgt) bounds hv hi hp
  obtain ⟨c₁, hsteps₁, hc₁, hsim₁⟩ := start_sim bounds hv hi hp hS hF hl
  obtain ⟨c', hsteps', hsim'⟩ := Steps.toCore hosts hrun hsim₁
  refine ⟨c, c', hinst, (hsteps.trans hsteps₁).trans hsteps', Sim.result hsim' rfl, ?_, hF, ?_⟩
  · obtain ⟨hn, -⟩ := hsim'
    rcases c' with ⟨cs, cf, cl⟩
    exact (ToCore.Config.norm_eq_toCore_iff.mp hn).1
  · rw [coreSteps_frame_module hsteps', hc₁]

/-- **Milestone.** A divergent Lime1 instantiation diverges in Core.
Stated under `InstantiationBounds` (see the module documentation). -/
theorem InstantiationDiverges.toCore {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {before : Store H} {m : Module}
    {imports : List Runtime.ExternVal} (bounds : InstantiationBounds before m)
    (h : InstantiationDiverges src before m imports) :
    ∃ c, Silmaril.Wasm.Execution.Core.Instantiate coreProfile tgt before.toCore m.toCore
        (imports.map Runtime.ExternVal.toCore) c ∧
      Silmaril.Wasm.Execution.Core.Diverges coreProfile tgt c := by
  obtain ⟨hv, hi, p, hp, hdiv⟩ := h
  obtain ⟨c, S, hinst, hsteps, hS, hF, hl⟩ := prepare_core (tgt := tgt) bounds hv hi hp
  obtain ⟨c₁, hsteps₁, -, hsim₁⟩ := start_sim bounds hv hi hp hS hF hl
  exact ⟨c, hinst, InfiniteTrace.of_steps (hsteps.trans hsteps₁)
    (Diverges.toCore hosts hdiv hsim₁)⟩

end Silmaril.Wasm.Lime1.Execution
