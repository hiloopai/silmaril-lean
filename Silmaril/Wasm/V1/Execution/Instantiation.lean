module

public import Silmaril.Wasm.V1.Execution.Step
public import Silmaril.Wasm.V1.Validation.Modules

/-!
# Linking, allocation and instantiation

Import matching uses current table and memory sizes and covariant limit
matching, with invariant function and global types. Initializers see only the
imported globals; segment offsets see the complete allocated module. Segment
writes occur only after every segment has been resolved and bounds checked.

`prepare?` is executable allocation and segment initialization, separately
from declarative module validation and import matching. `Instantiation` adds
those premises and execution of the start function, including its traps;
`InstantiationDiverges` records a divergent start. Failed preparation has no
returned store; this interface makes no rollback claim about an embedder.
The relation is defined over raw stores: import matching alone does not prove
that imported instances or the store are well-formed. Store validity and its
connection to module validation, preservation and progress remain separate.
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-- An actual maximum must exist and be no larger whenever the import requires one. -/
def LimitsMatch (size : Nat) (maximum : Option Nat) (expected : Limits) : Prop :=
  expected.min.val ≤ size ∧ ∀ bound ∈ expected.max,
    ∃ actual ∈ maximum, actual ≤ bound.val

inductive ExternMatches {H : Type} (s : Store H) : ExternVal → ExternType → Prop where
  | func (a : FuncAddr) (fn : FuncInst Func H) (ft : FuncType)
      (found : s.funcs[a.value]? = some fn) (typed : fn.type = ft) :
      ExternMatches s (.func a) (.func ft)
  | table (a : TableAddr) (table : TableInst) (tt : TableType)
      (found : s.tables[a.value]? = some table)
      (limits : LimitsMatch table.refs.length table.max tt.limits) :
      ExternMatches s (.table a) (.table tt)
  | memory (a : MemAddr) (memory : MemInst) (mt : MemoryType)
      (found : s.memories[a.value]? = some memory)
      (limits : LimitsMatch (Memory.size memory.data) memory.max mt.limits) :
      ExternMatches s (.memory a) (.memory mt)
  | global (a : GlobalAddr) (global : GlobalInst) (gt : GlobalType)
      (found : s.globals[a.value]? = some global)
      (type : global.value.type = gt.value) (mutability : global.mutability = gt.mutability) :
      ExternMatches s (.global a) (.global gt)

def ImportsMatch {H : Type} (s : Store H) (m : Module) (imports : List ExternVal) : Prop :=
  List.Forall₂ (fun i e => ∃ et, Validation.importType? m.types i.desc = some et ∧
    ExternMatches s e et) m.imports imports

def importedInstance (imports : List ExternVal) : ModuleInst where
  funcs := imports.filterMap fun e => match e with | .func a => some a | _ => none
  tables := imports.filterMap fun e => match e with | .table a => some a | _ => none
  memories := imports.filterMap fun e => match e with | .memory a => some a | _ => none
  globals := imports.filterMap fun e => match e with | .global a => some a | _ => none

/-- Evaluation of the scalar constants admitted in 1.0 constant expressions. -/
def constInstr? {H : Type} (s : Store H) (module : ModuleInst) : Instr → Option Value
  | .intConst t x => some (.int t x)
  | .floatConst t x => some (.float t x)
  | .globalGet i => do
      let a ← module.globals[i.toNat]?
      let g ← s.globals[a.value]?
      return g.value
  | _ => none

/-- A well-typed 1.0 initializer leaves exactly one value. -/
def constExpr? {H : Type} (s : Store H) (module : ModuleInst) (es : Expr) : Option Value := do
  let vs ← es.mapM (constInstr? s module)
  match vs with | [v] => some v | _ => none

def offset? {H : Type} (s : Store H) (module : ModuleInst) (es : Expr) : Option Nat := do
  match ← constExpr? s module es with
  | ⟨.int .i32, x⟩ => some x.toNat
  | _ => none

def exportValue? (module : ModuleInst) : ExternIdx → Option ExternVal
  | .func i => (module.funcs[i.toNat]?).map .func
  | .table i => (module.tables[i.toNat]?).map .table
  | .memory i => (module.memories[i.toNat]?).map .memory
  | .global i => (module.globals[i.toNat]?).map .global

/-- Fresh addresses preserve definition order after the preexisting store. -/
def addresses (kind : AddrKind) (start count : Nat) : List (Addr kind) :=
  (List.range count).map fun i => ⟨start + i⟩

def allocate? {H : Type} (s : Store H) (m : Module) (imports : List ExternVal) :
    Option (Store H × ModuleInst) := do
  let imported := importedInstance imports
  let initializers : List Value ← m.globals.mapM fun g =>
    constExpr? s { globals := imported.globals } g.init
  let module : ModuleInst := {
    types := m.types
    funcs := imported.funcs ++ addresses .func s.funcs.length m.funcs.length
    tables := imported.tables ++ addresses .table s.tables.length m.tables.length
    memories := imported.memories ++ addresses .memory s.memories.length m.memories.length
    globals := imported.globals ++ addresses .global s.globals.length m.globals.length }
  let exports : List ExportInst ← m.exports.mapM fun e => do
    return ⟨e.name, ← exportValue? module e.index⟩
  let module := {module with exports := exports}
  let funcs : List (FuncInst Func H) ← m.funcs.mapM fun (f : Func) => do
    let ft ← m.types[f.type.toNat]?
    return FuncInst.wasm ft module f
  let tables := m.tables.map fun t =>
    TableInst.mk (List.replicate t.limits.min.val none) (t.limits.max.map Fin.val)
  let memories := m.memories.map fun t =>
    MemInst.mk ⟨Array.replicate (t.limits.min.val * Memory.pageSize) 0⟩ (t.limits.max.map Fin.val)
  let globals := List.zipWith (fun g v => GlobalInst.mk v g.type.mutability) m.globals initializers
  return (⟨s.funcs ++ funcs, s.tables ++ tables, s.memories ++ memories, s.globals ++ globals⟩, module)

structure ElemWrite where
  address : TableAddr
  offset : Nat
  values : List FuncAddr

structure DataWrite where
  address : MemAddr
  offset : Nat
  bytes : Memory.Bytes

def resolveElem? {H : Type} (s : Store H) (module : ModuleInst) (e : Elem) : Option ElemWrite := do
  let offset ← offset? s module e.offset
  let a ← module.tables[e.table.toNat]?
  let table ← s.tables[a.value]?
  let refs ← e.init.mapM fun i => module.funcs[i.toNat]?
  if offset + refs.length ≤ table.refs.length then return ⟨a, offset, refs⟩ else none

def resolveData? {H : Type} (s : Store H) (module : ModuleInst) (d : Data) : Option DataWrite := do
  let offset ← offset? s module d.offset
  let a ← module.memories[d.memory.toNat]?
  let memory ← s.memories[a.value]?
  let bytes := d.bytes
  if offset + bytes.size ≤ memory.data.size then return ⟨a, offset, bytes⟩ else none

def applyElem {H : Type} (s : Store H) (w : ElemWrite) : Store H :=
  {s with tables := s.tables.modify w.address.value fun table =>
    {table with refs := table.refs.take w.offset ++ w.values.map some ++
      table.refs.drop (w.offset + w.values.length)}}

def applyData {H : Type} (s : Store H) (w : DataWrite) : Store H :=
  {s with memories := s.memories.modify w.address.value fun memory =>
    {memory with data := w.bytes.copySlice 0 memory.data w.offset w.bytes.size}}

structure Prepared (H : Type) where
  store : Store H
  module : ModuleInst
  start : List Admin

def prepare? {H : Type} (s : Store H) (m : Module) (imports : List ExternVal) : Option (Prepared H) := do
  let (allocated, module) ← allocate? s m imports
  let elems ← m.elems.mapM (resolveElem? allocated module)
  let data ← m.data.mapM (resolveData? allocated module)
  let initialized := data.foldl applyData (elems.foldl applyElem allocated)
  let start : List Admin ← match m.start with
    | none => some []
    | some i => (module.funcs[i.toNat]?).map fun a => [.invoke a]
  return ⟨initialized, module, start⟩

/-- A successful preparation followed by a finite start result (including a trap). -/
structure Instantiation {H : Type} (host : HostSemantics H) (before : Store H)
    (m : Module) (imports : List ExternVal) (after : Store H) (module : ModuleInst)
    (outcome : Result) : Prop where
  valid : Validation.ModuleValid m
  importsMatch : ImportsMatch before m imports
  prepared : ∃ p : Prepared H, prepare? before m imports = some p ∧ p.module = module ∧
    Steps host ⟨p.store, ⟨[], module⟩, p.start⟩ ⟨after, ⟨[], module⟩, result outcome⟩

def InstantiationDiverges {H : Type} (host : HostSemantics H) (before : Store H)
    (m : Module) (imports : List ExternVal) : Prop :=
  Validation.ModuleValid m ∧ ImportsMatch before m imports ∧
    ∃ p : Prepared H, prepare? before m imports = some p ∧
      Diverges host ⟨p.store, ⟨[], p.module⟩, p.start⟩

theorem ImportsMatch.length {H : Type} {s : Store H} {m : Module} {imports : List ExternVal}
    (h : ImportsMatch s m imports) : m.imports.length = imports.length := h.length_eq

/-- Bounds are checked before a resolved element write is returned. -/
theorem resolveElem?_bounds {H : Type} {s : Store H} {module : ModuleInst} {e : Elem}
    {w : ElemWrite} (h : resolveElem? s module e = some w) :
    ∃ table, s.tables[w.address.value]? = some table ∧
      w.offset + w.values.length ≤ table.refs.length := by
  simp only [resolveElem?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨offset, _, a, _, table, ht, refs, _, h⟩ := h
  split at h
  · simp only [Option.pure_def, Option.some.injEq] at h
    subst w
    exact ⟨_, ht, by assumption⟩
  · contradiction

theorem resolveData?_bounds {H : Type} {s : Store H} {module : ModuleInst} {d : Data}
    {w : DataWrite} (h : resolveData? s module d = some w) :
    ∃ memory, s.memories[w.address.value]? = some memory ∧
      w.offset + w.bytes.size ≤ memory.data.size := by
  simp only [resolveData?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨offset, _, a, _, memory, hm, h⟩ := h
  split at h
  · simp only [Option.pure_def, Option.some.injEq] at h
    subst w
    exact ⟨_, hm, by assumption⟩
  · contradiction

/-! ## Invocation

`$invoke(s, funcaddr, val*)` (`9-module.spectec`, section `Invocation`; REC 4.5.5).
This is the embedder's entry point: it is not reachable from `Instantiation`, but
it fixes two things nothing else records — that the initial frame has no locals and
the *empty* module instance, and that the arguments must match the function's
parameter types. The Core 3.0 model has the same pair
(`Silmaril/Wasm/Execution/Core/Instantiation.lean`). -/

/-- `$invoke(s, a, val*)`: the configuration that invokes function address `a` on
`vs`. SpecTec fixes the frame to `{ MODULE {} }`; the arity side condition is
`InvokeOk`. -/
def invoke {H : Type} (s : Store H) (a : FuncAddr) (vs : List Value) : Config H :=
  ⟨s, ⟨[], {}⟩, values vs ++ [.invoke a]⟩

/-- The premise of `$invoke`: the function exists and the arguments match its
parameter types pointwise. SpecTec writes this as
`$funcinst((s; f))[fa].TYPE = t_1^n -> t_2*` with `val^n` the arguments, which
constrains the arity; the 2019 Recommendation (4.5.5) additionally requires each
argument to have the corresponding parameter type, and that is what we state. -/
def InvokeOk {H : Type} (s : Store H) (a : FuncAddr) (vs : List Value) : Prop :=
  ∃ fn, s.funcs[a.value]? = some fn ∧ vs.map Value.type = fn.type.params

/-- A valid invocation supplies exactly as many arguments as the function declares. -/
theorem InvokeOk.arity {H : Type} {s : Store H} {a : FuncAddr} {vs : List Value}
    (h : InvokeOk s a vs) :
    ∃ fn, s.funcs[a.value]? = some fn ∧ vs.length = fn.type.params.length := by
  obtain ⟨fn, hf, ht⟩ := h
  exact ⟨fn, hf, by simpa using congrArg List.length ht⟩

/-- `invoke` produces exactly the administrative code SpecTec writes. -/
@[simp] theorem invoke_code {H : Type} (s : Store H) (a : FuncAddr) (vs : List Value) :
    (invoke s a vs).code = values vs ++ [.invoke a] := rfl

@[simp] theorem invoke_store {H : Type} (s : Store H) (a : FuncAddr) (vs : List Value) :
    (invoke s a vs).store = s := rfl

@[simp] theorem invoke_frame {H : Type} (s : Store H) (a : FuncAddr) (vs : List Value) :
    (invoke s a vs).frame = ⟨[], {}⟩ := rfl

/-- A valid invocation of a Wasm function takes the first step of `Step.invokeWasm`,
provided the function's result arity is within the 1.0 restriction. -/
theorem InvokeOk.step_wasm {H : Type} {host : HostSemantics H} {s : Store H} {a : FuncAddr}
    {vs : List Value} {ft : FuncType} {module : ModuleInst} {fn : Func}
    (h : InvokeOk s a vs) (hf : s.funcs[a.value]? = some (.wasm ft module fn))
    (hr : ft.results.length ≤ 1) :
    Step host (invoke s a vs)
      ⟨s, ⟨[], {}⟩, [.frame ft.results.length ⟨vs ++ fn.locals.map Value.zero, module⟩
        [.label ft.results.length [] (expression fn.body)]]⟩ := by
  obtain ⟨fn', hf', ht⟩ := h
  rw [hf] at hf'
  cases hf'
  exact Step.invokeWasm s ⟨[], {}⟩ a ft module fn vs hf
    (by simpa [FuncInst.type] using congrArg List.length ht) hr

end Silmaril.Wasm.V1.Execution
