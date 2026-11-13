module

public import Silmaril.Wasm.Component.Reference.Runtime.Objects.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Defs

/-!
# The component store `CStore`

`Runtime.CStore E` is all component-level runtime state as plain data: the shared core-engine
store (whose host code is `CanonHost E`), one append-only `Arena` per REF runtime object kind
(instances, resource types, function values, tasks, threads, subtasks, resource handles,
stream/future ends, waitable sets, error contexts, callers), and the REF `Store` fields
(`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`, `Store`, L508-515,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>):
`waiting` (REF `store.waiting`, in append order), `nesting_depth` and `lockdown`. The
component store lives OUTSIDE the core store (issue #477). Continuations of blocked threads are
NOT part of it (they live in the machine).

Arena access is uniform: an `ArenaField E Id α` names one arena of the store together with its
id type, and `ArenaField.alloc`/`get?`/`set`/`modify` act on the store through it. The
lemmas (`get?_alloc`, `get?_alloc_self`, `length_alloc`, `get?_set`, `get?_set_self`,
`get?_set_ne`, `get?_modify`, ...) are proved once, generically, from the `Runtime.Arena`
lemmas, and hold for each of the eleven instances `ArenaField.insts`, ..., `ArenaField.callers`.
Accesses to different arenas commute definitionally (each `put` is a structure update of one
field), so cross-arena frame facts are `rfl`/`simp` on the concrete instances.

Not modelled here: readiness evaluation, candidate selection, store operations of the
REF (`invoke`, `tick`, `lift`, `lower`; `Embedding.lean`) and invariants.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine

/-- The component store: the core store plus all component-level runtime objects. -/
structure CStore (E : CoreEngine) where
  /-- The shared core-engine store; its host code is canon host sites. -/
  core : E.Store (CanonHost E)
  /-- Component instances (REF `ComponentInstance`). -/
  insts : Arena InstState := []
  /-- Resource types (REF `ResourceType`). -/
  resourceTypes : Arena (ResourceType E) := []
  /-- Component function values (REF `FuncInst`). -/
  funcs : Arena (CFuncInst E) := []
  /-- Tasks (REF `Task`). -/
  tasks : Arena (Task E) := []
  /-- Threads (REF `Thread`, without continuations). -/
  threads : Arena Thread := []
  /-- Subtasks (REF `Subtask`). -/
  subtasks : Arena Subtask := []
  /-- Resource handles (REF `ResourceHandle`). -/
  resHandles : Arena ResourceHandle := []
  /-- Stream and future ends (REF `End`). -/
  ends : Arena (End E) := []
  /-- Waitable sets (REF `WaitableSet`). -/
  wsets : Arena WaitableSet := []
  /-- Error contexts (REF `ErrorContext`). -/
  errCtxs : Arena ErrorContext := []
  /-- Callers (defunctionalized `on_start`/`on_resolve` pairs). -/
  callers : Arena (Caller E) := []
  /-- REF `Store.waiting`, in append order. -/
  waiting : List ThreadId := []
  /-- REF `Store.nesting_depth`. -/
  nestingDepth : Nat := 0
  /-- REF `Store.lockdown`. -/
  lockdown : Bool := false

namespace CStore

variable {E : CoreEngine}

/-- REF `Store.__init__`: the empty core store and no objects. -/
def empty : CStore E := { core := E.empty (CanonHost E) }

@[simp] theorem empty_core : (empty : CStore E).core = E.empty (CanonHost E) := rfl
@[simp] theorem empty_insts : (empty : CStore E).insts = [] := rfl
@[simp] theorem empty_resourceTypes : (empty : CStore E).resourceTypes = [] := rfl
@[simp] theorem empty_funcs : (empty : CStore E).funcs = [] := rfl
@[simp] theorem empty_tasks : (empty : CStore E).tasks = [] := rfl
@[simp] theorem empty_threads : (empty : CStore E).threads = [] := rfl
@[simp] theorem empty_subtasks : (empty : CStore E).subtasks = [] := rfl
@[simp] theorem empty_resHandles : (empty : CStore E).resHandles = [] := rfl
@[simp] theorem empty_ends : (empty : CStore E).ends = [] := rfl
@[simp] theorem empty_wsets : (empty : CStore E).wsets = [] := rfl
@[simp] theorem empty_errCtxs : (empty : CStore E).errCtxs = [] := rfl
@[simp] theorem empty_callers : (empty : CStore E).callers = [] := rfl
@[simp] theorem empty_waiting : (empty : CStore E).waiting = [] := rfl
@[simp] theorem empty_nestingDepth : (empty : CStore E).nestingDepth = 0 := rfl
@[simp] theorem empty_lockdown : (empty : CStore E).lockdown = false := rfl

end CStore

/-- One arena of the component store with its id type: a lens `get`/`put` onto the arena and
the id wrapping `mkId`/`idx` (a bijection with `Nat`). -/
structure ArenaField (E : CoreEngine) (Id : Type) (α : Type) where
  /-- Read the arena. -/
  get : CStore E → Arena α
  /-- Replace the arena. -/
  put : CStore E → Arena α → CStore E
  /-- Wrap an arena index. -/
  mkId : Nat → Id
  /-- Unwrap an id. -/
  idx : Id → Nat
  get_put : ∀ s a, get (put s a) = a
  put_get : ∀ s, put s (get s) = s
  idx_mkId : ∀ n, idx (mkId n) = n
  mkId_idx : ∀ i, mkId (idx i) = i

namespace ArenaField

variable {E : CoreEngine} {Id α : Type} (F : ArenaField E Id α)

attribute [simp] get_put put_get idx_mkId mkId_idx

/-- Allocate `x` in the arena; returns the new store and the fresh id (the old length). -/
def alloc (s : CStore E) (x : α) : CStore E × Id :=
  let r := (F.get s).alloc x
  (F.put s r.1, F.mkId r.2)

/-- The object with id `i`, if allocated. -/
def get? (s : CStore E) (i : Id) : Option α := (F.get s).get? (F.idx i)

/-- Replace the object with id `i` (no-op if unallocated). -/
def set (s : CStore E) (i : Id) (x : α) : CStore E := F.put s ((F.get s).set (F.idx i) x)

/-- Update the object with id `i` (no-op if unallocated). -/
def modify (s : CStore E) (i : Id) (f : α → α) : CStore E :=
  F.put s ((F.get s).modify (F.idx i) f)

/-- Number of allocated objects. -/
def size (s : CStore E) : Nat := (F.get s).length

@[simp] theorem alloc_snd (s : CStore E) (x : α) : (F.alloc s x).2 = F.mkId (F.size s) := rfl

@[simp] theorem length_alloc (s : CStore E) (x : α) :
    F.size (F.alloc s x).1 = F.size s + 1 := by
  simp [alloc, size]

@[simp] theorem get?_alloc_self (s : CStore E) (x : α) :
    F.get? (F.alloc s x).1 (F.alloc s x).2 = some x := by
  simp [alloc, get?, Arena.alloc, Arena.get?_eq_getElem?]

@[simp] theorem size_set (s : CStore E) (i : Id) (x : α) : F.size (F.set s i x) = F.size s := by
  simp [set, size]

@[simp] theorem size_modify (s : CStore E) (i : Id) (f : α → α) :
    F.size (F.modify s i f) = F.size s := by
  simp [modify, size]

section DecEq

variable [DecidableEq Id]

end DecEq

/-! ### The eleven arenas of `CStore` -/

/-- Component instances. -/
def insts : ArenaField E InstId InstState where
  get s := s.insts
  put s a := { s with insts := a }
  mkId := InstId.mk
  idx := InstId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

/-- Resource types. -/
def resourceTypes : ArenaField E RtId (ResourceType E) where
  get s := s.resourceTypes
  put s a := { s with resourceTypes := a }
  mkId := RtId.mk
  idx := RtId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

/-- Component function values. -/
def funcs : ArenaField E FuncId (CFuncInst E) where
  get s := s.funcs
  put s a := { s with funcs := a }
  mkId := FuncId.mk
  idx := FuncId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

/-- Tasks. -/
def tasks : ArenaField E TaskId (Task E) where
  get s := s.tasks
  put s a := { s with tasks := a }
  mkId := TaskId.mk
  idx := TaskId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

/-- Threads. -/
def threads : ArenaField E ThreadId Thread where
  get s := s.threads
  put s a := { s with threads := a }
  mkId := ThreadId.mk
  idx := ThreadId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

/-- Subtasks. -/
def subtasks : ArenaField E SubtaskId Subtask where
  get s := s.subtasks
  put s a := { s with subtasks := a }
  mkId := SubtaskId.mk
  idx := SubtaskId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

/-- Resource handles. -/
def resHandles : ArenaField E HandleObjId ResourceHandle where
  get s := s.resHandles
  put s a := { s with resHandles := a }
  mkId := HandleObjId.mk
  idx := HandleObjId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

/-- Stream and future ends. -/
def ends : ArenaField E EndId (End E) where
  get s := s.ends
  put s a := { s with ends := a }
  mkId := EndId.mk
  idx := EndId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

/-- Waitable sets. -/
def wsets : ArenaField E WsetId WaitableSet where
  get s := s.wsets
  put s a := { s with wsets := a }
  mkId := WsetId.mk
  idx := WsetId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

/-- Error contexts. -/
def errCtxs : ArenaField E ErrCtxId ErrorContext where
  get s := s.errCtxs
  put s a := { s with errCtxs := a }
  mkId := ErrCtxId.mk
  idx := ErrCtxId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

/-- Callers. -/
def callers : ArenaField E CallerId (Caller E) where
  get s := s.callers
  put s a := { s with callers := a }
  mkId := CallerId.mk
  idx := CallerId.idx
  get_put _ _ := rfl
  put_get _ := rfl
  idx_mkId _ := rfl
  mkId_idx _ := rfl

end ArenaField

namespace CStore

variable {E : CoreEngine}

/-- The component instance `i`. -/
def inst? (s : CStore E) (i : InstId) : Option InstState := ArenaField.insts.get? s i
/-- The resource type `r`. -/
def resourceType? (s : CStore E) (r : RtId) : Option (ResourceType E) :=
  ArenaField.resourceTypes.get? s r
/-- The function value `f`. -/
def func? (s : CStore E) (f : FuncId) : Option (CFuncInst E) := ArenaField.funcs.get? s f
/-- The task `t`. -/
def task? (s : CStore E) (t : TaskId) : Option (Task E) := ArenaField.tasks.get? s t
/-- The thread `t`. -/
def thread? (s : CStore E) (t : ThreadId) : Option Thread := ArenaField.threads.get? s t
/-- The subtask `t`. -/
def subtask? (s : CStore E) (t : SubtaskId) : Option Subtask := ArenaField.subtasks.get? s t
/-- The resource handle `h`. -/
def resHandle? (s : CStore E) (h : HandleObjId) : Option ResourceHandle :=
  ArenaField.resHandles.get? s h
/-- The stream/future end `e`. -/
def end? (s : CStore E) (e : EndId) : Option (End E) := ArenaField.ends.get? s e
/-- The waitable set `w`. -/
def wset? (s : CStore E) (w : WsetId) : Option WaitableSet := ArenaField.wsets.get? s w
/-- The error context `x`. -/
def errCtx? (s : CStore E) (x : ErrCtxId) : Option ErrorContext := ArenaField.errCtxs.get? s x
/-- The caller `c`. -/
def caller? (s : CStore E) (c : CallerId) : Option (Caller E) := ArenaField.callers.get? s c

/-! ### Tests -/

end CStore

end Silmaril.Wasm.Component.Runtime

namespace Silmaril.Wasm.Component.Runtime

open Engine

namespace ArenaField

variable {E : CoreEngine} {Id α : Type} (F : ArenaField E Id α)

theorem idx_injective {i j : Id} (h : F.idx i = F.idx j) : i = j := by
  rw [← F.mkId_idx i, ← F.mkId_idx j, h]

section DecEq

variable [DecidableEq Id]

theorem get?_modify (s : CStore E) (i j : Id) (f : α → α) :
    F.get? (F.modify s i f) j = if i = j then (F.get? s j).map f else F.get? s j := by
  by_cases h : i = j
  · subst h; simp [modify, get?, Arena.get?_modify_self]
  · have : F.idx i ≠ F.idx j := fun e => h (F.idx_injective e)
    simp [modify, get?, h, Arena.get?_modify_ne _ _ this]

theorem get?_modify_self (s : CStore E) (i : Id) (f : α → α) :
    F.get? (F.modify s i f) i = (F.get? s i).map f := by
  simp [get?_modify]

theorem get?_modify_ne (s : CStore E) {i j : Id} (f : α → α) (h : i ≠ j) :
    F.get? (F.modify s i f) j = F.get? s j := by
  simp [get?_modify, h]

end DecEq

end ArenaField

end Silmaril.Wasm.Component.Runtime
