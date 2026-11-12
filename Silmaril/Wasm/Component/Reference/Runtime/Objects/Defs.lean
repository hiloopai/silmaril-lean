module

public import Silmaril.Wasm.Component.Reference.Runtime.Builtin.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Table.Defs
public import Silmaril.Wasm.Component.Reference.Value.Basic.Defs
public import Silmaril.Wasm.Component.Reference.Async.Codes.Defs

/-!
# Runtime objects of the component store

Every REF runtime class of `design/mvp/canonical-abi/definitions.py` at component-model
`a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
transcribed as PLAIN DATA: no functions, no programs. Object
references are arena ids (`Runtime/Ids.lean`); the objects live in the arenas of
`Runtime.CStore` (`Runtime/Store.lean`). Python closures stored in objects are
defunctionalized into data:

| Lean | REF (line) | defunctionalized closures |
| --- | --- | --- |
| `ResourceType` | `ResourceType` (L703) | `dtor` is a core function address |
| `ResourceHandle` | `ResourceHandle` (L689) | |
| `PendingEvent` | `Waitable.pending_event` (L724) | `subtask_event`, `*_event` of `notify` |
| `WaitableCommon`, `Waitable` | `Waitable` (L724) | |
| `WaitableSet` | `WaitableSet` (L766) | |
| `Subtask` | `Subtask` (L816) | `on_cancel` is a `CancelRef` |
| `Task` | `Task` (L392) | `on_start`/`on_resolve` are a `Caller` record (by id) |
| `Thread`, `ThreadStatus` | `Thread` (L279) | `ready_func` is a `ReadyCond`; no `cont` |
| `End`, `BufferDesc` | `End` (L931), `GuestBuffer` (L887), host buffers of `run_tests.py` | |
| `ErrorContext` | `ErrorContext` (L2664) | |
| `HandleEntry` | elements of `ComponentInstance.handles` (L190) | |
| `InstState` | `ComponentInstance` (L190) | `store` is implicit |
| `CFuncInst` | `FuncInst` (L385-389) produced by `Store.lift` or supplied by the host | |
| `Caller`, `SubKind` | `(on_start, on_resolve)` pairs (see `Caller`) | |
| `CancelRef` | `OnCancel` (L385-389) | |
| `WaitSite` | the `block()` sites K1-K13 (listed at `WaitSite`) | |

The Async/Codes enumerations `SubtaskState`, `TaskState`, `EndState`, `EndKind` are reused.

Not modelled or claimed here: any behaviour (methods are canon programs in `Runtime/` and
`Canon/`), the evaluation of `ReadyCond` (`Runtime/Thread.lean`), invariants relating objects, and
REF's `Thread.cont` (the machine keeps continuations). -/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine Async

/-! ## Resources -/

/-- REF `ResourceType` (L703): the defining instance (`none` for host-defined resources), the
representation type (`rep` of `resourcetype`, i32 or 🐘 i64) and the optional destructor. -/
structure ResourceType (E : CoreEngine) where
  /-- REF `impl`. -/
  impl : Option InstId
  /-- The representation address type (`rep` of the resource type definition). -/
  rep : AddrType := .i32
  /-- REF `dtor`. -/
  dtor : Option E.FuncAddr := none
  deriving DecidableEq

/-- REF `ResourceHandle` (L689). `scope` is REF `borrow_scope : Optional[Task]`. -/
structure ResourceHandle where
  /-- REF `rt`. -/
  rt : RtId
  /-- REF `rep`. -/
  rep : Nat
  /-- REF `own`. -/
  own : Bool
  /-- REF `borrow_scope`. -/
  scope : Option TaskId := none
  /-- REF `num_lends`. -/
  numLends : Nat := 0
  deriving DecidableEq, Repr

/-! ## Waitables -/

/-- A defunctionalized REF `pending_event` closure: the `subtask_event` of an async
`canon_lower` (L2222-2226), or the `stream_event`/`future_event` of `notify(progress)`
(L1030-1066) with the progress it captured. All other data the closures read (state, index,
peer) is read from the store at delivery time, as in REF. -/
inductive PendingEvent where
  | subtask (s : SubtaskId)
  | streamEnd (e : EndId) (progress : Nat)
  | futureEnd (e : EndId) (progress : Nat)
  deriving DecidableEq, Repr

/-- The `Waitable` base-class fields (L724-731). -/
structure WaitableCommon where
  /-- REF `pending_event`. -/
  pending : Option PendingEvent := none
  /-- REF `wset`. -/
  wset : Option WsetId := none
  /-- REF `has_sync_waiter`. -/
  hasSyncWaiter : Bool := false
  /-- Ghost field (no REF counterpart; no program reads it): the thread that set
  `has_sync_waiter` (REF `current_thread()` at `Waitable.wait_for_pending_event`, L745, and at
  `canon_subtask_cancel`, L2397/L2406), `none` while the flag is clear. Written by exactly the
  updates that write `hasSyncWaiter` (`CStore.setSyncWaiterSt`,
  `Builtins.WaitableSt.requestCancel`). -/
  syncOwner : Option ThreadId := none
  deriving DecidableEq, Repr

/-- A waitable object: a subtask or a stream/future end. -/
inductive Waitable where
  | subtask (s : SubtaskId)
  | end_ (e : EndId)
  deriving DecidableEq, Repr

/-- REF `WaitableSet` (L766). `elems` is in REF list order (which `random.shuffle` (C4)
permutes persistently). -/
structure WaitableSet where
  /-- REF `elems`. -/
  elems : List Waitable := []
  /-- REF `num_waiting`. -/
  numWaiting : Nat := 0
  deriving DecidableEq, Repr

/-- REF `OnCancel` (L385-389) of a started call: the callee task's `request_cancellation`, a
host cancellation hook (choice point E1), or none. -/
inductive CancelRef where
  | task (t : TaskId)
  | host (n : Nat)
  | none
  deriving DecidableEq, Repr

/-- REF `Subtask` (L816): the caller-side record of a lowered call. `index` is the caller's
handle index (`subtaski`), `inst` the caller instance. -/
structure Subtask where
  /-- `Waitable` fields. -/
  common : WaitableCommon := {}
  /-- REF `state`. -/
  state : SubtaskState := .starting
  /-- REF `on_cancel`. -/
  onCancel : CancelRef := .none
  /-- REF `lenders` (`none` once the resolve was delivered). -/
  lenders : Option (List HandleObjId) := some []
  /-- REF `cancellation_requested`. -/
  cancellationRequested : Bool := false
  /-- REF `flat_results`. -/
  flatResults : List FlatValue := []
  /-- The caller's handle index of this subtask, once added. -/
  index : Option Nat := none
  /-- The caller instance. -/
  inst : InstId
  deriving DecidableEq

/-! ## Threads and readiness -/

/-- The `block()` sites of the REF (K1-K13, numbered as below). A choice `earlyReturn`
of `wait_until` (C1) carries its site, so policies can tell e.g. `thread.yield` from
`waitable-set.wait`. -/
inductive WaitSite where
  /-- K1: `Task.enter_implicit_thread` backpressure gate. -/
  | enterBackpressure
  /-- K2: callback `YIELD`. -/
  | callbackYield
  /-- K3: callback `WAIT` (`WaitableSet.wait_from_callback`). -/
  | callbackWait
  /-- K4: `waitable-set.wait`. -/
  | waitableSetWait
  /-- K5: sync `stream/future.read/write` (`wait_for_pending_event`). -/
  | syncCopy
  /-- K6: sync `stream/future.cancel-read/write`. -/
  | syncCancelCopy
  /-- K7: sync `canon_lower` waiting for the subtask to resolve. -/
  | syncLower
  /-- K8: sync `subtask.cancel`. -/
  | syncSubtaskCancel
  /-- K9: `thread.yield` and the `yield-then-promote` fallback. -/
  | yield_
  /-- K10: `thread.suspend` and the `suspend-then-promote` fallback. -/
  | suspend
  /-- K11: `suspend-then-resume` and successful `suspend-then-promote`. -/
  | suspendThenResume
  /-- K12: `yield-then-resume` and successful `yield-then-promote`. -/
  | yieldThenResume
  /-- K13: host threads. -/
  | host
  deriving DecidableEq, Repr

/-- The number `k` of site `Kk`. -/
def WaitSite.toNat : WaitSite → Nat
  | .enterBackpressure => 1 | .callbackYield => 2 | .callbackWait => 3
  | .waitableSetWait => 4 | .syncCopy => 5 | .syncCancelCopy => 6 | .syncLower => 7
  | .syncSubtaskCancel => 8 | .yield_ => 9 | .suspend => 10 | .suspendThenResume => 11
  | .yieldThenResume => 12 | .host => 13

/-- All wait sites, in K order. -/
def WaitSite.all : List WaitSite :=
  [.enterBackpressure, .callbackYield, .callbackWait, .waitableSetWait, .syncCopy,
    .syncCancelCopy, .syncLower, .syncSubtaskCancel, .yield_, .suspend, .suspendThenResume,
    .yieldThenResume, .host]

/-- A defunctionalized REF `ready_func` (DATA ONLY; evaluated in `Runtime/Thread.lean`). One
constructor per
REF ready predicate:
* `always`: `lambda: True` (K9, K12, `thread.resume-later`);
* `backpressure inst needsExclusive`: `not has_bp()` of `enter_implicit_thread` (K1);
* `exclusiveFree inst`: `inst.exclusive_thread is None` (K2);
* `callbackWait inst task wset`: `wait_from_callback`'s condition (K3);
* `wsetHasEvent wset`: `wset.has_pending_event` (K4);
* `waitableHasEvent w`: `w.has_pending_event` (K5, K6);
* `subtaskResolved s`: `subtask.resolved` (K7, K8);
* `host n`: a host predicate (K13). -/
inductive ReadyCond where
  | always
  | backpressure (inst : InstId) (needsExclusive : Bool)
  | exclusiveFree (inst : InstId)
  | callbackWait (inst : InstId) (task : TaskId) (wset : WsetId)
  | wsetHasEvent (wset : WsetId)
  | waitableHasEvent (w : Waitable)
  | subtaskResolved (s : SubtaskId)
  | host (n : Nat)
  deriving DecidableEq, Repr

/-- The REF `Thread.cont` states at head: `'running'`, `None` (exited), or a continuation
(blocked; the continuation itself lives in the machine). -/
inductive ThreadStatus where
  | running
  | exited
  | blocked
  deriving DecidableEq, Repr

/-- REF `Thread` (L279) without its continuation. A new thread is blocked with no
`readyCond` (suspended) and unregistered (`index = none`). -/
structure Thread where
  /-- REF `cont` state. -/
  status : ThreadStatus := .blocked
  /-- REF `ready_func` (`some` exactly when the thread is in `store.waiting`). -/
  readyCond : Option ReadyCond := none
  /-- REF `task`. -/
  task : TaskId
  /-- REF `index` in `inst.threads`. -/
  index : Option Nat := none
  /-- REF `storage` (context slots, initially `[0, 0]`). -/
  storage : List Nat := initialContext
  /-- REF `cancellable`. -/
  cancellable : Bool := false
  deriving DecidableEq, Repr

/-! ## Streams and futures -/

/-- A stream/future copy buffer: REF `GuestBuffer` (L887, with its `LiftLowerContext` whose
borrow scope is none), or a host buffer (choice point E1). `length` is REF `length`,
`progress` REF `progress`. -/
inductive BufferDesc (E : CoreEngine) where
  | guest (cx : LiftLowerContext E) (t : Option (WIT.ClosedType RtId)) (ptr length progress : Nat)
  | host (b : HostBufId) (length progress : Nat)
  deriving DecidableEq

namespace BufferDesc

variable {E : CoreEngine}

/-- REF `Buffer.remain` (`length - progress`). -/
def remain : BufferDesc E → Nat
  | .guest _ _ _ length progress => length - progress
  | .host _ length progress => length - progress

/-- REF `progress`. -/
def progress : BufferDesc E → Nat
  | .guest _ _ _ _ p => p
  | .host _ _ p => p

end BufferDesc

/-- REF `End` (L931) and its four subclasses (`kind`). `owner = none` is a host end;
`other = none` means the peer was dropped. -/
structure End (E : CoreEngine) where
  /-- The concrete end class. -/
  kind : EndKind
  /-- REF `t` (element type; `none` for unit). -/
  t : Option (WIT.ClosedType RtId)
  /-- REF `state`. -/
  state : EndState := .idle
  /-- REF `other`. -/
  other : Option EndId := none
  /-- REF `buffer`. -/
  buffer : Option (BufferDesc E) := none
  /-- REF `owner`. -/
  owner : Option InstId := none
  /-- REF `index`. -/
  index : Option Nat := none
  /-- `Waitable` fields. -/
  common : WaitableCommon := {}
  deriving DecidableEq

/-- REF `ErrorContext` (L2664): an immutable shared object. -/
structure ErrorContext where
  /-- REF `debug_message : String`, the lifted tuple `(str, encoding, tagged_code_units)`,
  kept with its source pointer width (deviation D-a) so that `error-context.debug-message`
  can store it with the REF `store_string` algorithm after re-tagging (`StrVal.retag`). The
  deterministic profile's empty message is `⟨⟨"", .utf8, 0⟩, .i32⟩`. -/
  message : Value.StrVal
  deriving DecidableEq, Repr

/-- The REF deterministic-profile message `String(('', 'utf8', 0))` of
`canon_error_context_new` (L2671). -/
def ErrorContext.empty : ErrorContext := ⟨⟨⟨"", .utf8, 0⟩, .i32⟩⟩

/-! ## Tasks, callers and instances -/

/-- The kinds of internal nested calls whose REF `on_start`/`on_resolve` closures are not those
of `canon_lower` or the host:
* `realloc args result`: `LiftLowerContext.reallocate` (L625-641); `on_start` returns `args`
  (`[old, old_byte_length, alignment, new_byte_length]`), `on_resolve` fills `result` (`ptr`);
* `destructor rep`: a resource destructor call of `canon_resource_drop` (L2253-2259), when a
  model runs it without the `canon_lower` wrapper; `on_start` returns `[rep]`;
* `start`: a core start function, an implicitly sync `func()` task (`on_start` returns `[]`,
  `on_resolve` ignores its argument);
* `invoke args result`: a nested REF `Store.invoke` issued by a host function
  (`Call.hostInvoke`, L524-536); `on_start` returns `args`, `on_resolve r` records
  `result := some r` (`none`: not resolved yet; `some none`: resolved by cancellation, REF
  `on_resolve(None)`; `some (some vs)`: returned `vs`), which the host program reads back. -/
inductive SubKind where
  | realloc (args : List Value.Val) (result : Option Value.Val)
  | destructor (rep : Nat)
  | start
  | invoke (args : List Value.Val) (result : Option (Option (List Value.Val)))
  deriving DecidableEq, Repr

/-- The caller of a task: a defunctionalized REF `(on_start, on_resolve)` pair.
* `host call args depth`: the host (test harness or embedding) invoked the function through
  a top-level `Store.invoke`; `on_start` returns `args`, results are delivered to host call
  `call`; `depth` is `0` for a top-level invoke (nested invokes issued by host functions use
  `sub (.invoke ..)` records instead, see `SubKind.invoke`).
* `lower subtask cx flatArgs pos ft maxParams maxResults`: `canon_lower` (L2169-2207), with the
  caller's flat arguments, the position of the `CoreValueIter` over them, the callee's
  function type and `max_flat_params`/`max_flat_results`.
* `sub kind`: other internal nested calls (`SubKind`). -/
inductive Caller (E : CoreEngine) where
  | host (call : CallId) (args : List Value.Val) (depth : Nat)
  | lower (subtask : SubtaskId) (cx : LiftLowerContext E) (flatArgs : List FlatValue) (pos : Nat)
      (ft : WIT.FuncType Empty RtId) (maxParams maxResults : Nat)
  | sub (kind : SubKind)
  deriving DecidableEq

/-- REF `Task` (L392). `caller` names the `(on_start, on_resolve)` pair. -/
structure Task (E : CoreEngine) where
  /-- REF `ft`. -/
  ft : WIT.FuncType Empty RtId
  /-- REF `opts`. -/
  opts : CanonOpts E
  /-- REF `inst`. -/
  inst : InstId
  /-- REF `on_start`/`on_resolve`. -/
  caller : CallerId
  /-- REF `state`. -/
  state : TaskState := .initial
  /-- REF `num_borrows`. -/
  numBorrows : Nat := 0
  /-- REF `implicit_thread`. -/
  implicitThread : Option ThreadId := none
  /-- REF `threads`. -/
  threads : List ThreadId := []
  deriving DecidableEq

/-- An element of `ComponentInstance.handles` (L192). -/
inductive HandleEntry where
  | resource (h : HandleObjId)
  | waitable (w : Waitable)
  | wset (s : WsetId)
  | errCtx (x : ErrCtxId)
  deriving DecidableEq, Repr

/-- REF `ComponentInstance` (L190) without `store`. -/
structure InstState where
  /-- REF `handles`. -/
  handles : Table HandleEntry := .empty
  /-- REF `threads`. -/
  threads : Table ThreadId := .empty
  /-- REF `may_leave`. -/
  mayLeave : Bool := true
  /-- Ghost field (no REF counterpart; no program reads it): the current thread (REF
  `current_thread()`, `none` on a host frame) of the `reallocate` (L636-639) or `post_return`
  (L2093-2096) window that cleared `may_leave`, `none` once the flag is set back. Written by
  exactly the updates that write `mayLeave` (`LiftSt.setMayLeave`). -/
  leaveOwner : Option ThreadId := none
  /-- REF `backpressure`. -/
  backpressure : Nat := 0
  /-- REF `num_waiting_to_enter`. -/
  numWaitingToEnter : Nat := 0
  /-- REF `exclusive_thread`. -/
  exclusive : Option ThreadId := none
  deriving DecidableEq, Repr

/-- A component-level function value (REF `FuncInst`, L385-389): a lifted core function
(`Store.lift`, L542) or a host function (choice point E1). -/
inductive CFuncInst (E : CoreEngine) where
  | lifted (core : E.FuncAddr) (ft : WIT.FuncType Empty RtId) (opts : CanonOpts E) (inst : InstId)
  | host (ft : WIT.FuncType Empty RtId) (h : HostFuncId)
  deriving DecidableEq

/-- The function type of a component function value. -/
def CFuncInst.ft {E : CoreEngine} : CFuncInst E → WIT.FuncType Empty RtId
  | .lifted _ ft _ _ => ft
  | .host ft _ => ft

end Silmaril.Wasm.Component.Runtime
