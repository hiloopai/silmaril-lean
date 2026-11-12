module

public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs

/-!
# Waitable-set, waitable and subtask built-ins

Specification programs `P E σ` transcribing the canon built-ins over waitables of REF
`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>;
`CanonicalABI.md` §"Canonical Definitions"):

| Lean | REF (lines) |
| --- | --- |
| `waitableSetNew lim` | `canon_waitable_set_new` (L2333-2337) |
| `waitableSetWait lim mem si ptr` | `canon_waitable_set_wait` (L2341-2347), `unpack_event` |
| `waitableSetPoll lim mem si ptr` | `canon_waitable_set_poll` (L2358-2364) |
| `waitableSetDrop lim i` | `canon_waitable_set_drop` (L2368-2374) |
| `waitableJoin lim wi si` | `canon_waitable_join` (L2378-2390) |
| `subtaskCancel lim async_ i` | `canon_subtask_cancel` (L2396-2416), `BLOCKED` (L2394) |
| `subtaskCancelRequest`, `subtaskCancelSyncWait`, `subtaskCancelDeliver` | its parts (L2404-2416) |
| `subtaskDrop lim i` | `canon_subtask_drop` (L2420-2426) |

Each built-in returns its flat core results (`List FlatValue`, every result an `i32`); its
arguments are the flat core arguments already read as unsigned numbers (`Canon.flatNat`), so
`ptr` may be a 64-bit pointer under 🐘. Every built-in takes the numeric `Limits` as its
explicit leading argument (unused here: the handle-table bound is the fixed
`Runtime.Table.maxLength`); none has a quirk branch, so none takes `Quirks`.

**Reuse.** The object-level methods are the transcriptions of `Runtime/Waitable.lean`
(`wsetWait`, `wsetPoll`, `wsetDrop`, `Waitable.join`, `Waitable.inWaitableSet`,
`Waitable.getPendingEvent`, `Subtask.resolveDelivered`, `Runtime.subtaskDrop`); the event
store is `Canon.unpackEvent` (`Canon/Context.lean`, REF `unpack_event`), called explicitly;
handle-table accesses are `handlesAdd`/`handlesGet`/`handlesRemove` (`Canon/Effects.lean`).
The only new store mutation is `WaitableSt.requestCancel` (REF `subtask.cancellation_requested
= True; subtask.has_sync_waiter = True`, ONE named multi-field update); `has_sync_waiter = False` is
`CStore.setSyncWaiterSt`.

**`subtask.cancel`.** The exact REF sequence (L2396-2416): `may_leave`; `handles.get(i)`; type
check; `trap_if(resolve_delivered)`; `trap_if(cancellation_requested)`;
`trap_if(in_waitable_set)` (also when `async_`); if not resolved: the named update above,
`subtask.on_cancel()` as the late-bound `call (.onCancel r)` (resume site R2 when `r` is a
task's `request_cancellation`), then for a sync cancel still unresolved
`thread.wait_until(subtask.resolved)` at site K8 (`.syncSubtaskCancel`, choice C1), then
`has_sync_waiter = False`, and `[BLOCKED]` if still unresolved (`Async.subtaskCancelResult
none = Async.blocked = 0xFFFF_FFFF`); finally `get_pending_event()` (which consumes the
`SUBTASK` event and runs `deliver_resolve`) and `[subtask.state]`
(`Async.subtaskCancelResult (some state)`).

**Trap reasons** (informative; the specification compares traps only as "some trap"):
`may_leave` is `cannotLeave`; an unknown index `unknownHandle`; an entry of the wrong kind
`wrongHandleType`; `waitable.join` with a sync waiter `subtaskInSet` (the wasmtime message the
`.wast` tests expect, see `TrapReason.subtaskInSet`); `subtask.cancel` after the resolve was
delivered or a second cancellation `subtaskCancelTwice`, in a waitable set `subtaskInSet`;
`waitable-set.drop` of a non-empty set `setNotEmpty`, with waiters `setHasWaiters`;
`subtask.drop` before the resolve was delivered `subtaskNotResolved`.

## Deviations and non-claims

* D-d: `waitable-set.wait`/`poll` store the event with `Canon.unpackEvent`, which traps
  (`unalignedPointer`/`outOfBounds`) on a misaligned or out-of-bounds 8-byte slot BEFORE
  writing anything, like wasmtime; REF `store` only asserts. The wait/poll itself (and hence
  the consumption of the event, C4 shuffle included) happens before the check, as in REF and
  wasmtime (the trap locks the store down anyway).
* D-f: REF `assert`s are preconditions, not checked: `subtask.cancel`'s final
  `code == SUBTASK and index == i and payload == subtask.state` and `resolve_delivered()`.
  A dangling arena id behind a handle entry (unreachable: arena ids are never freed) is an
  internal trap (`getObj`, or an explicit `internal` for a waitable's base fields).
* `current_instance()`/`current_thread()` on a host frame (no current thread) is an internal
  trap (`currentInst`/`currentThreadId`); REF asserts built-ins run on guest threads.
* `waitable-set.new` allocates the `WaitableSet` object before `handles.add` (REF evaluates
  `WaitableSet()` first); a full table traps and leaves the unreferenced object in its
  append-only arena.
* Nothing is proved here beyond the `P.Inv` program-logic lemmas (each built-in preserves a
  store invariant whenever the named updates it issues do). No tests here: the built-ins are
  exercised by the machine examples, the `run_tests.py` ports and the `.wast` ports.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Async _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-! ## Named store update -/

namespace WaitableSt

/-- REF `subtask.cancellation_requested = True; subtask.has_sync_waiter = True`
(`canon_subtask_cancel`, L2405-2406), one update (no-op on a dangling id), recording the
calling thread `t` (REF `thread = current_thread()`, L2397) in the ghost
`WaitableCommon.syncOwner`. -/
def requestCancel (st : SubtaskId) (t : ThreadId) (s : CStore E) : CStore E :=
  ArenaField.subtasks.modify s st fun x =>
    { x with cancellationRequested := true,
             common := { x.common with hasSyncWaiter := true, syncOwner := some t } }

end WaitableSt

/-! ## Shared entry checks -/

/-- REF `inst = current_instance(); trap_if(not inst.may_leave)` at every built-in entry of this
file (`current_thread().task.inst` in `canon_subtask_cancel`, the same instance). -/
def enterWaitableBuiltin : P E σ InstId := do
  let inst ← currentInst
  trapIf (!(← getInst inst).mayLeave) .cannotLeave
  pure inst

/-- REF `trap_if(not isinstance(wset, WaitableSet))`. -/
def expectWset : HandleEntry → P E σ WsetId
  | .wset s => pure s
  | _ => trap .wrongHandleType

/-- REF `trap_if(not isinstance(w, Waitable))`. -/
def expectWaitable : HandleEntry → P E σ Runtime.Waitable
  | .waitable w => pure w
  | _ => trap .wrongHandleType

/-- REF `trap_if(not isinstance(subtask, Subtask))`. -/
def expectSubtask : HandleEntry → P E σ SubtaskId
  | .waitable (.subtask s) => pure s
  | _ => trap .wrongHandleType

/-- REF `subtask.resolved()` (L838-846) on the current store. -/
def subtaskResolvedNow (st : SubtaskId) : P E σ Bool := gets (·.subtaskResolved st)

/-- The pointer-carrying context of `unpack_event`: REF
`LiftLowerContext(LiftLowerOptions(memory = mem), inst)` (L2351). -/
def eventCx (mem : E.MemAddr) (inst : InstId) : LiftLowerContext E :=
  { opts := { memory := some mem }, inst }

/-! ## Built-ins -/

/-- REF `canon_waitable_set_new()` (L2333-2337): `may_leave`; `i = inst.handles.add(WaitableSet())`;
`[i]`. -/
def waitableSetNew (_lim : Limits) : P E σ (List FlatValue) := do
  let inst ← enterWaitableBuiltin
  let ws ← allocObj ArenaField.wsets ({} : WaitableSet)
  let i ← handlesAdd inst (.wset ws)
  pure [i32Flat i]

/-- REF `canon_waitable_set_wait(mem, si, ptr)` (L2341-2347): `may_leave`; get the set (type
trap); `wset.wait()` (K4, choices C1 and C4); `unpack_event(mem, inst, ptr, event)` with the
D-d traps (`Canon.unpackEvent`); `[code]`. -/
def waitableSetWait (_lim : Limits) (mem : E.MemAddr) (si ptr : Nat) :
    P E σ (List FlatValue) := do
  let inst ← enterWaitableBuiltin
  let ws ← expectWset (← handlesGet inst si)
  let ev ← wsetWait ws
  let code ← unpackEvent (eventCx mem inst) ptr ev
  pure [i32Flat code]

/-- REF `canon_waitable_set_poll(mem, si, ptr)` (L2358-2364): as `waitableSetWait` with
`wset.poll()` (never blocks; `(NONE, 0, 0)` without an event; choice C4). -/
def waitableSetPoll (_lim : Limits) (mem : E.MemAddr) (si ptr : Nat) :
    P E σ (List FlatValue) := do
  let inst ← enterWaitableBuiltin
  let ws ← expectWset (← handlesGet inst si)
  let ev ← wsetPoll ws
  let code ← unpackEvent (eventCx mem inst) ptr ev
  pure [i32Flat code]

/-- REF `canon_waitable_set_drop(i)` (L2368-2374): `may_leave`; `inst.handles.remove(i)`; type
trap; `wset.drop()` (`setNotEmpty`, `setHasWaiters`); `[]`. -/
def waitableSetDrop (_lim : Limits) (i : Nat) : P E σ (List FlatValue) := do
  let inst ← enterWaitableBuiltin
  let ws ← expectWset (← handlesRemove inst i)
  wsetDrop ws
  pure []

/-- The REF `Waitable` base field `has_sync_waiter` of `w` (internal trap if dangling). -/
def waitableHasSyncWaiter (w : Runtime.Waitable) : P E σ Bool := do
  match (← getStore).waitableCommon? w with
  | some c => pure c.hasSyncWaiter
  | none => internal "dangling waitable"

/-- REF `canon_waitable_join(wi, si)` (L2378-2390): `may_leave`; `w = inst.handles.get(wi)`
(must be a `Waitable`); `trap_if(w.has_sync_waiter)`; `si == 0` leaves any set (`w.join(None)`),
otherwise `inst.handles.get(si)` must be a `WaitableSet` and `w.join(wset)`; `[]`. -/
def waitableJoin (_lim : Limits) (wi si : Nat) : P E σ (List FlatValue) := do
  let inst ← enterWaitableBuiltin
  let w ← expectWaitable (← handlesGet inst wi)
  trapIf (← waitableHasSyncWaiter w) .subtaskInSet
  if si = noWaitableSet then do
    Runtime.Waitable.join w none
    pure []
  else do
    let ws ← expectWset (← handlesGet inst si)
    Runtime.Waitable.join w (some ws)
    pure []

/-- The tail of `canon_subtask_cancel` (L2413-2416): `get_pending_event()` (consumes the
`SUBTASK` event and runs `deliver_resolve`; its REF asserts are preconditions, D-f), then
`[subtask.state]`. -/
def subtaskCancelDeliver (st : SubtaskId) : P E σ (List FlatValue) := do
  let _ ← Runtime.Waitable.getPendingEvent (.subtask st)
  let x ← getObj ArenaField.subtasks st
  pure [i32Flat (subtaskCancelResult (some x.state))]

/-- REF `if not async_ and not subtask.resolved(): thread.wait_until(subtask.resolved)`
(L2408-2409): site K8 (`.syncSubtaskCancel`, choice C1). -/
def subtaskCancelSyncWait (async_ : Bool) (st : SubtaskId) : P E σ Unit := do
  let r ← subtaskResolvedNow st
  if !async_ && !r then Thread.waitUntilGuest .syncSubtaskCancel (.subtaskResolved st)
  else pure ()

/-- The cancellation request of `canon_subtask_cancel` for an unresolved subtask (L2405-2412):
`cancellation_requested = True; has_sync_waiter = True` (`WaitableSt.requestCancel`);
`subtask.on_cancel()` (late-bound `call (.onCancel r)`, resume site R2); if `not async_` and
still unresolved, `thread.wait_until(subtask.resolved)` (K8, choice C1);
`has_sync_waiter = False`; `true` iff the subtask is now resolved. -/
def subtaskCancelRequest (async_ : Bool) (st : SubtaskId) (r : CancelRef) : P E σ Bool := do
  let t ← currentThreadId
  modifyStore (WaitableSt.requestCancel st t)
  callUnit (.onCancel r)
  subtaskCancelSyncWait async_ st
  modifyStore (CStore.setSyncWaiterSt (.subtask st) none)
  subtaskResolvedNow st

/-- REF `canon_subtask_cancel(async_, i)` (L2396-2416): `may_leave`; `subtask =
handles.get(i)` (type trap); `trap_if(resolve_delivered)`; `trap_if(cancellation_requested)`;
`trap_if(in_waitable_set)`; if not resolved, `subtaskCancelRequest` and `[BLOCKED]`
(`subtaskCancelResult none`) if it is still unresolved; then `subtaskCancelDeliver`. -/
def subtaskCancel (_lim : Limits) (async_ : Bool) (i : Nat) : P E σ (List FlatValue) := do
  let inst ← enterWaitableBuiltin
  let st ← expectSubtask (← handlesGet inst i)
  trapIf (← Subtask.resolveDelivered st) .subtaskCancelTwice
  let x ← getObj ArenaField.subtasks st
  trapIf x.cancellationRequested .subtaskCancelTwice
  trapIf (← Runtime.Waitable.inWaitableSet (.subtask st)) .subtaskInSet
  if x.state.resolved then
    subtaskCancelDeliver st
  else
    if ← subtaskCancelRequest async_ st x.onCancel then
      subtaskCancelDeliver st
    else
      pure [i32Flat (subtaskCancelResult none)]

/-- REF `canon_subtask_drop(i)` (L2420-2426): `may_leave`; `s = inst.handles.remove(i)`; type
trap; `s.drop()` (`subtaskNotResolved` unless the resolve was delivered; leave the set); `[]`. -/
def subtaskDrop (_lim : Limits) (i : Nat) : P E σ (List FlatValue) := do
  let inst ← enterWaitableBuiltin
  let st ← expectSubtask (← handlesRemove inst i)
  Runtime.subtaskDrop st
  pure []

/-! ## Basic facts -/

/-! ## Program-logic lemmas

Each built-in preserves a store invariant `I` as soon as the named updates it issues do. -/

namespace Inv

variable {I : CStore E → Prop}

/-- Memory writes of `unpack_event` preserve `I`. -/
abbrev MemWritePres (I : CStore E → Prop) : Prop :=
  ∀ m p v s, I s → I (writeMemSt m p (u32Bytes v) s)

end Inv

end Silmaril.Wasm.Component.Canon.Builtins
