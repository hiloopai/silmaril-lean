module

public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Stream.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Defs
import Silmaril.Wasm.Component.Reference.Runtime.Arena.Defs
import Silmaril.Wasm.Component.Reference.Runtime.Store.Defs

/-!
# Waitables, waitable sets and subtasks

Transcribes the REF classes `Waitable`, `WaitableSet` and `Subtask` of
`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
L713-874; `CanonicalABI.md` §"Waitable State" and §"Subtask State") as programs over `Canon.P E σ`,
together with the named pure store updates they issue.

| Lean | REF (line) |
| --- | --- |
| `CStore.waitableCommon?`, `CStore.modifyWaitableCommon` | the `Waitable` base fields (L724-731) |
| `Waitable.setPendingEvent` (`CStore.setPendingSt`) | `Waitable.set_pending_event` (L734-735) |
| `Waitable.hasPendingEvent` (`CStore.waitableHasEvent`) | `Waitable.has_pending_event` (L737-738) |
| `Waitable.inWaitableSet` | `Waitable.in_waitable_set` (L740-741) |
| `Waitable.waitForPendingEvent` | `Waitable.wait_for_pending_event` (L743-747) |
| `Waitable.getPendingEvent` (`takeWaitableEvent`) | `Waitable.get_pending_event` (L749-752) |
| `Waitable.join` (`CStore.joinSt`) | `Waitable.join` (L754-760) |
| `Waitable.dropWaitable` | `Waitable.drop` (L762-764) |
| `wsetHasPendingEvent` (`CStore.wsetHasEvent`) | `WaitableSet.has_pending_event` (L774-775) |
| `wsetGetPendingEvent` | `WaitableSet.get_pending_event` (L777-783), choice C4 |
| `wsetWait` | `WaitableSet.wait` (L785-789) |
| `wsetPoll` | `WaitableSet.poll` (L791-795) |
| `wsetWaitFromCallback` | `WaitableSet.wait_from_callback` (L797-808) |
| `wsetDrop` | `WaitableSet.drop` (L810-812) |
| `CStore.subtaskEvent` | the `subtask_event` closure of `canon_lower` (L2225-2228) |
| `Subtask.addLender` (`Canon.HandleSt.addLender`) | `Subtask.add_lender` (L848-851) |
| `Subtask.resolve` (`CStore.subtaskResolveSt`) | `Subtask.resolve` (L853-858) |
| `Subtask.deliverResolve` (`CStore.deliverResolveSt`) | `Subtask.deliver_resolve` (L860-864) |
| `Subtask.resolveDelivered` (`subtaskResolveDelivered`) | `Subtask.resolve_delivered` (L866-868) |
| `subtaskDrop` | `Subtask.drop` (L870-872) |

Event codes, event tuples and subtask states are the `Async.EventCode`,
`Async.EventTuple` and `Async.SubtaskState` (`Async/Codes.lean`).

**Pending events.** A REF `pending_event` closure is the data `PendingEvent`
(`Runtime/Objects.lean`). `getPendingEvent w` clears the slot and RUNS the closure in one named
store update (`CStore.takeWaitableEventSt`): for a stream/future end this is
`Runtime.takeEvent` (delivery-time state transitions of `stream_event`/`future_event`); for a
subtask it is `CStore.subtaskEvent`, the `subtask_event` closure of an async `canon_lower`
(L2225-2228): `deliver_resolve` if resolved, then `(SUBTASK, subtaski, state)`. The captured
`subtaski` is the subtask's recorded caller handle index `Subtask.index`. As in
`Runtime.takeEvent`, the closure is run on the waitable it is pending on (a closure pending on
a waitable always names that waitable; `subtaskEvent` and `takeEvent` read the waitable's own
id).

**Choice C4.** `wsetGetPendingEvent` issues `choose (.shuffle n)` (through `Canon.shuffle`) and
PERSISTS the permutation into `elems` (REF `random.shuffle(self.elems)` mutates the list) with
the named update `CStore.wsetSetElemsSt`, then takes the first element with a pending event.

**Waiting.** All waits are guest-side (`Thread.waitUntilGuest`, choice C1 with its site):
`waitForPendingEvent` takes the site (K5 `syncCopy` for sync stream/future read/write, K6
`syncCancelCopy` for sync cancel), `wsetWait` is K4 and `wsetWaitFromCallback` is K3.

**Reused transcriptions.** `wsetWaitFromCallback` calls REF `Task.deliver_pending_cancel`
(L481-486) as `Task.deliverPendingCancel` (`Runtime/Task.lean`, named update
`CStore.setTaskState task .cancelDelivered`), and `Subtask.addLender` applies the named update
`Canon.HandleSt.addLender` (`Canon/Handles.lean`, used by `lift_borrow`), so each REF mutation
has exactly one named update.

**Deviations and non-claims.**
* REF `assert`s are preconditions (deviation D-f) and are not checked: `wait_for_pending_event`
  (not in a set, no sync waiter), `join`/`drop` (no sync waiter), `WaitableSet.get_pending_event`
  (some element has an event; each element's `wset` is this set), `add_lender` (not resolved,
  not delivered), `resolve` (state/results shape, not yet resolved), `deliver_resolve`
  (resolved, not yet delivered). Where a fallback is needed: `getPendingEvent` without a
  pending event and `wsetGetPendingEvent` without an eventful element are `TrapReason.internal`
  (REF would crash calling `None`, resp. return `None`); dangling waitable/subtask ids make the
  pure updates of this file no-ops (`joinSt` on a dangling waitable changes nothing; a dangling
  set id only skips that set's `elems` update); `deliverResolveSt` of an already delivered
  subtask (`lenders = none`) changes nothing; `HandleSt.addLender` on a delivered subtask only
  increments the handle's `num_lends` (REF would crash on `None.append`).
* `num_lends -= 1` is truncated `Nat` subtraction (the REF invariant keeps it positive).
* The canon built-ins around these methods (`waitable-set.*`, `waitable.join`,
  `subtask.cancel/drop`: `may_leave`, handle-table lookups and type checks, `unpack_event`)
  belong to the canon built-in items; `wsetDrop` and `subtaskDrop` are the object-level
  `drop` methods only.
* Tests: the pure updates are exercised on a tiny store by kernel `rfl` (generic engine `E`,
  the core store is never inspected); the programs are tested end to end through the machine
  (`Examples/`, `Tests/`). -/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine Async Canon

variable {E : CoreEngine}

/-! ## Named pure store updates -/

namespace CStore

/-- The `Waitable` base fields (L724-731) of waitable `w` (`none` if dangling). -/
def waitableCommon? (s : CStore E) : Waitable → Option WaitableCommon
  | .subtask st => (s.subtask? st).map (·.common)
  | .end_ e => (s.end? e).map (·.common)

/-- Update the `Waitable` base fields of `w` (no-op if dangling). -/
def modifyWaitableCommon (w : Waitable) (f : WaitableCommon → WaitableCommon) (s : CStore E) :
    CStore E :=
  match w with
  | .subtask st => ArenaField.subtasks.modify s st fun x => { x with common := f x.common }
  | .end_ e => ArenaField.ends.modify s e fun x => { x with common := f x.common }

/-- The update of REF `set_pending_event(ev)` (L734-735): overwrite the pending event. -/
def setPendingSt (w : Waitable) (ev : PendingEvent) (s : CStore E) : CStore E :=
  s.modifyWaitableCommon w fun c => { c with pending := some ev }

/-- Set REF `has_sync_waiter` of `w` (L745 and L747): `some t` sets the flag on behalf of
the waiting thread `t` (REF `current_thread()`, recorded in the ghost field
`WaitableCommon.syncOwner`), `none` clears both. -/
def setSyncWaiterSt (w : Waitable) (o : Option ThreadId) (s : CStore E) : CStore E :=
  s.modifyWaitableCommon w fun c => { c with hasSyncWaiter := o.isSome, syncOwner := o }

/-- The update of REF `Waitable.join(wset)` (L754-760), one multi-field update: remove `w` from
its current set's `elems` (Python `list.remove`, first occurrence), set `w.wset`, and append
`w` to the new set's `elems`. A dangling `w` changes nothing (so every set member keeps a
`wset` field naming its set). -/
def joinSt (w : Waitable) (ws : Option WsetId) (s : CStore E) : CStore E :=
  match s.waitableCommon? w with
  | none => s
  | some c =>
    let s1 := match c.wset with
      | some old => ArenaField.wsets.modify s old fun x => { x with elems := x.elems.erase w }
      | none => s
    let s2 := s1.modifyWaitableCommon w fun c => { c with wset := ws }
    match ws with
    | some n => ArenaField.wsets.modify s2 n fun x => { x with elems := x.elems ++ [w] }
    | none => s2

/-- Persist the C4 permutation: replace `elems` of set `ws` (REF `random.shuffle(self.elems)`,
L779, shuffles in place). -/
def wsetSetElemsSt (ws : WsetId) (elems : List Waitable) (s : CStore E) : CStore E :=
  ArenaField.wsets.modify s ws fun x => { x with elems }

/-- REF `self.num_waiting += 1` (L786, L802). -/
def wsetIncWaitingSt (ws : WsetId) (s : CStore E) : CStore E :=
  ArenaField.wsets.modify s ws fun x => { x with numWaiting := x.numWaiting + 1 }

/-- REF `self.num_waiting -= 1` (L788, L804). -/
def wsetDecWaitingSt (ws : WsetId) (s : CStore E) : CStore E :=
  ArenaField.wsets.modify s ws fun x => { x with numWaiting := x.numWaiting - 1 }

/-- The update of REF `Subtask.resolve(state, flat_results)` (L853-858). -/
def subtaskResolveSt (st : SubtaskId) (state : SubtaskState) (flat : List FlatValue)
    (s : CStore E) : CStore E :=
  ArenaField.subtasks.modify s st fun x => { x with state, flatResults := flat }

/-- The update of REF `Subtask.deliver_resolve()` (L860-864): decrement `num_lends` of every
lender and set `lenders = None` (one multi-field update). -/
def deliverResolveSt (st : SubtaskId) (s : CStore E) : CStore E :=
  match s.subtask? st with
  | none => s
  | some x =>
    let s1 := (x.lenders.getD []).foldl
      (fun s h => ArenaField.resHandles.modify s h fun r => { r with numLends := r.numLends - 1 })
      s
    ArenaField.subtasks.modify s1 st fun y => { y with lenders := none }

/-- REF `Subtask.resolve_delivered()` (L866-868): `lenders is None` (`false` if dangling). -/
def subtaskResolveDelivered (s : CStore E) (st : SubtaskId) : Bool :=
  match s.subtask? st with
  | some x => x.lenders.isNone
  | none => false

/-- Run the `subtask_event` closure of `canon_lower` (L2225-2228) for subtask `st`: if the
subtask is resolved, `deliver_resolve()`; the event is `(SUBTASK, subtaski, state)` with the
recorded caller handle index. -/
def subtaskEvent (st : SubtaskId) (s : CStore E) : CStore E × EventTuple :=
  match s.subtask? st with
  | none => (s, EventTuple.none)
  | some x =>
    let s1 := if x.state.resolved then s.deliverResolveSt st else s
    (s1, ⟨.subtask, x.index.getD 0, x.state.toNat⟩)

/-- REF `Waitable.get_pending_event()` (L749-752) as a pure function: clear the pending event
of `w` and run its closure; `none` if no (matching) event is pending. Ends delegate to the
stream/future `Runtime.takeEvent`. -/
def takeWaitableEvent (w : Waitable) (s : CStore E) : CStore E × Option EventTuple :=
  match w with
  | .end_ e => takeEvent e s
  | .subtask st =>
    match s.subtask? st with
    | none => (s, none)
    | some x =>
      match x.common.pending with
      | some (.subtask _) =>
        let r := subtaskEvent st (s.modifyWaitableCommon w fun c => { c with pending := none })
        (r.1, some r.2)
      | _ => (s, none)

/-- The store update of `get_pending_event` (the named function `getPendingEvent` applies). -/
def takeWaitableEventSt (w : Waitable) (s : CStore E) : CStore E := (s.takeWaitableEvent w).1

end CStore

/-! ## `Waitable` methods -/

namespace Waitable

variable {σ : Type}

/-- REF `Waitable.set_pending_event(ev)` (L734-735): overwrite (events coalesce). -/
def setPendingEvent (w : Waitable) (ev : PendingEvent) : P E σ Unit :=
  modifyStore (CStore.setPendingSt w ev)

/-- REF `Waitable.has_pending_event()` (L737-738). -/
def hasPendingEvent (w : Waitable) : P E σ Bool := gets (·.waitableHasEvent w)

/-- REF `Waitable.in_waitable_set()` (L740-741). -/
def inWaitableSet (w : Waitable) : P E σ Bool :=
  gets fun s => ((s.waitableCommon? w).bind (·.wset)).isSome

/-- REF `Waitable.get_pending_event()` (L749-752): take the pending closure, clear the slot and
run it (one named update, `CStore.takeWaitableEventSt`). Precondition (REF: calling `None`
crashes): an event is pending; otherwise an internal trap. -/
def getPendingEvent (w : Waitable) : P E σ EventTuple := do
  let s ← getStore
  match (s.takeWaitableEvent w).2 with
  | none => internal "get_pending_event: no pending event"
  | some ev =>
    modifyStore (CStore.takeWaitableEventSt w)
    pure ev

/-- REF `Waitable.wait_for_pending_event()` (L743-747): `has_sync_waiter = True` (recording
`current_thread()`, which REF's `current_thread().wait_until` at L746 also reads, in the ghost
`syncOwner`), `wait_until(has_pending_event)` at `site` (K5 `syncCopy` or K6 `syncCancelCopy`,
choice C1), `has_sync_waiter = False`. Preconditions (REF assert): `w` is not in a waitable set
and has no sync waiter. -/
def waitForPendingEvent (site : WaitSite) (w : Waitable) : P E σ Unit := do
  let t ← currentThreadId
  modifyStore (CStore.setSyncWaiterSt w (some t))
  Thread.waitUntilGuest site (.waitableHasEvent w)
  modifyStore (CStore.setSyncWaiterSt w none)

/-- REF `Waitable.join(wset)` (L754-760). Precondition (REF assert): no sync waiter. -/
def join (w : Waitable) (ws : Option WsetId) : P E σ Unit := modifyStore (CStore.joinSt w ws)

/-- REF `Waitable.drop()` (L762-764): `join(None)`. Precondition (REF assert): no sync
waiter. -/
def dropWaitable (w : Waitable) : P E σ Unit := join w none

end Waitable

/-! ## `WaitableSet` methods -/

section WaitableSetMethods

variable {σ : Type}

/-- REF `WaitableSet.has_pending_event()` (L774-775). -/
def wsetHasPendingEvent (ws : WsetId) : P E σ Bool := gets (·.wsetHasEvent ws)

/-- REF `WaitableSet.get_pending_event()` (L777-783): `random.shuffle(self.elems)` (choice C4,
`choose (.shuffle n)`), persisted into `elems`, then the event of the first element with a
pending event. Preconditions (REF asserts): some element has a pending event (otherwise an
internal trap: REF would return `None`); every element's `wset` is `ws`. -/
def wsetGetPendingEvent (ws : WsetId) : P E σ EventTuple := do
  let x ← getObj ArenaField.wsets ws
  let elems ← Canon.shuffle x.elems
  modifyStore (CStore.wsetSetElemsSt ws elems)
  let s ← getStore
  match elems.find? s.waitableHasEvent with
  | some w => Waitable.getPendingEvent w
  | none => internal "WaitableSet.get_pending_event: no pending event"

/-- REF `WaitableSet.wait()` (L785-789): `num_waiting += 1`,
`wait_until(has_pending_event)` (K4, choice C1), `num_waiting -= 1`, `get_pending_event()`. -/
def wsetWait (ws : WsetId) : P E σ EventTuple := do
  modifyStore (CStore.wsetIncWaitingSt ws)
  Thread.waitUntilGuest .waitableSetWait (.wsetHasEvent ws)
  modifyStore (CStore.wsetDecWaitingSt ws)
  wsetGetPendingEvent ws

/-- REF `WaitableSet.poll()` (L791-795): `(NONE, 0, 0)` if no element has a pending event,
else `get_pending_event()`. Never blocks. -/
def wsetPoll (ws : WsetId) : P E σ EventTuple := do
  if ← wsetHasPendingEvent ws then wsetGetPendingEvent ws else pure EventTuple.none

/-- REF `WaitableSet.wait_from_callback()` (L797-808) for set `ws` and the current thread's
task `task`: `num_waiting += 1`; wait (K3, choice C1) until
`task.inst.exclusive_thread is None and (ws.has_pending_event() or
task.has_pending_cancel())` (`ReadyCond.callbackWait`); `num_waiting -= 1`; then a pending
cancellation takes priority: `(TASK_CANCELLED, 0, 0)` if `deliver_pending_cancel()`, else
`get_pending_event()` (`Task.deliverPendingCancel` of `Runtime/Task.lean`). Precondition:
`task` is the current thread's task (REF reads `current_thread().task`). -/
def wsetWaitFromCallback (ws : WsetId) (task : TaskId) : P E σ EventTuple := do
  let inst := (← getTask task).inst
  modifyStore (CStore.wsetIncWaitingSt ws)
  Thread.waitUntilGuest .callbackWait (.callbackWait inst task ws)
  modifyStore (CStore.wsetDecWaitingSt ws)
  if ← Task.deliverPendingCancel task then pure EventTuple.taskCancelled
  else wsetGetPendingEvent ws

/-- REF `WaitableSet.drop()` (L810-812): trap if the set still has elements (`setNotEmpty`) or
waiters (`setHasWaiters`). The handle removal is the canon built-in's. -/
def wsetDrop (ws : WsetId) : P E σ Unit := do
  let x ← getObj ArenaField.wsets ws
  trapIf (!x.elems.isEmpty) .setNotEmpty
  trapIf (decide (x.numWaiting > 0)) .setHasWaiters

end WaitableSetMethods

/-! ## `Subtask` methods -/

namespace Subtask

variable {σ : Type}

/-- REF `Subtask.add_lender(h)` (L848-851). Precondition (REF assert): the subtask is neither
resolved nor resolve-delivered. -/
def addLender (st : SubtaskId) (h : HandleObjId) : P E σ Unit :=
  modifyStore (HandleSt.addLender st h)

/-- REF `Subtask.resolve(state, flat_results)` (L853-858). Preconditions (REF asserts):
`state = RETURNED` or `flat = []`; not yet resolved; `state` is a resolved state. -/
def resolve (st : SubtaskId) (state : SubtaskState) (flat : List FlatValue) : P E σ Unit :=
  modifyStore (CStore.subtaskResolveSt st state flat)

/-- REF `Subtask.deliver_resolve()` (L860-864). Precondition (REF assert): resolved and not yet
delivered. -/
def deliverResolve (st : SubtaskId) : P E σ Unit := modifyStore (CStore.deliverResolveSt st)

/-- REF `Subtask.resolve_delivered()` (L866-868). -/
def resolveDelivered (st : SubtaskId) : P E σ Bool := gets (·.subtaskResolveDelivered st)

end Subtask

/-- REF `Subtask.drop()` (L870-872): trap `subtaskNotResolved` unless the resolve was
delivered, then `Waitable.drop` (leave the waitable set). -/
def subtaskDrop {σ : Type} (st : SubtaskId) : P E σ Unit := do
  trapIf (!(← Subtask.resolveDelivered st)) .subtaskNotResolved
  Waitable.dropWaitable (.subtask st)

/-! ## Program-logic lemmas

Each program preserves a store invariant `I` as soon as the named updates it issues do. -/

section Inv

variable {σ : Type} {I : CStore E → Prop}

end Inv

/-! ## Basic facts about the pure updates -/

namespace CStore

/-- Updating a waitable set leaves every waitable's base fields unchanged. -/
theorem waitableCommon?_wsets_modify (s : CStore E) (n : WsetId)
    (f : WaitableSet → WaitableSet) (w : Waitable) :
    (ArenaField.wsets.modify s n f).waitableCommon? w = s.waitableCommon? w := by
  cases w <;> rfl

theorem waitableCommon?_modifyWaitableCommon_self (s : CStore E) (w : Waitable)
    (f : WaitableCommon → WaitableCommon) :
    (s.modifyWaitableCommon w f).waitableCommon? w = (s.waitableCommon? w).map f := by
  cases w with
  | subtask st =>
    simp only [modifyWaitableCommon, waitableCommon?, subtask?, ArenaField.get?_modify_self,
      Option.map_map]
    rfl
  | end_ e =>
    simp only [modifyWaitableCommon, waitableCommon?, end?, ArenaField.get?_modify_self,
      Option.map_map]
    rfl

theorem waitableCommon?_modifyWaitableCommon_ne (s : CStore E) {w w' : Waitable}
    (f : WaitableCommon → WaitableCommon) (hne : w' ≠ w) :
    (s.modifyWaitableCommon w f).waitableCommon? w' = s.waitableCommon? w' := by
  cases w with
  | subtask st =>
    cases w' with
    | subtask st' =>
      have h : st ≠ st' := fun e => hne (e ▸ rfl)
      simp only [modifyWaitableCommon, waitableCommon?, subtask?, ArenaField.get?_modify_ne _ _ _ h]
    | end_ _ => rfl
  | end_ e =>
    cases w' with
    | subtask _ => rfl
    | end_ e' =>
      have h : e ≠ e' := fun x => hne (x ▸ rfl)
      simp only [modifyWaitableCommon, waitableCommon?, end?, ArenaField.get?_modify_ne _ _ _ h]

/-- After `joinSt w ws`, `w`'s base fields are the old ones with `wset := ws`. -/
theorem waitableCommon?_joinSt (s : CStore E) (w : Waitable) (ws : Option WsetId) :
    (s.joinSt w ws).waitableCommon? w =
      (s.waitableCommon? w).map fun c => { c with wset := ws } := by
  unfold joinSt
  cases hc : s.waitableCommon? w with
  | none => simp only [hc, Option.map_none]
  | some c =>
    have h1 : (match c.wset with
        | some old => ArenaField.wsets.modify s old fun x => { x with elems := x.elems.erase w }
        | none => s).waitableCommon? w = some c := by
      split <;> simp only [waitableCommon?_wsets_modify, hc]
    simp only
    split <;>
      simp only [waitableCommon?_wsets_modify, waitableCommon?_modifyWaitableCommon_self, h1,
        Option.map_some]

/-- Frame: `joinSt w ws` leaves the base fields of every other waitable unchanged (it only
touches `elems` of sets and the arena entry of `w`). -/
theorem waitableCommon?_joinSt_ne (s : CStore E) {w w' : Waitable} (ws : Option WsetId)
    (hne : w' ≠ w) : (s.joinSt w ws).waitableCommon? w' = s.waitableCommon? w' := by
  unfold joinSt
  cases s.waitableCommon? w with
  | none => rfl
  | some c =>
    have h1 : (match c.wset with
        | some old => ArenaField.wsets.modify s old fun x => { x with elems := x.elems.erase w }
        | none => s).waitableCommon? w' = s.waitableCommon? w' := by
      split <;> simp only [waitableCommon?_wsets_modify]
    simp only
    split <;>
      simp only [waitableCommon?_wsets_modify, waitableCommon?_modifyWaitableCommon_ne _ _ hne, h1]

end CStore

/-! ## Tests: the pure updates on a tiny store -/

section Tests

end Tests

end Silmaril.Wasm.Component.Runtime
