module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Waitable.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Waitable
public import Silmaril.Raw.Wasm.Component.Canon.Context
public import Silmaril.Raw.Wasm.Component.Canon.Flat

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
`has_sync_waiter = False`, and `[BLOCKED]` if still unresolved (`AsyncRef.subtaskCancelResult
none = AsyncRef.blocked = 0xFFFF_FFFF`); finally `get_pending_event()` (which consumes the
`SUBTASK` event and runs `deliver_resolve`) and `[subtask.state]`
(`AsyncRef.subtaskCancelResult (some state)`).

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
  _root_.Silmaril.Wasm.Component.AsyncRef _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-! ## Named store update -/

namespace WaitableSt

end WaitableSt

/-! ## Shared entry checks -/

/-! ## Built-ins -/

/-! ## Basic facts -/

/-- The `BLOCKED` result of `subtask.cancel` is `0xFFFF_FFFF`. -/
theorem subtaskCancel_blocked_code : subtaskCancelResult none = 0xFFFF_FFFF := rfl

/-- `requestCancel` sets exactly `cancellation_requested`, `has_sync_waiter` and its ghost owner. -/
theorem subtask?_requestCancel (s : CStore E) (st : SubtaskId) (t : ThreadId) :
    (WaitableSt.requestCancel st t s).subtask? st = (s.subtask? st).map fun x =>
      { x with cancellationRequested := true,
               common := { x.common with hasSyncWaiter := true, syncOwner := some t } } := by
  simp only [WaitableSt.requestCancel, CStore.subtask?, ArenaField.get?_modify_self]

/-! ## Program-logic lemmas

Each built-in preserves a store invariant `I` as soon as the named updates it issues do. -/

namespace Inv

variable {I : CStore E → Prop}

end Inv

end Silmaril.Wasm.Component.Canon.Builtins
