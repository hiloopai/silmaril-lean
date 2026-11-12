module

public import Silmaril.Wasm.Component.Reference.Runtime.StreamOps.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs

/-!
# Stream and future built-ins

Specification programs in `Canon.P E σ` for the stream/future canon built-ins of REF
`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>;
`CanonicalABI.md` §"`canon {stream,future}.new`" and the following stream/future sections).
They wrap the `End` methods of `Runtime/StreamOps.lean` and the `Waitable` methods of
`Runtime/Waitable.lean`.

| Lean | REF (lines) |
| --- | --- |
| `newBuiltin`, `streamNew`, `futureNew` | `canon_{stream,future}_new` (L2430-2444) |
| `copyBuiltin` | `copy` (L2460-2478) |
| `streamRead`, `streamWrite`, `futureRead`, `futureWrite` | their wrappers (L2448-2458) |
| `cancelCopy` | `cancel_copy` (L2494-2512) |
| `stream/futureCancelRead/Write` | the four wrappers (L2482-2492) |
| `dropEnd` | `drop` (L2528-2537) |
| `stream/futureDropReadable/Writable` | the four wrappers (L2516-2526) |
| `forwardBuiltin` | `forward` (L2547-2561) |
| `streamForward`, `futureForward` | the two wrappers (L2541-2545) |

The `kind : EndKind` argument is the REF class argument `EndT` (`ReadableStreamEnd`, ...);
for `forwardBuiltin` it is the READABLE class `ReadableEndT` and the writable class is
`kind.dual`. The element type `t` is the REF `stream_or_future_t.t`.

## Shape

Each built-in starts with `current_instance()` (`Canon.currentInst`; REF `copy`/`cancel_copy`
use `current_thread().task.inst`, the same instance) and the `may_leave` check
(`endMayLeave`, trap `cannotLeave`). Handle-table accesses are the `Effects.lean` helpers
(`handlesGet`, `handlesRemove`, `handlesAdd`); the class and element-type checks are
`expectEnd` (trap `wrongHandleType`, like `Canon.checkLiftEnd`). Every store mutation is a
NAMED update: `newEndsSt` (REF `new_stream`/`new_future`), `HandleSt.setEndIndex`
(`end.index = ...`), and the updates issued by the reused methods: `Runtime.copySt`
(`End.copy`, inside `endCopy`), `Runtime.cancel` (`End.cancel`, choice C5, inside
`endCancel`), `Runtime.dropEnd` (`End.drop`), `Runtime.forwardSt` (`End.forward`),
`CStore.setSyncWaiterSt`/`CStore.startWaitingSt` (`wait_for_pending_event`) and
`CStore.takeWaitableEventSt` (`get_pending_event`).

**Sync vs async.** For `stream/future.read/write` the choice is the `async` canonopt of the
built-in's own options (`opts.async_`); for the cancels it is the built-in's `async_`
immediate. Waiting is the guest-side `Waitable.waitForPendingEvent` at site K5 (`syncCopy`)
for copies and K6 (`syncCancelCopy`) for cancels; the async form returns `Async.blocked`.

**Results.** `stream.new`/`future.new` return one `i64` holding `Async.packEnds r w`
(`r | w << 32`; readable added first). A copy or cancel returns the pending event's payload,
which is already `Async.packStreamCopyResult r progress` for streams and
`Async.futureCopyPayload r` for futures (computed by `Runtime.deliver`). The flat result type
follows `ResolvedBuiltin.coreType`: `stream.read/write` return a pointer-sized value (`i32`, or
`i64` for a 64-bit memory; `ptrFlat` at the pointer width of the built-in's options, `.i32`
without a memory, D-g); `future.read/write` and all cancels return an `i32`.

## Trap reasons (informative; the specification compares traps only as "some trap")

* `copy`, `trap_if(end.state != IDLE)` (L2466): `streamDone (future) (write)` for a DONE end,
  `concurrentStreamOp` for a COPYING/CANCELLING_COPY end (as `Runtime.copy`).
* `copy`/`cancel_copy`, `trap_if(end.in_waitable_set() and not async_)` and `cancel_copy`,
  `trap_if(end.has_sync_waiter)` (L2501): `subtaskInSet` (the wasmtime message
  "waitable cannot be used synchronously while added to a waitable set", see `Trap.lean`).
* `cancel_copy`, `trap_if(end.state != COPYING)` (L2500): `concurrentStreamOp`. There is no
  dedicated `TrapReason` constructor (wasmtime: "... cancelled when no write/read is
  pending"); the reason is informative only.
* `drop`, `trap_if(end.copying_or_cancelling())` (L2534): `dropBusy (future) (readable)`;
  `trap_if(isinstance(end, WritableFutureEnd) and end.state != DONE)` (L2535):
  `futureNotWritten`.
* `forward`, `trap_if(... .state != IDLE)` (L2553, L2558): `forwardBusy (future)`;
  `trap_if(... .in_waitable_set())` (L2554, L2559): `endInSet`.
* `mkGuestBuffer`: `bufferTooLong`, `unalignedPointer`, `outOfBounds`; `End.copy`:
  `sameInstanceCopy`.

## Deviations and non-claims

* (D-f) REF asserts are preconditions and are not checked: after `get_pending_event`,
  `code == end.event_code and index == i and payload != BLOCKED` (copy) and
  `not end.copying_or_cancelling()` (cancel_copy); `wait_for_pending_event`'s "not in a set,
  no sync waiter" (guaranteed by the preceding traps); `End.drop`'s "no sync waiter"
  (`Waitable.drop`). A missing pending event after a sync wait is `internal` inside
  `Waitable.getPendingEvent` (unreachable: the wait returns only once an event is pending).
* Every program takes `(lim : Limits)` as its leading argument (unused by `new`, `cancel`,
  `drop`); those that reach `End.copy`/`End.forward` also take `(q : Quirks)` (passed through
  to the element transfer of `Runtime/StreamOps.lean`), as in `streamNew lim t`, `dropEnd lim kind t
  i` and `forwardBuiltin lim q kind t ri wi`.
* `End.forward` is the REF method (`Runtime.endForward`), not the run_tests pumped variant;
  likewise `End.copy`/`End.drop` are `endCopy`/`endDrop` (`endCopyPumped` etc. are conveniences of
  the `run_tests.py` ports).
* Proved here: only the `P.Inv` lemmas (each built-in preserves a store invariant `I` as soon
  as the named updates it issues do). No tests here (`Examples/Streams.lean` and the `run_tests.py`
  ports test these programs end to end). -/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Async

variable {E : CoreEngine} {σ : Type}

/-! ## Named store updates -/

/-- The store update of REF `new_stream(t, owner)` / `new_future(t, owner)` (L1085-1097):
allocate a linked `(readable, writable)` pair of class `k` (`Runtime.newEnds`). -/
def newEndsSt (k : EndKind) (t : Option (WIT.ClosedType RtId)) (owner : Option InstId)
    (s : CStore E) : CStore E :=
  (newEnds k t owner s).1

/-! ## Shared checks -/

/-- REF `trap_if(not inst.may_leave)` (trap `cannotLeave`). -/
def endMayLeave (inst : InstId) : P E σ Unit := do
  trapIf (!(← getInst inst).mayLeave) .cannotLeave

/-- The end behind handle-table entry `ent`, with REF `trap_if(not isinstance(end, EndT))` and
`trap_if(end.t != stream_or_future_t.t)` (both `wrongHandleType`). -/
def expectEnd (kind : EndKind) (t : Option (WIT.ClosedType RtId)) (ent : HandleEntry) :
    P E σ (EndId × End E) :=
  match ent with
  | .waitable (.end_ e) => do
    let en ← getObj ArenaField.ends e
    trapIf (en.kind != kind) .wrongHandleType
    trapIf (en.t != t) .wrongHandleType
    return (e, en)
  | _ => trap .wrongHandleType

/-- REF `trap_if(end.state != End.State.IDLE)` of `copy` (L2466): `streamDone` for a DONE end,
`concurrentStreamOp` for a busy one. -/
def checkCopyIdle (kind : EndKind) : EndState → P E σ Unit
  | .idle => pure ()
  | .done => trap (.streamDone (!kind.isStream) (!kind.isReadable))
  | .copying | .cancellingCopy => trap .concurrentStreamOp

/-- The flat result of a copy: pointer-sized for streams (`ResolvedBuiltin.coreType`), `i32`
for futures. -/
def copyResultFlat (kind : EndKind) (cx : LiftLowerContext E) (payload : Nat) :
    P E σ (List FlatValue) :=
  if kind.isStream then do return [ptrFlat (← ptrType cx) payload]
  else pure [i32Flat payload]

/-- The common tail of `copy` (L2470-2478) and `cancel_copy` (L2503-2512): if no event is
pending, wait for it at `site` (sync) or return `BLOCKED` (async); then take the event and
return its payload. `res` builds the flat result. -/
def awaitEndEvent (site : WaitSite) (async_ : Bool) (e : EndId)
    (res : Nat → P E σ (List FlatValue)) : P E σ (List FlatValue) := do
  if ← Waitable.hasPendingEvent (.end_ e) then
    let ev ← Waitable.getPendingEvent (.end_ e)
    res ev.payload
  else if async_ then res blocked
  else do
    Waitable.waitForPendingEvent site (.end_ e)
    let ev ← Waitable.getPendingEvent (.end_ e)
    res ev.payload

/-! ## `stream.new` / `future.new` -/

/-- REF `canon_stream_new`/`canon_future_new` (L2430-2444) for the readable class `k`:
`may_leave`, `new_stream/new_future(t, owner = inst)` (`newEndsSt`), then
`readable_end.index = inst.handles.add(readable_end)` and likewise for the writable end
(readable FIRST); returns the `i64` `packEnds r w`. -/
def newBuiltin (_lim : Limits) (k : EndKind) (t : Option (WIT.ClosedType RtId)) :
    P E σ (List FlatValue) := do
  let inst ← currentInst
  endMayLeave inst
  let s ← getStore
  let ids := (newEnds k t (some inst) s).2
  modifyStore (newEndsSt k t (some inst))
  let ri ← handlesAdd inst (.waitable (.end_ ids.1))
  modifyStore (HandleSt.setEndIndex ids.1 ri)
  let wi ← handlesAdd inst (.waitable (.end_ ids.2))
  modifyStore (HandleSt.setEndIndex ids.2 wi)
  return [.int .i64 (BitVec.ofNat 64 (packEnds ri wi))]

/-- REF `canon_stream_new(stream_t)` (L2430-2436). -/
def streamNew (lim : Limits) (t : Option (WIT.ClosedType RtId)) : P E σ (List FlatValue) :=
  newBuiltin lim .readableStream t

/-- REF `canon_future_new(future_t)` (L2438-2444). -/
def futureNew (lim : Limits) (t : Option (WIT.ClosedType RtId)) : P E σ (List FlatValue) :=
  newBuiltin lim .readableFuture t

/-! ## `stream/future.read/write` -/

/-- REF `copy(EndT, BufferT, stream_or_future_t, opts, i, ptr, length)` (L2460-2478):
1. `may_leave` (`cannotLeave`); `end = handles.get(i)`; class and element type
   (`wrongHandleType`);
2. `trap_if(end.state != IDLE)` (`checkCopyIdle`);
3. `trap_if(end.in_waitable_set() and not opts.async_)` (`subtaskInSet`);
4. `cx = LiftLowerContext(opts, inst, borrow_scope = None)`, `buffer = BufferT(end.t, cx,
   ptr, length)` (`mkGuestBuffer`: eager length/alignment/bounds traps);
5. `end.copy(buffer)` (`endCopy`, `is_read` = the class is readable);
6. no pending event: sync waits (K5), async returns `BLOCKED`; else the event's payload. -/
def copyBuiltin (lim : Limits) (q : Quirks) (kind : EndKind) (t : Option (WIT.ClosedType RtId))
    (opts : CanonOpts E) (i ptr length : Nat) : P E σ (List FlatValue) := do
  let inst ← currentInst
  endMayLeave inst
  let ent ← handlesGet inst i
  let r ← expectEnd kind t ent
  checkCopyIdle kind r.2.state
  trapIf (r.2.common.wset.isSome && !opts.async_) .subtaskInSet
  let buf ← mkGuestBuffer lim { opts, inst, scope := .none } r.2.t ptr length
  endCopy lim q r.1 buf kind.isReadable
  awaitEndEvent .syncCopy opts.async_ r.1 (copyResultFlat kind { opts, inst, scope := .none })

/-- REF `canon_stream_read(stream_t, opts, i, ptr, length)` (L2448-2449). -/
def streamRead (lim : Limits) (q : Quirks) (t : Option (WIT.ClosedType RtId))
    (opts : CanonOpts E) (i ptr length : Nat) : P E σ (List FlatValue) :=
  copyBuiltin lim q .readableStream t opts i ptr length

/-- REF `canon_stream_write(stream_t, opts, i, ptr, length)` (L2451-2452). -/
def streamWrite (lim : Limits) (q : Quirks) (t : Option (WIT.ClosedType RtId))
    (opts : CanonOpts E) (i ptr length : Nat) : P E σ (List FlatValue) :=
  copyBuiltin lim q .writableStream t opts i ptr length

/-- REF `canon_future_read(future_t, opts, i, ptr)` (L2454-2455): length 1. -/
def futureRead (lim : Limits) (q : Quirks) (t : Option (WIT.ClosedType RtId))
    (opts : CanonOpts E) (i ptr : Nat) : P E σ (List FlatValue) :=
  copyBuiltin lim q .readableFuture t opts i ptr 1

/-- REF `canon_future_write(future_t, opts, i, ptr)` (L2457-2458): length 1. -/
def futureWrite (lim : Limits) (q : Quirks) (t : Option (WIT.ClosedType RtId))
    (opts : CanonOpts E) (i ptr : Nat) : P E σ (List FlatValue) :=
  copyBuiltin lim q .writableFuture t opts i ptr 1

/-! ## `{stream,future}.cancel-{read,write}` -/

/-- REF `cancel_copy(EndT, stream_or_future_t, async_, i)` (L2494-2512): `may_leave`;
`handles.get(i)`; class and element type; `trap_if(end.state != COPYING)`
(`concurrentStreamOp`, see the module docstring); `trap_if(end.has_sync_waiter)` and
`trap_if(end.in_waitable_set() and not async_)` (`subtaskInSet`); `end.cancel()`
(`endCancel`, choice C5); then wait (K6) or `BLOCKED`, and the pending event's payload as an
`i32`. -/
def cancelCopy (_lim : Limits) (kind : EndKind) (t : Option (WIT.ClosedType RtId))
    (async_ : Bool) (i : Nat) : P E σ (List FlatValue) := do
  let inst ← currentInst
  endMayLeave inst
  let ent ← handlesGet inst i
  let r ← expectEnd kind t ent
  trapIf (r.2.state != .copying) .concurrentStreamOp
  trapIf r.2.common.hasSyncWaiter .subtaskInSet
  trapIf (r.2.common.wset.isSome && !async_) .subtaskInSet
  endCancel r.1
  awaitEndEvent .syncCancelCopy async_ r.1 fun p => pure [i32Flat p]

/-- REF `canon_stream_cancel_read(stream_t, async_, i)` (L2482-2483). -/
def streamCancelRead (lim : Limits) (t : Option (WIT.ClosedType RtId)) (async_ : Bool)
    (i : Nat) : P E σ (List FlatValue) :=
  cancelCopy lim .readableStream t async_ i

/-- REF `canon_stream_cancel_write(stream_t, async_, i)` (L2485-2486). -/
def streamCancelWrite (lim : Limits) (t : Option (WIT.ClosedType RtId)) (async_ : Bool)
    (i : Nat) : P E σ (List FlatValue) :=
  cancelCopy lim .writableStream t async_ i

/-- REF `canon_future_cancel_read(future_t, async_, i)` (L2488-2489). -/
def futureCancelRead (lim : Limits) (t : Option (WIT.ClosedType RtId)) (async_ : Bool)
    (i : Nat) : P E σ (List FlatValue) :=
  cancelCopy lim .readableFuture t async_ i

/-- REF `canon_future_cancel_write(future_t, async_, i)` (L2491-2492). -/
def futureCancelWrite (lim : Limits) (t : Option (WIT.ClosedType RtId)) (async_ : Bool)
    (i : Nat) : P E σ (List FlatValue) :=
  cancelCopy lim .writableFuture t async_ i

/-! ## `{stream,future}.drop-{readable,writable}` -/

/-- REF `drop(EndT, stream_or_future_t, i)` (L2528-2537): `may_leave`;
`end = inst.handles.remove(i)`; class and element type; `trap_if(end.copying_or_cancelling())`
(`dropBusy`); a writable future end must be DONE (`futureNotWritten`); `end.drop()`
(`endDrop`: unlink and notify the peer, leave the waitable set). Returns `[]`. -/
def dropEnd (_lim : Limits) (kind : EndKind) (t : Option (WIT.ClosedType RtId)) (i : Nat) :
    P E σ (List FlatValue) := do
  let inst ← currentInst
  endMayLeave inst
  let ent ← handlesRemove inst i
  let r ← expectEnd kind t ent
  trapIf (r.2.state == .copying || r.2.state == .cancellingCopy)
    (.dropBusy (!kind.isStream) kind.isReadable)
  trapIf (kind == .writableFuture && r.2.state != .done) .futureNotWritten
  endDrop r.1
  return []

/-- REF `canon_stream_drop_readable(stream_t, i)` (L2516-2517). -/
def streamDropReadable (lim : Limits) (t : Option (WIT.ClosedType RtId)) (i : Nat) :
    P E σ (List FlatValue) :=
  Builtins.dropEnd lim .readableStream t i

/-- REF `canon_stream_drop_writable(stream_t, i)` (L2519-2520). -/
def streamDropWritable (lim : Limits) (t : Option (WIT.ClosedType RtId)) (i : Nat) :
    P E σ (List FlatValue) :=
  Builtins.dropEnd lim .writableStream t i

/-- REF `canon_future_drop_readable(future_t, i)` (L2522-2523). -/
def futureDropReadable (lim : Limits) (t : Option (WIT.ClosedType RtId)) (i : Nat) :
    P E σ (List FlatValue) :=
  Builtins.dropEnd lim .readableFuture t i

/-- REF `canon_future_drop_writable(future_t, i)` (L2525-2526). -/
def futureDropWritable (lim : Limits) (t : Option (WIT.ClosedType RtId)) (i : Nat) :
    P E σ (List FlatValue) :=
  Builtins.dropEnd lim .writableFuture t i

/-! ## `stream.forward` / `future.forward` -/

/-- The checks of `forward` on one removed end (L2549-2554 / L2555-2559): class and element
type (`wrongHandleType`), `state != IDLE` (`forwardBusy`), in a waitable set (`endInSet`). -/
def expectForwardEnd (kind : EndKind) (t : Option (WIT.ClosedType RtId)) (ent : HandleEntry) :
    P E σ EndId := do
  let r ← expectEnd kind t ent
  trapIf (r.2.state != .idle) (.forwardBusy (!kind.isStream))
  trapIf r.2.common.wset.isSome .endInSet
  return r.1

/-- REF `forward(ReadableEndT, WritableEndT, stream_or_future_t, ri, wi)` (L2547-2561):
`may_leave`; remove `ri` and check it (readable class `kind`); remove `wi` and check it
(writable class `kind.dual`); `End.forward(readable_end, writable_end)` (`endForward`, whose
drop branch is the `Runtime.dropEnd`). Returns `[]`. -/
def forwardBuiltin (lim : Limits) (q : Quirks) (kind : EndKind)
    (t : Option (WIT.ClosedType RtId)) (ri wi : Nat) : P E σ (List FlatValue) := do
  let inst ← currentInst
  endMayLeave inst
  let rent ← handlesRemove inst ri
  let r ← expectForwardEnd kind t rent
  let went ← handlesRemove inst wi
  let w ← expectForwardEnd kind.dual t went
  endForward lim q r w
  return []

/-- REF `canon_stream_forward(stream_t, ri, wi)` (L2541-2542). -/
def streamForward (lim : Limits) (q : Quirks) (t : Option (WIT.ClosedType RtId))
    (ri wi : Nat) : P E σ (List FlatValue) :=
  forwardBuiltin lim q .readableStream t ri wi

/-- REF `canon_future_forward(future_t, ri, wi)` (L2544-2545). -/
def futureForward (lim : Limits) (q : Quirks) (t : Option (WIT.ClosedType RtId))
    (ri wi : Nat) : P E σ (List FlatValue) :=
  forwardBuiltin lim q .readableFuture t ri wi

/-! ## Program-logic lemmas

Each built-in preserves a store invariant `I` as soon as the named updates it issues do. -/

namespace Inv

variable {I : CStore E → Prop}

/-- The named updates of `wait_for_pending_event` and `get_pending_event` on an end. -/
structure AwaitPres (I : CStore E → Prop) : Prop where
  syncWaiter : ∀ w o s, I s → I (CStore.setSyncWaiterSt (E := E) w o s)
  startWaiting : ∀ t rc s, I s → I (CStore.startWaitingSt (E := E) t rc s)
  takeEvent : ∀ w s, I s → I (CStore.takeWaitableEventSt (E := E) w s)

end Inv

end Silmaril.Wasm.Component.Canon.Builtins
