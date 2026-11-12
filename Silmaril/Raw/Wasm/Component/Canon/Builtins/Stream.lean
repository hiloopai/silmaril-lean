module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Stream.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Stream.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.StreamOps
public import Silmaril.Raw.Wasm.Component.Runtime.Waitable
public import Silmaril.Raw.Wasm.Component.Canon.Flat

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

/-! ## Shared checks -/

/-! ## `stream.new` / `future.new` -/

/-! ## `stream/future.read/write` -/

/-! ## `{stream,future}.cancel-{read,write}` -/

/-! ## `{stream,future}.drop-{readable,writable}` -/

/-! ## `stream.forward` / `future.forward` -/

/-! ## Program-logic lemmas

Each built-in preserves a store invariant `I` as soon as the named updates it issues do. -/

namespace Inv

variable {I : CStore E → Prop}

end Inv

end Silmaril.Wasm.Component.Canon.Builtins
