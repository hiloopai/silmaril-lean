module

public import Silmaril.Wasm.Component.Reference.ABI.Calling.Defs

/-!
# Canonical ABI async codes and bit packings

This module transcribes every numeric code, sentinel and bit packing of the
Component Model concurrency ABI (the 🔀/🧵 parts of the Canonical ABI). It does
not depend on any runtime or scheduler design: everything here is a plain
enumeration, a constant, or a total function on `Nat`.

Source: `design/mvp/canonical-abi/definitions.py` at component-model revision
`a25fc0b` (line numbers below refer to that file), with prose in
`design/mvp/CanonicalABI.md` and `design/mvp/Explainer.md` at the same revision.

| Lean | `definitions.py` |
| --- | --- |
| `tableMaxLength` | `Table.MAX_LENGTH` (L654), index 0 reserved (`Table.__init__`, L656–658) |
| `bufferMaxLength` | `Buffer.MAX_LENGTH` (L877), trap in `GuestBuffer.__init__` (L895) |
| `EventCode`, `EventTuple` | `EventCode`, `EventTuple` (L713–722) |
| `SubtaskState` | `Subtask.State` (L817–822), `Subtask.resolved` (L838) |
| `TaskState` | `Task.State` (L393–398) |
| `EndState` | `End.State` (L932–936), `End.copying_or_cancelling` (L1018) |
| `CopyResult` | `CopyResult` (L1021–1024) |
| `packStreamCopyResult` | `StreamEnd.notify.stream_event` (L1028–1044) |
| `futureCopyPayload` | `FutureEnd.notify.future_event` (L1050–1066) |
| `EndKind.eventCode` | `new_stream`, `new_future` (L1085–1097) |
| `CallbackCode`, `unpackCallbackResult` | `CallbackCode`, `unpack_callback_result` (L2147–2159) |
| `AsyncLowerResult` | `canon_lower`, async branch (L2217–2233) |
| `contextSlotCount`, `contextValueBound` | `Thread.storage` (L292), `canon_context_*` (L2275–2291) |
| `backpressureInc?`, `backpressureDec?` | `canon_backpressure_{inc,dec}` (L2295–2307) |
| `EventTuple.callbackArgs` | callback call in `canon_lift` (L2131–2132) |
| `EventTuple.Storable` | `unpack_event` (L2349–2354) |
| `noWaitableSet` | `canon_waitable_join` (L2384) |
| `blocked` | `BLOCKED` (L2394) |
| `subtaskCancelResult`, `SubtaskCancelResultWF`, `subtaskCancelResult?` | `canon_subtask_cancel` (L2396–2416) |
| `packEnds`, `unpackEnds` | `canon_{stream,future}_new` (L2430–2444); test helper `unpack_new_ends` |
| `threadSwitchResult` | `canon_thread_{suspend,yield,…}` return `[0]` (L2605–2659) |
| `ABI.maxFlat*` (from `ABI.Calling`) | `MAX_FLAT_{PARAMS,ASYNC_PARAMS,RESULTS}` (L1765–1767) |

`CallbackCode` at `a25fc0b` has exactly `EXIT`, `YIELD` and `WAIT` (with
`MAX = 2`); there is no `POLL` code, and codes `3..15` trap in
`unpack_callback_result`. There is no function named `pack_copy_result` at this
revision; the packing is inlined in `stream_event` (wasmtime's
`ReturnCode::encode` comment still uses that older name).

Python models core values as unbounded integers and relies on assertions for
their ranges. Here packings are total functions on `Nat`; the range facts that
Python asserts are theorems in `Async/Codes/Properties.lean`. `TaskState` and
`EndState` are Python `Enum`s (not `IntEnum`s), so their numeric values are
never observable through the ABI; they are recorded only for transcription
fidelity.

Cross-check with wasmtime (`a7b4f29`,
`crates/wasmtime/src/runtime/component/concurrent.rs`,
`concurrent/futures_and_streams.rs`, `crates/environ/src/component.rs`,
`crates/environ/src/vmoffsets.rs`): event codes (`Event::parts`), callback codes
(`callback_code`, `unpack_callback_code`), subtask states (`Status`, whose
cancelled cases are named `StartCancelled`/`ReturnCancelled`), copy results and
`BLOCKED` (`ReturnCode::encode`), `ItemCount::MAX = 1 << 28` (strict bound,
agreeing with `Buffer.MAX_LENGTH = 2^28 - 1`), `MAX_FLAT_*`,
`NUM_COMPONENT_CONTEXT_SLOTS = 2` and the `u16` backpressure counter all agree.
Differences: wasmtime keeps context slots as `u32` only (Python also allows the
🐘 `i64` form); wasmtime's `PREPARE_ASYNC_*` and `START_FLAG_ASYNC_CALLEE` are
implementation-internal adapter constants with no spec counterpart. A spec-level
inconsistency: `Explainer.md` says the `stream.{read,write}` result is a
`memory.addrtype` whose all-ones value means blocked, but `definitions.py`
returns `BLOCKED = 0xffff_ffff` for both address types; `blocked` follows
`definitions.py`.

Nothing here models tasks, threads, waitables, scheduling or memory; this is
not a conformance claim for any runtime behaviour.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.AsyncRef

/-! ## Shared bounds and sentinels -/

/-- `Table.MAX_LENGTH = 2**28 - 1` (L654). Index `0` is never allocated
because `Table.__init__` starts with `array = [None]`. -/
def tableMaxLength : Nat := 2 ^ 28 - 1

/-- `Buffer.MAX_LENGTH = 2**28 - 1` (L877); a guest buffer longer than this
traps (L895). -/
def bufferMaxLength : Nat := 2 ^ 28 - 1

/-- `BLOCKED = 0xffff_ffff` (L2394): returned by `subtask.cancel`,
`{stream,future}.{read,write}` and `{stream,future}.cancel-{read,write}` when the
operation has not completed. -/
def blocked : Nat := 0xffff_ffff

/-- `canon_waitable_join` (L2384): set index `0` means "remove from any set". -/
def noWaitableSet : Nat := 0

/-- The constant `i32` result of `thread.suspend`, `thread.yield` and the four
`thread.*-then-*` built-ins (`return [0]`, L2609–2659). -/
def threadSwitchResult : Nat := 0

/-! ## Low-nibble packing

`lo | (hi << 4)` is shared by callback results (`unpack_callback_result`),
async-lower results (`canon_lower`) and stream copy results (`stream_event`). -/

/-- `lo | (hi << 4)`. -/
def packLow4 (lo hi : Nat) : Nat := lo ||| (hi <<< 4)

/-- `(packed & 0xf, packed >> 4)`. -/
def unpackLow4 (packed : Nat) : Nat × Nat := (packed &&& 0xf, packed >>> 4)

/-! ## Event codes -/

/-- `EventCode` (L713–720). -/
inductive EventCode where
  | none
  | subtask
  | streamRead
  | streamWrite
  | futureRead
  | futureWrite
  | taskCancelled
  deriving Repr, DecidableEq

def EventCode.toNat : EventCode → Nat
  | .none => 0
  | .subtask => 1
  | .streamRead => 2
  | .streamWrite => 3
  | .futureRead => 4
  | .futureWrite => 5
  | .taskCancelled => 6

def EventCode.ofNat? : Nat → Option EventCode
  | 0 => some .none
  | 1 => some .subtask
  | 2 => some .streamRead
  | 3 => some .streamWrite
  | 4 => some .futureRead
  | 5 => some .futureWrite
  | 6 => some .taskCancelled
  | _ => Option.none

def EventCode.all : List EventCode :=
  [.none, .subtask, .streamRead, .streamWrite, .futureRead, .futureWrite, .taskCancelled]

/-- `EventTuple = tuple[EventCode, int, int]` (L722): the event code, the table
index of the waitable (or `0`), and the payload. -/
structure EventTuple where
  code : EventCode
  index : Nat
  payload : Nat
  deriving Repr, DecidableEq

/-- `(EventCode.NONE, 0, 0)` (`WaitableSet.poll`, L793; the `YIELD` case of
`canon_lift`, L2121). -/
def EventTuple.none : EventTuple := ⟨.none, 0, 0⟩

/-- `(EventCode.TASK_CANCELLED, 0, 0)` (`WaitableSet.wait_from_callback`, L806;
`canon_lift`, L2110/L2119). -/
def EventTuple.taskCancelled : EventTuple := ⟨.taskCancelled, 0, 0⟩

/-- The three `i32` arguments passed to the `callback` function:
`[event_code, p1, p2]` (L2131–2132). -/
def EventTuple.callbackArgs (e : EventTuple) : List Nat := [e.code.toNat, e.index, e.payload]

/-- `unpack_event` (L2349–2354) returns the code and stores `index` and
`payload` as `u32`s at `ptr` and `ptr + 4`; this is the range it needs. -/
def EventTuple.Storable (e : EventTuple) : Prop := e.index < 2 ^ 32 ∧ e.payload < 2 ^ 32

instance (e : EventTuple) : Decidable e.Storable := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Callback codes -/

/-- `CallbackCode` (L2147–2151). -/
inductive CallbackCode where
  | exit
  | yield
  | wait
  deriving Repr, DecidableEq

def CallbackCode.toNat : CallbackCode → Nat
  | .exit => 0
  | .yield => 1
  | .wait => 2

/-- `CallbackCode.MAX = 2` (L2151). -/
def CallbackCode.max : Nat := 2

def CallbackCode.ofNat? : Nat → Option CallbackCode
  | 0 => some .exit
  | 1 => some .yield
  | 2 => some .wait
  | _ => none

def CallbackCode.all : List CallbackCode := [.exit, .yield, .wait]

/-- The `i32` a callback-lifted core function returns: `code | (si << 4)`, as
written by guests (e.g. `CallbackCode.WAIT | (seti << 4)` in `run_tests.py`). -/
def packCallbackResult (code : CallbackCode) (waitableSetIndex : Nat) : Nat :=
  packLow4 code.toNat waitableSetIndex

/-- `unpack_callback_result` (L2153–2159). `none` is the trap
`trap_if(code > CallbackCode.MAX)`. Python additionally asserts
`packed < 2**32`; the second component is returned for every code, although
`canon_lift` only reads it for `WAIT`. -/
def unpackCallbackResult (packed : Nat) : Option (CallbackCode × Nat) :=
  let (code, waitableSetIndex) := unpackLow4 packed
  if code > CallbackCode.max then none
  else (CallbackCode.ofNat? code).map fun c => (c, waitableSetIndex)

/-! ## Subtask and task states -/

/-- `Subtask.State` (L817–822), an `IntEnum` whose values are observable. -/
inductive SubtaskState where
  | starting
  | started
  | returned
  | cancelledBeforeStarted
  | cancelledBeforeReturned
  deriving Repr, DecidableEq

def SubtaskState.toNat : SubtaskState → Nat
  | .starting => 0
  | .started => 1
  | .returned => 2
  | .cancelledBeforeStarted => 3
  | .cancelledBeforeReturned => 4

def SubtaskState.ofNat? : Nat → Option SubtaskState
  | 0 => some .starting
  | 1 => some .started
  | 2 => some .returned
  | 3 => some .cancelledBeforeStarted
  | 4 => some .cancelledBeforeReturned
  | _ => none

def SubtaskState.all : List SubtaskState :=
  [.starting, .started, .returned, .cancelledBeforeStarted, .cancelledBeforeReturned]

/-- `Subtask.resolved` (L838–846). -/
def SubtaskState.resolved : SubtaskState → Bool
  | .starting | .started => false
  | .returned | .cancelledBeforeStarted | .cancelledBeforeReturned => true

/-- `Task.State` (L393–398), a Python `Enum`; the values are not observable. -/
inductive TaskState where
  | initial
  | started
  | pendingCancel
  | cancelDelivered
  | resolved
  deriving Repr, DecidableEq

def TaskState.toNat : TaskState → Nat
  | .initial => 1
  | .started => 2
  | .pendingCancel => 3
  | .cancelDelivered => 4
  | .resolved => 5

/-- The `i32` result of an async `canon lower` (L2217–2233): either the callee
resolved eagerly, giving plain `Subtask.State.RETURNED`, or a subtask handle was
allocated and the result is `state | (subtaski << 4)`. -/
inductive AsyncLowerResult where
  | returned
  | pending (state : SubtaskState) (subtaskIndex : Nat)
  deriving Repr, DecidableEq

def AsyncLowerResult.pack : AsyncLowerResult → Nat
  | .returned => SubtaskState.returned.toNat
  | .pending state i => packLow4 state.toNat i

/-- The facts `canon_lower` asserts or guarantees: a pending subtask is not yet
resolved (the eager branch covers resolved ones) and
`0 < subtaski <= Table.MAX_LENGTH` (L2231). -/
def AsyncLowerResult.WellFormed : AsyncLowerResult → Prop
  | .returned => True
  | .pending state i => state.resolved = false ∧ 0 < i ∧ i ≤ tableMaxLength

instance (r : AsyncLowerResult) : Decidable r.WellFormed := by
  cases r <;> unfold AsyncLowerResult.WellFormed <;> infer_instance

/-- Guest-side decoding of an async-lower result (the `unpack_result` helper of
`run_tests.py`, plus the index/state distinctions `canon_lower` guarantees). -/
def AsyncLowerResult.unpack? (packed : Nat) : Option AsyncLowerResult :=
  let (lo, i) := unpackLow4 packed
  match SubtaskState.ofNat? lo with
  | none => none
  | some state =>
    if i = 0 then
      if state = .returned then some .returned else none
    else if state.resolved = false ∧ i ≤ tableMaxLength then some (.pending state i)
    else none

/-- `canon_subtask_cancel` (L2396–2416): `none` (still unresolved after an
`async` cancel) is returned as `BLOCKED`, otherwise the resolved state. -/
def subtaskCancelResult : Option SubtaskState → Nat
  | none => blocked
  | some state => state.toNat

/-- The results `canon_subtask_cancel` can actually produce: past the `BLOCKED`
early return, `subtask.resolved()` holds and the function returns
`subtask.state`, which is therefore `RETURNED`, `CANCELLED_BEFORE_STARTED` or
`CANCELLED_BEFORE_RETURNED` (never `STARTING`/`STARTED`). -/
def SubtaskCancelResultWF : Option SubtaskState → Prop
  | none => True
  | some state => state.resolved = true

instance (r : Option SubtaskState) : Decidable (SubtaskCancelResultWF r) := by
  cases r <;> unfold SubtaskCancelResultWF <;> infer_instance

/-- Guest-side decoding of a `subtask.cancel` result: `BLOCKED` decodes to
`some none`, a resolved state code (`2..4`) to `some (some state)`; any other
value (including `STARTING`/`STARTED`) is rejected with `none`. -/
def subtaskCancelResult? (n : Nat) : Option (Option SubtaskState) :=
  if n = blocked then some none
  else match SubtaskState.ofNat? n with
    | some state => if state.resolved then some (some state) else none
    | none => none

/-! ## Stream and future ends -/

/-- `End.State` (L932–936), a Python `Enum`; the values are not observable.
At `a25fc0b` there is a single `COPYING` state (no sync/async split). -/
inductive EndState where
  | idle
  | copying
  | cancellingCopy
  | done
  deriving Repr, DecidableEq

def EndState.toNat : EndState → Nat
  | .idle => 1
  | .copying => 2
  | .cancellingCopy => 3
  | .done => 4

/-- `End.copying_or_cancelling` (L1018–1019). -/
def EndState.copyingOrCancelling : EndState → Bool
  | .copying | .cancellingCopy => true
  | .idle | .done => false

/-- The four concrete end classes (L1069–1083). -/
inductive EndKind where
  | readableStream
  | writableStream
  | readableFuture
  | writableFuture
  deriving Repr, DecidableEq

/-- The `event_code` each end is created with by `new_stream`/`new_future`
(L1085–1097). -/
def EndKind.eventCode : EndKind → EventCode
  | .readableStream => .streamRead
  | .writableStream => .streamWrite
  | .readableFuture => .futureRead
  | .writableFuture => .futureWrite

def EndKind.isStream : EndKind → Bool
  | .readableStream | .writableStream => true
  | .readableFuture | .writableFuture => false

/-- `CopyResult` (L1021–1024). -/
inductive CopyResult where
  | completed
  | dropped
  | cancelled
  deriving Repr, DecidableEq

def CopyResult.toNat : CopyResult → Nat
  | .completed => 0
  | .dropped => 1
  | .cancelled => 2

def CopyResult.ofNat? : Nat → Option CopyResult
  | 0 => some .completed
  | 1 => some .dropped
  | 2 => some .cancelled
  | _ => none

def CopyResult.all : List CopyResult := [.completed, .dropped, .cancelled]

/-- `packed_result = result | (progress << 4)` in `stream_event` (L1041–1043),
with `progress <= Buffer.MAX_LENGTH` asserted. -/
def packStreamCopyResult (result : CopyResult) (progress : Nat) : Nat :=
  packLow4 result.toNat progress

/-- Guest-side decoding of a non-`BLOCKED` stream payload. -/
def unpackStreamCopyResult? (packed : Nat) : Option (CopyResult × Nat) :=
  let (lo, progress) := unpackLow4 packed
  (CopyResult.ofNat? lo).map fun r => (r, progress)

/-- `future_event` (L1050–1066) returns the bare `CopyResult` with no progress
field (`future-read-result.cancelled` is encoded as `copy-result.cancelled`,
Explainer.md "future.read and future.write"). -/
def futureCopyPayload (result : CopyResult) : Nat := result.toNat

/-- `canon_{stream,future}_new` (L2430–2444) return one `i64`:
`readable_index | (writable_index << 32)`. -/
def packEnds (readable writable : Nat) : Nat := readable ||| (writable <<< 32)

/-- The `unpack_new_ends` helper of `run_tests.py`. -/
def unpackEnds (packed : Nat) : Nat × Nat := (packed &&& 0xffff_ffff, packed >>> 32)

/-! ## Thread-local context and backpressure -/

/-- `Thread.storage = [0,0]` (L292); validation requires `context.{get,set}`
indices `< 2` (CanonicalABI.md, "canon context.get"). -/
def contextSlotCount : Nat := 2

/-- Initial thread-local storage (L292). -/
def initialContext : List Nat := List.replicate contextSlotCount 0

/-- Values stored by `context.set` at type `t` satisfy `v < 2 ** (ptr_size(t) * 8)`
(L2280/L2289), i.e. `v < 2 ^ t.width`. -/
def contextValueBound (t : IntType) : Nat := 2 ^ t.width

/-- `2**16`, the backpressure counter trap bound (L2297–2299). -/
def backpressureLimit : Nat := 2 ^ 16

/-- `canon_backpressure_inc` (L2295–2300) on the counter; `none` is the trap. -/
def backpressureInc? (n : Nat) : Option Nat :=
  if n + 1 = backpressureLimit then none else some (n + 1)

/-- `canon_backpressure_dec` (L2302–2307) on the counter; `none` is the trap
`backpressure < 0`. -/
def backpressureDec? (n : Nat) : Option Nat :=
  if n = 0 then none else some (n - 1)

end Silmaril.Wasm.Component.AsyncRef
