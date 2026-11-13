module

@[expose] public section

/-!
# The async Canonical ABI of `definitions.py`, transcribed (component-model `d095e2f`)

An executable transcription of the concurrency part of the Component Model's Python reference
[`design/mvp/canonical-abi/definitions.py`](https://github.com/WebAssembly/component-model/blob/d095e2f60ddae1f9a1e9b1e2fb547ec1114da677/design/mvp/canonical-abi/definitions.py)
at revision `d095e2f60ddae1f9a1e9b1e2fb547ec1114da677` (2026-10-20). Line numbers `Lnnn` refer
to that file. The vendored copy is `vendor/component-model/d095e2f/canonical-abi/` (with `SHA256SUMS`).

Between `a25fc0b` (the revision of the copied reference machine `Silmaril.Wasm.Component.Reference`
and of `Silmaril.Wasm.Component.Async`) and `d095e2f`, `definitions.py` changed only in pointer
checks: the alignment/bounds traps of string and list stores moved into `reallocate`, the
out-param check moved inside `lower_flat_values`, and `unpack_event` and
`error-context.debug-message` gained alignment/bounds traps. No async state machine changed
(`tools/wasm-tools/README.md`, section *async*).

## What is transcribed

* `Table` (L652–687) with its free list (indices are reused, last freed first);
* `Waitable`, `WaitableSet` (L726–814), with the **pending event as a closure**: a stream or
  future end keeps the `progress` of its last `notify`, a subtask a flag; the event tuple and
  its side effects are computed when the event is delivered (`deliverEnd`, `deliverSub`), as
  in Python;
* `Subtask` (L818–874) and its states; `Task` (L392–505): states, `enter_implicit_thread`
  with backpressure and the exclusive thread, `return_`, `cancel`, `request_cancellation`;
* buffers (L878–929) over an abstract memory of cells, host buffers (`run_tests.py`'s
  `HostReadableBuffer`/`HostWritableBuffer`);
* `End` (L933–1021): `copy`, `cancel`, `forward`, `drop`, the stream and future `notify`;
* `canon lift` (L2056–2125), including the callback loop and `unpack_callback_result`, and
  for sync function types the loop that resumes ready threads of the callee's instance until
  the task resolves (`After.liftLoop` for a guest caller, `Store.topLoop` for the embedder);
  the lowering of arguments into the callee's table (`lower_flat_values`) and the lifting of
  results out of it (`Op.taskReturnL`, `Op.coreReturnL`); `canon lower` (L2149–2213);
* the built-ins `context.{get,set}`, `backpressure.{inc,dec}`, `task.{return,cancel}`,
  `waitable-set.{new,wait,poll,drop}`, `waitable.join`, `subtask.{cancel,drop}`,
  `{stream,future}.{new,read,write,cancel-read,cancel-write,drop-readable,drop-writable,
  forward}`, `thread.{index,new-indirect,resume-later,suspend,yield,suspend-then-resume,
  yield-then-resume,suspend-then-promote,yield-then-promote}`, `error-context.{new,drop}`
  (L2253–2681).

## Abstractions (stated, not hidden)

* **Core code is the environment.** There is no core Wasm: a run is a script of steps
  (`Step`) — built-in calls of the running thread, the returns of core functions and
  callbacks, host actions and scheduler ticks.
* **Control is flat.** Python's nested `resume` calls are a stack of resumers (`Store.stack`):
  when the running thread blocks or exits, control returns to the thread that resumed it,
  which continues with its pending code (`After`). `Store.tick` resumes any ready waiting
  thread (Python picks one at random); `wait_until` always blocks (the `DETERMINISTIC_PROFILE`
  branch); the non-deterministic "return at once" branch is a block followed by an immediate
  tick of the same thread.
* **Values and memory.** Element values are cells of type `α` in a per-instance memory
  `Nat → α`, one cell per element (`elem_size = 1`, no alignment or bounds traps). Flat values
  of calls are `Nat`s; stream and future values are end ids (`AVal`). Async-lowered results
  and multi-value results are recorded in the subtask (`Subtask.stored`) instead of guest
  memory at `retp`; events are returned as their three components instead of being stored at
  `ptr`.
* **Types** are opaque tags `Ty` (equality and whether they are `none` or a number type).
* `may_leave`, borrows and lenders are kept as fields but never change in a script (no
  `realloc`/`post-return` runs; no resources).
* The `canon lift` loop of a sync function type resumes the thread the script chose
  (`Step.loopPicks`), else the first ready thread in the instance's thread table (Python:
  `random.choice`). Host callees follow `run_tests.py`'s
  `mk_host_func`; the host helpers `HostWriter`/`HostReader` (L1382–1488) are pumps
  (`Pump`) hooked to the `copy`/`drop` of an end, as `pump_after_other_end_makes_progress`
  patches those methods (`copyH`, `dropH`).
* Failures: `Fail.trap` is a Python `Trap`; `Fail.assert` is a failed Python `assert` (a bug of
  the script or of the transcription); `Fail.unsupported` marks what is not transcribed.

A Silmaril transcription, not a copy of silmaril's machine (`Silmaril/Raw/Wasm/Component/Runtime`).
-/

namespace Silmaril.Wasm.Component.Async.Cabi

/-! ## Failures and codes -/

/-- How a step fails. -/
inductive Fail where
  /-- A `Trap` of `definitions.py`. -/
  | trap (why : String)
  /-- A failed `assert` of `definitions.py`. -/
  | assert (why : String)
  /-- Outside the transcribed fragment. -/
  | unsupported (why : String)
  deriving Repr, DecidableEq

/-- The monad of the transcription. -/
abbrev M := Except Fail

/-- `trap_if`. -/
def trapIf (c : Bool) (why : String) : M Unit := if c then .error (.trap why) else pure ()

/-- `assert`. -/
def check (c : Bool) (why : String) : M Unit := if c then pure () else .error (.assert why)

/-- A failure is a trap. -/
def Fail.isTrap : Fail → Bool
  | .trap _ => true
  | _ => false

/-- `EventCode` (L715–722). -/
inductive EventCode where
  | none | subtask | streamRead | streamWrite | futureRead | futureWrite | taskCancelled
  deriving DecidableEq, Repr

/-- The numeric event code. -/
def EventCode.toNat : EventCode → Nat
  | .none => 0 | .subtask => 1 | .streamRead => 2 | .streamWrite => 3
  | .futureRead => 4 | .futureWrite => 5 | .taskCancelled => 6

/-- `CopyResult` (L1023–1026). -/
inductive CopyResult where
  | completed | dropped | cancelled
  deriving DecidableEq, Repr

/-- The numeric copy result. -/
def CopyResult.toNat : CopyResult → Nat
  | .completed => 0 | .dropped => 1 | .cancelled => 2

/-- `BLOCKED` (L2376). -/
def BLOCKED : Nat := 0xffff_ffff

/-- `Buffer.MAX_LENGTH` and `Table.MAX_LENGTH`: `2^28 - 1`. -/
def MAX_LENGTH : Nat := 2 ^ 28 - 1

/-- `Subtask.State` (L819–824). -/
inductive SubState where
  | starting | started | returned | cancelledBeforeStarted | cancelledBeforeReturned
  deriving DecidableEq, Repr

/-- The numeric subtask state. -/
def SubState.toNat : SubState → Nat
  | .starting => 0 | .started => 1 | .returned => 2
  | .cancelledBeforeStarted => 3 | .cancelledBeforeReturned => 4

/-- `Subtask.resolved` (L840–848). -/
def SubState.resolved : SubState → Bool
  | .starting | .started => false
  | _ => true

/-- `Task.State` (L393–398). -/
inductive TaskState where
  | initial | started | pendingCancel | cancelDelivered | resolved
  deriving DecidableEq, Repr

/-- `CallbackCode` (L2127–2131). -/
inductive CallbackCode where
  | exit | yield | wait
  deriving DecidableEq, Repr

/-- `unpack_callback_result` (L2133–2139): code in the low 4 bits, waitable set above. -/
def unpackCallback (packed : Nat) : M (CallbackCode × Nat) := do
  let code := packed % 16
  trapIf (code > 2) "callback code > MAX"
  let c : CallbackCode := if code = 0 then .exit else if code = 1 then .yield else .wait
  pure (c, packed / 16)

/-! ## Types and values -/

/-- What `none_or_number_type` (L1138) needs of a type. -/
inductive TyKind where
  | none | number | other
  deriving DecidableEq, Repr

/-- An element type of a stream or future, as an opaque tag. -/
structure Ty where
  id : Nat
  kind : TyKind := .number
  deriving DecidableEq, Repr

/-- `none_or_number_type`. -/
def Ty.noneOrNumber (t : Ty) : Bool := t.kind != .other

/-- The kinds of ends (`ReadableStreamEnd`, …, L1071–1085). -/
inductive EndKind where
  | streamR | streamW | futureR | futureW
  deriving DecidableEq, Repr

/-- A readable end. -/
def EndKind.isReadable : EndKind → Bool
  | .streamR | .futureR => true
  | _ => false

/-- A stream end. -/
def EndKind.isStream : EndKind → Bool
  | .streamR | .streamW => true
  | _ => false

/-- `End.event_code`. -/
def EndKind.eventCode : EndKind → EventCode
  | .streamR => .streamRead | .streamW => .streamWrite
  | .futureR => .futureRead | .futureW => .futureWrite

/-- `End.State` (L934–938). -/
inductive EndState where
  | idle | copying | cancelling | done
  deriving DecidableEq, Repr

/-- A value passed to or from a task: a flat number, or a stream/future end (by end id). -/
inductive AVal where
  | num (n : Nat)
  | end_ (e : Nat)
  deriving DecidableEq, Repr

/-- An argument of `canon lower`: a flat number, or the handle of a readable end to lift
(`lift_stream`/`lift_future`, L1443–1461). -/
inductive LArg where
  | num (n : Nat)
  | readable (stream : Bool) (t : Ty) (i : Nat)
  deriving DecidableEq, Repr

/-! ## State -/

/-- A buffer (L878–929): guest memory of an instance, or a host buffer. -/
structure Buf (α : Type) where
  /-- `some i`: a guest buffer in the memory of instance `i`; `none`: a host buffer. -/
  inst : Option Nat
  /-- `self.t` is not `None`. -/
  typed : Bool := true
  /-- The next cell (guest buffers). -/
  ptr : Nat := 0
  length : Nat
  progress : Nat := 0
  /-- The values of a host readable buffer. -/
  src : List α := []
  deriving Repr

/-- `remain`. -/
def Buf.remain {α : Type} (b : Buf α) : Nat := b.length - b.progress

/-- A stream or future end (L933–957). -/
structure End where
  kind : EndKind
  t : Ty
  state : EndState := .idle
  other : Option Nat := none
  /-- The parked buffer (its id in `Store.bufs`). -/
  buffer : Option Nat := none
  owner : Option Nat := none
  index : Option Nat := none
  /-- The pending event: the `progress` of the last `notify`. -/
  pending : Option Nat := none
  wset : Option Nat := none
  syncWaiter : Bool := false
  deriving Repr, DecidableEq

/-- A subtask (L818–874), with the closures of `canon lower` (L2149–2213) as data. -/
structure Subtask where
  state : SubState := .starting
  /-- A pending `subtask_event` (set by `on_progress`). -/
  pending : Bool := false
  wset : Option Nat := none
  syncWaiter : Bool := false
  cancelRequested : Bool := false
  /-- `lenders is None`. -/
  delivered : Bool := false
  /-- `maybe_on_progress` is `on_progress` (an async lower that did not resolve at once). -/
  onProgress : Bool := false
  /-- The handle of the subtask in the caller's table (`subtaski`). -/
  index : Nat := 0
  /-- The caller's instance. -/
  callerInst : Nat
  /-- `opts.async_` of the lower. -/
  async : Bool
  /-- The arguments, lifted lazily by `on_start`. -/
  args : List LArg
  /-- The callee task (for `on_cancel`). -/
  callee : Nat := 0
  /-- `flat_results`. -/
  flatResults : List Nat := []
  /-- Results stored through `retp` (abstracted). -/
  stored : List Nat := []
  deriving Repr, DecidableEq

/-- A waitable set (L768–814). -/
inductive WRef where
  | end_ (e : Nat)
  | sub (s : Nat)
  deriving DecidableEq, Repr

/-- A waitable set. -/
structure WSet where
  elems : List WRef := []
  numWaiting : Nat := 0
  deriving Repr, DecidableEq

/-- What a handle denotes. -/
inductive Entry where
  | end_ (e : Nat)
  | sub (s : Nat)
  | wset (w : Nat)
  | errctx (msg : Nat)
  deriving DecidableEq, Repr

/-- `Table` (L652–687): `arr[0]` is never used; `free` is a stack (head = last freed). -/
structure Table (ε : Type) where
  arr : List (Option ε) := [none]
  free : List Nat := []
  deriving Repr

/-- Who called a task. -/
inductive Caller where
  /-- The embedder (`Store.invoke`): `on_start` supplies `args`, `on_resolve` records. -/
  | host (args : List AVal)
  /-- A `canon lower` with this subtask. -/
  | sub (s : Nat)
  deriving DecidableEq, Repr

/-- A task (L392–505). -/
structure Task where
  inst : Nat
  /-- `ft.async_`. -/
  ftAsync : Bool := true
  /-- `opts.async_`. -/
  optsAsync : Bool
  /-- `opts.callback` is set. -/
  callback : Bool
  /-- A host task (`mk_host_func`). -/
  isHost : Bool := false
  state : TaskState := .initial
  numBorrows : Nat := 0
  implicitThread : Option Nat := none
  threads : List Nat := []
  caller : Caller
  /-- The result type, as a tag (`task.return` compares it). -/
  resultTy : Nat := 0
  /-- `on_resolve` of a host caller: `some r` once resolved (`none`: cancelled). -/
  hostResult : Option (Option (List AVal)) := none
  deriving Repr, DecidableEq

/-- A component instance (L190–207). -/
structure Inst (α : Type) where
  handles : Table Entry := {}
  threads : Table Nat := {}
  mayLeave : Bool := true
  backpressure : Nat := 0
  numWaitingToEnter : Nat := 0
  exclusive : Option Nat := none
  mem : Nat → α

/-- What a blocked thread finishes when it is resumed (the rest of the Python function). -/
inductive Cont where
  /-- `copy`/`cancel_copy` after `wait_for_pending_event`: deliver the end's event. -/
  | copyDone (e : Nat)
  /-- `waitable-set.wait`. -/
  | wsWait (w : Nat)
  /-- A sync `canon lower` waiting for its subtask. -/
  | lowerSync (s : Nat)
  /-- A sync `subtask.cancel` waiting for its subtask. -/
  | cancelSync (s : Nat)
  /-- `thread.suspend`/`yield` and friends: return `[0]`. -/
  | retZero
  /-- A new thread (`thread.new-indirect`), started with its closure argument. -/
  | start (c : Nat)
  /-- `enter_implicit_thread` waiting for backpressure. -/
  | enter (task : Nat)
  /-- The callback loop after `YIELD`. -/
  | cbYield (task : Nat)
  /-- The callback loop after `WAIT` on the set `w`. -/
  | cbWait (task w : Nat)
  /-- A host thread's `wait_until(end.has_pending_event)`. -/
  | hostPending (e : Nat)
  /-- A host thread's `wait_until(subtask.resolved)`-like wait for a task. -/
  | hostTask (task : Nat)
  /-- `wait_until(flag.is_set)` on a `RacyBool` of `run_tests.py` (core code). -/
  | flag (f : Nat)
  /-- A host thread's `wait_until(lambda: reader.received or reader.dropped)` on the
  `HostReader` pump `p`. -/
  | hostReader (p : Nat)
  deriving DecidableEq, Repr

/-- Thread states (L279–312): `cont` and `ready_func`. -/
inductive TStatus where
  | running
  /-- Blocked without `ready_func`. -/
  | suspended (k : Cont)
  /-- Blocked with `ready_func` (on `Store.waiting`). -/
  | waiting (k : Cont)
  | exited
  deriving DecidableEq, Repr

/-- A thread. -/
structure Thread where
  task : Nat
  status : TStatus
  index : Option Nat := none
  storage : Nat × Nat := (0, 0)
  cancellable : Bool := false
  /-- The values its last completed operation returned (for scripts). -/
  out : List Nat := []
  /-- The values `on_start` gave a host thread (for scripts). -/
  hostArgs : List AVal := []
  deriving DecidableEq, Repr

/-- What a resumer does when control comes back to it. -/
inductive After where
  /-- `canon lower` after `callee(on_start, on_resolve)` returned. -/
  | lower (s : Nat)
  /-- `subtask.cancel` after `on_cancel()` returned. -/
  | cancel (s : Nat) (async : Bool)
  /-- Nothing (a tick, `thread.resume-later` or a host invoke). -/
  | nothing
  /-- The `canon lift` loop of a sync-typed callee `task` (L2119–2124): while the task is not
  resolved, resume a ready thread of its instance (trap if none); then continue with `next`. -/
  | liftLoop (task : Nat) (next : After)
  deriving DecidableEq, Repr

/-- A callee. -/
inductive Callee where
  /-- A lifted guest function of instance `inst`. -/
  | guest (inst : Nat) (ftAsync optsAsync callback : Bool) (resultTy : Nat)
  /-- A host function (`mk_host_func`): a fresh host instance per call. -/
  | host
  deriving DecidableEq, Repr

/-- A `HostWriter` of `run_tests.py` (L1395–1437): host code writing `queue` into the
writable end `e` in chunks of `chunk`, whose `pump` runs after each `copy`/`drop` of the peer
end it was created with. -/
structure PWriter (α : Type) where
  /-- `self.end` (writable). -/
  e : Nat
  /-- `self.readable_end`. -/
  r : Nat
  queue : List α
  chunk : Nat
  dropWhenEmpty : Bool
  pumping : Bool := false

/-- A `HostReader` of `run_tests.py` (L1439–1488) of the readable end `e`. `onData` is the
`on_data` callback of `test_eager_stream_completion` (`add10`): take what was received, write
it mapped by the function to the writer pump, and `end_when_empty` it once dropped. -/
structure PReader (α : Type) where
  e : Nat
  /-- The current `HostWritableBuffer` (its id). -/
  buf : Option Nat := none
  /-- `hostRecv e` had this length when `buf` was created (`buffer.received` is the rest). -/
  mark : Nat := 0
  received : List α := []
  remain : Nat
  dropped : Bool := false
  onData : Option (Nat × (α → α)) := none
  pumping : Bool := false

/-- A pump of `run_tests.py`'s host helpers. -/
inductive Pump (α : Type) where
  | writer (w : PWriter α)
  | reader (r : PReader α)

/-- The whole state. Heaps are functions with allocation counters. -/
structure Store (α : Type) where
  insts : Nat → Option (Inst α) := fun _ => none
  nInsts : Nat := 0
  ends : Nat → Option End := fun _ => none
  nEnds : Nat := 0
  bufs : Nat → Option (Buf α) := fun _ => none
  nBufs : Nat := 0
  subs : Nat → Option Subtask := fun _ => none
  nSubs : Nat := 0
  wsets : Nat → Option WSet := fun _ => none
  nWsets : Nat := 0
  tasks : Nat → Option Task := fun _ => none
  nTasks : Nat := 0
  threads : Nat → Option Thread := fun _ => none
  nThreads : Nat := 0
  /-- `Store.waiting` (L509). -/
  waiting : List Nat := []
  /-- The running thread. -/
  cur : Option Nat := none
  /-- The resumers of `cur`, innermost first. -/
  stack : List (Nat × After) := []
  /-- What host writable buffers of each end received. -/
  hostRecv : Nat → List α := fun _ => []
  /-- Events taken by host code, latest first. -/
  hostEvents : List (EventCode × Nat × Nat) := []
  /-- `DETERMINISTIC_PROFILE`. -/
  det : Bool := true
  /-- The `RacyBool`s of `run_tests.py`. -/
  flags : Nat → Bool := fun _ => false
  /-- The task of a sync-typed callee started by the embedder whose `canon lift` loop
  (L2119–2124) is running (`Store.invoke` has not returned). -/
  topLoop : Option Nat := none
  /-- The host pumps of `run_tests.py` (`HostWriter`, `HostReader`). -/
  pumps : Nat → Option (Pump α) := fun _ => none
  nPumps : Nat := 0
  /-- `pump_after_other_end_makes_progress` (L1382–1393): the pumps run, oldest first, after
  each `copy`/`drop` of an end. -/
  hooks : Nat → List Nat := fun _ => []
  /-- The threads the next turns of a `canon lift` loop resume (the script's choices for
  Python's `random.choice`); when empty, the first ready thread in table order. -/
  picks : List Nat := []

/-! ## Heap helpers -/

/-- Point update. -/
def upd {β : Type} (f : Nat → β) (k : Nat) (v : β) : Nat → β :=
  fun j => if j = k then v else f j

/-- Read an optional heap cell or fail with an assertion. -/
def need {β : Type} (o : Option β) (why : String) : M β :=
  match o with
  | some b => pure b
  | none => .error (.assert why)

namespace Table

variable {ε : Type}

/-- `Table.get` (L667–670). -/
def get (t : Table ε) (i : Nat) : M ε :=
  match t.arr[i]? with
  | some (some e) => pure e
  | _ => .error (.trap "table: bad index")

/-- `Table.add` (L672–681). -/
def add (t : Table ε) (e : ε) : M (Table ε × Nat) :=
  match t.free with
  | i :: fs => pure ({ arr := t.arr.set i (some e), free := fs }, i)
  | [] =>
    let i := t.arr.length
    if i > MAX_LENGTH then .error (.trap "table full")
    else pure ({ t with arr := t.arr ++ [some e] }, i)

/-- `Table.remove` (L683–687). -/
def remove (t : Table ε) (i : Nat) : M (Table ε × ε) := do
  let e ← t.get i
  pure ({ arr := t.arr.set i none, free := i :: t.free }, e)

end Table

namespace Store

variable {α : Type}

def getInst (st : Store α) (i : Nat) : M (Inst α) := need (st.insts i) "no instance"
def setInst (st : Store α) (i : Nat) (x : Inst α) : Store α := { st with insts := upd st.insts i (some x) }
def getEnd (st : Store α) (e : Nat) : M End := need (st.ends e) "no end"
def setEnd (st : Store α) (e : Nat) (x : End) : Store α := { st with ends := upd st.ends e (some x) }
def getBuf (st : Store α) (b : Nat) : M (Buf α) := need (st.bufs b) "no buffer"
def setBuf (st : Store α) (b : Nat) (x : Buf α) : Store α := { st with bufs := upd st.bufs b (some x) }
def getSub (st : Store α) (s : Nat) : M Subtask := need (st.subs s) "no subtask"
def setSub (st : Store α) (s : Nat) (x : Subtask) : Store α := { st with subs := upd st.subs s (some x) }
def getWs (st : Store α) (w : Nat) : M WSet := need (st.wsets w) "no waitable set"
def setWs (st : Store α) (w : Nat) (x : WSet) : Store α := { st with wsets := upd st.wsets w (some x) }
def getTask (st : Store α) (t : Nat) : M Task := need (st.tasks t) "no task"
def setTask (st : Store α) (t : Nat) (x : Task) : Store α := { st with tasks := upd st.tasks t (some x) }
def getThread (st : Store α) (t : Nat) : M Thread := need (st.threads t) "no thread"
def setThread (st : Store α) (t : Nat) (x : Thread) : Store α :=
  { st with threads := upd st.threads t (some x) }

/-- Allocate an end. -/
def newEnd (st : Store α) (x : End) : Store α × Nat :=
  ({ st with ends := upd st.ends st.nEnds (some x), nEnds := st.nEnds + 1 }, st.nEnds)

/-- Allocate a buffer. -/
def newBuf (st : Store α) (x : Buf α) : Store α × Nat :=
  ({ st with bufs := upd st.bufs st.nBufs (some x), nBufs := st.nBufs + 1 }, st.nBufs)

/-- Add an entry to the handle table of an instance. -/
def addHandle (st : Store α) (i : Nat) (e : Entry) : M (Store α × Nat) := do
  let x ← st.getInst i
  let (h, n) ← x.handles.add e
  pure (st.setInst i { x with handles := h }, n)

/-- Remove an entry from the handle table of an instance. -/
def removeHandle (st : Store α) (i : Nat) (n : Nat) : M (Store α × Entry) := do
  let x ← st.getInst i
  let (h, e) ← x.handles.remove n
  pure (st.setInst i { x with handles := h }, e)

/-- Look up a handle. -/
def handle (st : Store α) (i n : Nat) : M Entry := do
  (← st.getInst i).handles.get n

/-- Record the output of a thread. -/
def setOut (st : Store α) (th : Nat) (vs : List Nat) : M (Store α) := do
  let t ← st.getThread th
  pure (st.setThread th { t with out := vs })

end Store

/-! ## Waitables (L726–814) -/

namespace Store

variable {α : Type}

/-- `has_pending_event`. -/
def hasPending (st : Store α) : WRef → Bool
  | .end_ e => match st.ends e with | some x => x.pending.isSome | none => false
  | .sub s => match st.subs s with | some x => x.pending | none => false

/-- The set a waitable joined. -/
def wsetOf (st : Store α) : WRef → Option Nat
  | .end_ e => (st.ends e).bind (·.wset)
  | .sub s => (st.subs s).bind (·.wset)

/-- `has_sync_waiter`. -/
def syncWaiterOf (st : Store α) : WRef → Bool
  | .end_ e => match st.ends e with | some x => x.syncWaiter | none => false
  | .sub s => match st.subs s with | some x => x.syncWaiter | none => false

/-- Set the `wset` field. -/
def setWsetField (st : Store α) (w : WRef) (o : Option Nat) : M (Store α) :=
  match w with
  | .end_ e => do let x ← st.getEnd e; pure (st.setEnd e { x with wset := o })
  | .sub s => do let x ← st.getSub s; pure (st.setSub s { x with wset := o })

/-- Leave the set a waitable joined (`self.wset.elems.remove(self)`). -/
def leaveSet (st : Store α) (w : WRef) : M (Store α) :=
  match st.wsetOf w with
  | some old => do
    let ws ← st.getWs old
    pure (st.setWs old { ws with elems := ws.elems.erase w })
  | none => pure st

/-- Enter a set (`wset.elems.append(self)`). -/
def enterSet (st : Store α) (w : WRef) : Option Nat → M (Store α)
  | some n => do
    let ws ← st.getWs n
    pure (st.setWs n { ws with elems := ws.elems ++ [w] })
  | none => pure st

/-- `Waitable.join` (L756–762): leave the old set, join the new one (appended). -/
def join (st : Store α) (w : WRef) (o : Option Nat) : M (Store α) := do
  check (!st.syncWaiterOf w) "join: sync waiter"
  let st ← st.leaveSet w
  let st ← st.setWsetField w o
  st.enterSet w o

/-- `WaitableSet.has_pending_event` (L776). -/
def wsHasPending (st : Store α) (w : Nat) : Bool :=
  match st.wsets w with
  | some ws => ws.elems.any st.hasPending
  | none => false

/-- `StreamEnd.notify`/`FutureEnd.notify` (L1029–1069): record the pending event. -/
def notify (st : Store α) (e progress : Nat) : M (Store α) := do
  let x ← st.getEnd e
  check (x.kind.isStream || progress ≤ 1) "future progress ≤ 1"
  pure (st.setEnd e { x with pending := some progress })

/-- Deliver the pending event of an end: the `stream_event`/`future_event` closures
(L1030–1048, L1051–1069). -/
def deliverEnd (st : Store α) (e : Nat) : M (Store α × (EventCode × Nat × Nat)) := do
  let x ← st.getEnd e
  let p ← need x.pending "deliver: no pending event"
  let x := { x with pending := none }
  let idx := x.index.getD 0
  if x.kind.isStream then
    let x := { x with buffer := none }
    if x.other.isNone then
      check (x.state != .done) "stream_event: done"
      pure (st.setEnd e { x with state := .done },
        (x.kind.eventCode, idx, CopyResult.dropped.toNat + 16 * p))
    else if x.state = .cancelling then
      pure (st.setEnd e { x with state := .idle },
        (x.kind.eventCode, idx, CopyResult.cancelled.toNat + 16 * p))
    else do
      check (x.state = .copying) "stream_event: copying"
      pure (st.setEnd e { x with state := .idle },
        (x.kind.eventCode, idx, CopyResult.completed.toNat + 16 * p))
  else
    if p = 1 then do
      check (x.state = .copying || x.state = .cancelling) "future_event: copying"
      check x.buffer.isNone "future_event: buffer"
      pure (st.setEnd e { x with state := .done }, (x.kind.eventCode, idx, CopyResult.completed.toNat))
    else if x.other.isNone then do
      check (x.state != .done) "future_event: done"
      pure (st.setEnd e { x with buffer := none, state := .done },
        (x.kind.eventCode, idx, CopyResult.dropped.toNat))
    else do
      check (x.state = .cancelling) "future_event: cancelling"
      pure (st.setEnd e { x with buffer := none, state := .idle },
        (x.kind.eventCode, idx, CopyResult.cancelled.toNat))

/-- `Subtask.deliver_resolve` (L862–866). -/
def deliverResolve (st : Store α) (s : Nat) : M (Store α) := do
  let x ← st.getSub s
  check (!x.delivered && x.state.resolved) "deliver_resolve"
  pure (st.setSub s { x with delivered := true })

/-- Deliver the pending event of a subtask: the `subtask_event` closure (L2203–2207). -/
def deliverSub (st : Store α) (s : Nat) : M (Store α × (EventCode × Nat × Nat)) := do
  let x ← st.getSub s
  check x.pending "deliver: no pending event"
  let st := st.setSub s { x with pending := false }
  let st ← if x.state.resolved then st.deliverResolve s else pure st
  pure (st, (.subtask, x.index, x.state.toNat))

/-- `Waitable.get_pending_event`. -/
def deliver (st : Store α) : WRef → M (Store α × (EventCode × Nat × Nat))
  | .end_ e => st.deliverEnd e
  | .sub s => st.deliverSub s

/-- `WaitableSet.get_pending_event` (L779–785). Python shuffles the members; this takes the
first member (in join order) with a pending event. `wsGetEventR` allows any. -/
def wsGetEvent (st : Store α) (w : Nat) : M (Store α × (EventCode × Nat × Nat)) := do
  let ws ← st.getWs w
  match ws.elems.find? st.hasPending with
  | some r => st.deliver r
  | none => .error (.assert "get_pending_event: none")

end Store

/-- **`WaitableSet.get_pending_event`, relationally**: any member with a pending event. -/
def wsGetEventR {α : Type} (st : Store α) (w : Nat) (r : WRef)
    (res : Store α × (EventCode × Nat × Nat)) : Prop :=
  ∃ ws, st.wsets w = some ws ∧ r ∈ ws.elems ∧ st.hasPending r = true ∧ st.deliver r = .ok res

/-! ## Buffers (L878–929) -/

namespace Store

variable {α : Type} [Inhabited α]

/-- `read(n)` of a readable buffer. -/
def bufRead (st : Store α) (b : Nat) (n : Nat) : M (Store α × List α) := do
  let x ← st.getBuf b
  check (n ≤ x.remain) "read: n ≤ remain"
  match x.inst with
  | some i => do
    let ins ← st.getInst i
    let vs := if x.typed then (List.range n).map fun k => ins.mem (x.ptr + k)
      else List.replicate n default
    let x' := { x with ptr := if x.typed then x.ptr + n else x.ptr, progress := x.progress + n }
    pure (st.setBuf b x', vs)
  | none =>
    pure (st.setBuf b { x with progress := x.progress + n }, (x.src.drop x.progress).take n)

/-- `write(vs)` of a writable buffer, for the end `e` it belongs to (host buffers record in
`hostRecv e`). -/
def bufWrite (st : Store α) (e b : Nat) (vs : List α) : M (Store α) := do
  let x ← st.getBuf b
  check (vs.length ≤ x.remain) "write: len ≤ remain"
  match x.inst with
  | some i => do
    let ins ← st.getInst i
    let mem := if x.typed then
        (fun a => if x.ptr ≤ a ∧ a < x.ptr + vs.length then vs.getD (a - x.ptr) default else ins.mem a)
      else ins.mem
    let st := st.setInst i { ins with mem := mem }
    pure (st.setBuf b { x with ptr := if x.typed then x.ptr + vs.length else x.ptr,
                               progress := x.progress + vs.length })
  | none =>
    pure ({ (st.setBuf b { x with progress := x.progress + vs.length }) with
      hostRecv := upd st.hostRecv e (st.hostRecv e ++ vs) })

end Store

/-! ## Ends (L933–1100) -/

namespace Store

variable {α : Type} [Inhabited α]

/-- The element move of `End.copy` case 3 (L966–969): `n` elements from the writer's buffer
to the reader's (`isRead`: `e` reads from `ob`; otherwise `e` writes from `b` into `ob`). -/
def moveElems (st : Store α) (isRead : Bool) (e b o ob n : Nat) : M (Store α) :=
  if isRead then do
    let (st, vs) ← st.bufRead ob n
    st.bufWrite e b vs
  else do
    let (st, vs) ← st.bufRead b n
    st.bufWrite o ob vs

/-- The end of `End.copy` case 3 (L970–973): notify both ends with their buffers' progress and
unpark the peer's buffer if it is full. -/
def notifyBoth (st : Store α) (e b o ob : Nat) : M (Store α) := do
  let buf ← st.getBuf b
  let obuf ← st.getBuf ob
  let st ← st.notify e buf.progress
  let st ← st.notify o obuf.progress
  if obuf.remain = 0 then do
    let y ← st.getEnd o
    pure (st.setEnd o { y with buffer := none })
  else pure st

/-- **`End.copy`** (L958–981): `e` copies with the buffer `b` (already allocated). -/
def copyEnd (st : Store α) (e b : Nat) : M (Store α) := do
  let x ← st.getEnd e
  check x.buffer.isNone "copy: buffer is None"
  let isRead := x.kind.isReadable
  let x := { x with state := .copying }
  let st := st.setEnd e x
  match x.other with
  | none => do check x.pending.isSome "copy: other gone, event pending"; pure st
  | some o => do
    let y ← st.getEnd o
    match y.buffer with
    | none => pure (st.setEnd e { x with buffer := some b })
    | some ob => do
      let buf ← st.getBuf b
      let obuf ← st.getBuf ob
      if buf.remain > 0 && obuf.remain > 0 then do
        trapIf (x.owner.isSome && x.owner == y.owner && !x.t.noneOrNumber) "copy to self"
        let st ← st.moveElems isRead e b o ob (min buf.remain obuf.remain)
        st.notifyBoth e b o ob
      else if buf.remain > 0 || (isRead && obuf.remain = 0) then do
        let st ← st.notify o 0
        let y ← st.getEnd o
        let st := st.setEnd o { y with buffer := none }
        let x ← st.getEnd e
        pure (st.setEnd e { x with buffer := some b })
      else st.notify e 0

/-- **`End.cancel`** (L983–990). `coin` is Python's `random.randint(0,1)`. -/
def cancelEnd (st : Store α) (e : Nat) (coin : Bool) : M (Store α) := do
  let x ← st.getEnd e
  check (x.state = .copying) "cancel: copying"
  let st := st.setEnd e { x with state := .cancelling }
  if x.pending.isNone then do
    let o ← need x.other "cancel: other (AttributeError)"
    let y ← st.getEnd o
    if y.owner.isSome || st.det || coin then st.notify e 0 else pure st
  else pure st

/-- `notify(progress = 0)` of the peer `o` when it is not `DONE` and has no pending event. -/
def notifyIfIdle (st : Store α) (o : Nat) (y : End) : M (Store α) :=
  if y.state != .done && y.pending.isNone then st.notify o 0 else pure st

/-- The peer part of `End.drop`: unlink `e` (whose record is `x`) and its peer. -/
def unlinkPeer (st : Store α) (e : Nat) (x : End) : M (Store α) :=
  match x.other with
  | some o => do
    let y ← st.getEnd o
    check (y.other == some e) "drop: self is other.other"
    let st ← (st.setEnd o { y with other := none }).notifyIfIdle o y
    pure (st.setEnd e { x with other := none })
  | none => pure st

/-- **`End.drop`** (L1010–1018). -/
def dropEnd (st : Store α) (e : Nat) : M (Store α) := do
  let x ← st.getEnd e
  check (x.state != .copying && x.state != .cancelling) "drop: not copying"
  let st ← st.unlinkPeer e x
  check (!st.syncWaiterOf (.end_ e)) "drop: sync waiter"
  st.join (.end_ e) none

/-- `new_stream`/`new_future` (L1087–1100): two linked ends; returns `(reader, writer)`. -/
def newPair (st : Store α) (stream : Bool) (t : Ty) (owner : Option Nat) : Store α × Nat × Nat :=
  let r := st.nEnds
  let w := st.nEnds + 1
  let rk : EndKind := if stream then .streamR else .futureR
  let wk : EndKind := if stream then .streamW else .futureW
  let (st, _) := st.newEnd { kind := rk, t := t, other := some w, owner := owner }
  let (st, _) := st.newEnd { kind := wk, t := t, other := some r, owner := owner }
  (st, r, w)

end Store

/-! ## The host pumps of `run_tests.py` (L1382–1488)

`pump_after_other_end_makes_progress` replaces the `copy` and `drop` methods of one end by
versions that call a pump afterwards; `copyH`/`dropH` are `End.copy`/`End.drop` followed by
the pumps hooked to the end, oldest first. The mutual recursion (a pump copies, which runs
other pumps) is bounded by fuel; running out is `Fail.assert`. -/

/-- The fuel of a pump run. -/
def pumpFuel : Nat := 64

namespace Store

variable {α : Type} [Inhabited α]

/-- Set a pump. -/
def setPump (st : Store α) (p : Nat) (x : Pump α) : Store α :=
  { st with pumps := upd st.pumps p (some x) }

/-- The writer pump `p`. -/
def getWriter (st : Store α) (p : Nat) : M (PWriter α) :=
  match st.pumps p with
  | some (.writer w) => pure w
  | _ => .error (.assert "no writer pump")

/-- The reader pump `p`. -/
def getReader (st : Store α) (p : Nat) : M (PReader α) :=
  match st.pumps p with
  | some (.reader r) => pure r
  | _ => .error (.assert "no reader pump")

mutual

/-- `end.copy(buffer)` with the pumps hooked to `e`. -/
def copyH (fuel : Nat) (st : Store α) (e b : Nat) : M (Store α) :=
  match fuel with
  | 0 => .error (.assert "pump fuel")
  | n + 1 => do
    let st ← st.copyEnd e b
    runHooks n st (st.hooks e)
termination_by structural fuel

/-- `end.drop()` with the pumps hooked to `e`. -/
def dropH (fuel : Nat) (st : Store α) (e : Nat) : M (Store α) :=
  match fuel with
  | 0 => .error (.assert "pump fuel")
  | n + 1 => do
    let st ← st.dropEnd e
    runHooks n st (st.hooks e)
termination_by structural fuel

/-- Run the pumps `ps` in order. -/
def runHooks (fuel : Nat) (st : Store α) (ps : List Nat) : M (Store α) :=
  match fuel, ps with
  | _, [] => pure st
  | 0, _ :: _ => .error (.assert "pump fuel")
  | n + 1, p :: ps => do
    let st ← runPump n st p
    runHooks n st ps
termination_by structural fuel

/-- `pump()` of `HostWriter` (L1424–1437) or `HostReader` (L1468–1488): a no-op while the
pump is already running (`pumping`). -/
def runPump (fuel : Nat) (st : Store α) (p : Nat) : M (Store α) :=
  match fuel with
  | 0 => .error (.assert "pump fuel")
  | n + 1 => match st.pumps p with
    | some (.writer w) =>
      if w.pumping then pure st else do
        let st ← writerLoop n (st.setPump p (.writer { w with pumping := true })) p
        let w ← st.getWriter p
        pure (st.setPump p (.writer { w with pumping := false }))
    | some (.reader r) =>
      if r.pumping then pure st else do
        let st ← readerLoop n (st.setPump p (.reader { r with pumping := true })) p
        let r ← st.getReader p
        pure (st.setPump p (.reader { r with pumping := false }))
    | none => .error (.assert "no pump")
termination_by structural fuel

/-- The loop of `HostWriter.pump`. -/
def writerLoop (fuel : Nat) (st : Store α) (p : Nat) : M (Store α) :=
  match fuel with
  | 0 => .error (.assert "pump fuel")
  | n + 1 => do
    let w ← st.getWriter p
    let x ← st.getEnd w.e
    if x.other.isNone then pure st
    else if x.pending.isSome then do
      let (st, (_, _, packed)) ← st.deliverEnd w.e
      check (packed != BLOCKED) "unpack_result"
      let w ← st.getWriter p
      writerLoop n (st.setPump p (.writer { w with queue := w.queue.drop (packed / 16) })) p
    else if x.state != .idle then pure st
    else if !w.queue.isEmpty then do
      let vs := w.queue.take w.chunk
      let (st, b) := st.newBuf { inst := none, length := vs.length, src := vs }
      let st ← copyH n st w.e b
      writerLoop n st p
    else if w.dropWhenEmpty then do
      let st ← dropH n st w.e
      writerLoop n st p
    else pure st
termination_by structural fuel

/-- The loop of `HostReader.pump`, with the `add10` `on_data` callback. -/
def readerLoop (fuel : Nat) (st : Store α) (p : Nat) : M (Store α) :=
  match fuel with
  | 0 => .error (.assert "pump fuel")
  | n + 1 => do
    let r ← st.getReader p
    if r.dropped then pure st else do
    let x ← st.getEnd r.e
    if (x.state = .copying || x.state = .cancelling) && x.pending.isSome then do
      let (st, (_, _, packed)) ← st.deliverEnd r.e
      check (packed != BLOCKED) "unpack_result"
      let got := (st.hostRecv r.e).drop r.mark
      check (packed / 16 = got.length) "HostReader: progress = len(received)"
      let r := { r with received := r.received ++ got, remain := r.remain - packed / 16,
                        dropped := packed % 16 = CopyResult.dropped.toNat, buf := none }
      let st := st.setPump p (.reader r)
      let st ← match r.onData with
        | none => pure st
        | some (wp, f) => do
          -- `add10`: `vs = reader.take()`; `writer.write(map f vs)`; `end_when_empty`
          let st := st.setPump p (.reader { r with received := [] })
          let st ← if r.received.isEmpty then pure st else do
            let w ← st.getWriter wp
            let st := st.setPump wp (.writer { w with queue := w.queue ++ r.received.map f })
            runPump n st wp
          if r.dropped then do
            let w ← st.getWriter wp
            runPump n (st.setPump wp (.writer { w with dropWhenEmpty := true })) wp
          else pure st
      readerLoop n st p
    else if x.state = .idle && r.remain > 0 then do
      let (st, b) := st.newBuf { inst := none, length := r.remain }
      let st := st.setPump p (.reader { r with buf := some b, mark := (st.hostRecv r.e).length })
      let st ← copyH n st r.e b
      readerLoop n st p
    else pure st
termination_by structural fuel

end

/-- `HostWriter(t, vs, chunk, drop_when_empty)` (L1403–1410): a new stream owned by the host,
the pump hooked to the peer of its writable end, and a first `pump()`. -/
def newWriter (st : Store α) (t : Ty) (vs : List α) (chunk : Nat) (dropWhenEmpty : Bool) :
    M (Store α) := do
  let (st, r, w) := st.newPair true t none
  let p := st.nPumps
  let st := { st with nPumps := p + 1, hooks := upd st.hooks r (st.hooks r ++ [p]) }
  let pw : PWriter α := { e := w, r := r, queue := vs, chunk := chunk, dropWhenEmpty }
  let st := st.setPump p (.writer pw)
  runPump pumpFuel st p

/-- `HostReader(end, remain, on_data)` (L1448–1457): the pump hooked to the end's peer (if
any), and a first `pump()`. -/
def newReader (st : Store α) (e remain : Nat) (onData : Option (Nat × (α → α))) :
    M (Store α) := do
  let x ← st.getEnd e
  let p := st.nPumps
  let st := { st with nPumps := p + 1 }
  let st := match x.other with
    | some o => { st with hooks := upd st.hooks o (st.hooks o ++ [p]) }
    | none => st
  let st := st.setPump p (.reader { e := e, remain := remain, onData := onData })
  runPump pumpFuel st p

end Store

namespace Store

variable {α : Type} [Inhabited α]

/-- **`End.forward`** (L992–1008): `src` is the readable end, `dst` the writable end. Its `drop`s and
`copy` run the pumps hooked to those ends. -/
def forwardEnd (st : Store α) (src dst : Nat) : M (Store α) := do
  let n := pumpFuel
  let x ← st.getEnd src
  let y ← st.getEnd dst
  if x.other == some dst || x.other.isNone || y.other.isNone then do
    let st ← dropH n st src
    dropH n st dst
  else do
    let w ← need x.other "forward"
    let r ← need y.other "forward"
    let we ← st.getEnd w
    let st := st.setEnd w { we with other := some r }
    let re ← st.getEnd r
    let st := st.setEnd r { re with other := some w }
    let we ← st.getEnd w
    let re ← st.getEnd r
    match we.buffer, re.buffer with
    | some wb, some rb => do
      let wbuf ← st.getBuf wb
      let rbuf ← st.getBuf rb
      let smaller := if rbuf.remain > wbuf.remain then w else r
      let sb := if rbuf.remain > wbuf.remain then wb else rb
      let se ← st.getEnd smaller
      let st := st.setEnd smaller { se with buffer := none }
      copyH n st smaller sb
    | _, _ => pure st

end Store

/-! ## Threads and control (L279–383) -/

namespace Store

variable {α : Type}

/-- `Thread.ready` for a blocked thread's continuation. -/
def readyK (st : Store α) : Cont → Bool
  | .copyDone e => st.hasPending (.end_ e)
  | .wsWait w => st.wsHasPending w
  | .lowerSync s | .cancelSync s => match st.subs s with | some x => x.state.resolved | none => false
  | .retZero | .start _ => true
  | .enter t => match st.tasks t with
    | some task => match st.insts task.inst with
      | some ins => !(ins.backpressure > 0 ||
          ((!task.optsAsync || task.callback) && ins.exclusive.isSome))
      | none => false
    | none => false
  | .cbYield t => match st.tasks t with
    | some task => match st.insts task.inst with
      | some ins => ins.exclusive.isNone
      | none => false
    | none => false
  | .cbWait t w => match st.tasks t with
    | some task => match st.insts task.inst with
      | some ins => ins.exclusive.isNone && (st.wsHasPending w || task.state = .pendingCancel)
      | none => false
    | none => false
  | .hostPending e => st.hasPending (.end_ e)
  | .hostTask t => match st.tasks t with
    | some task => task.state = .resolved
    | none => false
  | .flag f => st.flags f
  | .hostReader p => match st.pumps p with
    | some (.reader r) => !r.received.isEmpty || r.dropped
    | _ => false

/-- `Thread.ready`. -/
def ready (st : Store α) (th : Nat) : Bool :=
  match st.threads th with
  | some t => match t.status with
    | .waiting k => st.readyK k
    | _ => false
  | none => false

/-- `start_waiting` + `block`: the running thread waits with continuation `k`. -/
def blockWaiting (st : Store α) (th : Nat) (k : Cont) : M (Store α) := do
  let t ← st.getThread th
  pure { (st.setThread th { t with status := .waiting k }) with waiting := st.waiting ++ [th] }

/-- `block` without `ready_func`. -/
def blockSuspended (st : Store α) (th : Nat) (k : Cont) : M (Store α) := do
  let t ← st.getThread th
  pure (st.setThread th { t with status := .suspended k })

/-- `stop_waiting`. -/
def stopWaiting (st : Store α) (th : Nat) : Store α :=
  { st with waiting := st.waiting.erase th }

end Store

/-! ## Tasks (L392–505) -/

namespace Store

variable {α : Type} [Inhabited α]

/-- `Task.register_thread` (L445–449). -/
def registerThread (st : Store α) (task th : Nat) : M (Store α) := do
  let x ← st.getTask task
  check (!x.threads.contains th) "register: new"
  let st := st.setTask task { x with threads := x.threads ++ [th] }
  let ins ← st.getInst x.inst
  let (tt, i) ← ins.threads.add th
  let st := st.setInst x.inst { ins with threads := tt }
  let t ← st.getThread th
  pure (st.setThread th { t with index := some i })

/-- `Task.unregister_thread` (L458–465). -/
def unregisterThread (st : Store α) (task th : Nat) : M (Store α) := do
  let x ← st.getTask task
  check (x.threads.contains th) "unregister: present"
  let x := { x with threads := x.threads.erase th }
  let st := st.setTask task x
  if x.threads.isEmpty then
    trapIf (x.state != .resolved) "thread exit before task resolved"
  let t ← st.getThread th
  let i ← need t.index "unregister: index"
  let ins ← st.getInst x.inst
  let (tt, _) ← ins.threads.remove i
  pure (st.setInst x.inst { ins with threads := tt })

/-- `on_start` of the caller (`canon lower`, L2172–2176, or the embedder): returns the
arguments. Lifting a stream or future argument removes it from the caller's table
(`lift_async_value`, L1449–1461). -/
def onStart (st : Store α) (c : Caller) : M (Store α × List AVal) :=
  match c with
  | .host args => pure (st, args)
  | .sub s => do
    let x ← st.getSub s
    let st := if x.onProgress then st.setSub s { x with pending := true } else st
    let x ← st.getSub s
    check (x.state = .starting) "on_start: STARTING"
    let st := st.setSub s { x with state := .started }
    x.args.foldlM (init := (st, [])) fun (st, acc) a =>
      match a with
      | .num n => pure (st, acc ++ [.num n])
      | .readable stream t i => do
        let (st, ent) ← st.removeHandle x.callerInst i
        match ent with
        | .end_ e => do
          let y ← st.getEnd e
          trapIf (y.kind != (if stream then .streamR else .futureR)) "lift: not a readable end"
          trapIf (y.t != t) "lift: type"
          trapIf (y.state != .idle) "lift: not idle"
          trapIf y.wset.isSome "lift: in a waitable set"
          pure (st.setEnd e { y with owner := none, index := none }, acc ++ [.end_ e])
        | _ => .error (.trap "lift: not a readable end")

/-- `lift_flat_values` of values given as handles of instance `i` (`lift_async_value`,
L1449–1461, for readable ends, which are removed from the table; numbers pass through). -/
def liftArgs (st : Store α) (i : Nat) (args : List LArg) : M (Store α × List AVal) :=
  args.foldlM (init := (st, [])) fun (st, acc) a =>
    match a with
    | .num n => pure (st, acc ++ [.num n])
    | .readable stream t h => do
      let (st, ent) ← st.removeHandle i h
      match ent with
      | .end_ e => do
        let y ← st.getEnd e
        trapIf (y.kind != (if stream then .streamR else .futureR)) "lift: not a readable end"
        trapIf (y.t != t) "lift: type"
        trapIf (y.state != .idle) "lift: not idle"
        trapIf y.wset.isSome "lift: in a waitable set"
        pure (st.setEnd e { y with owner := none, index := none }, acc ++ [.end_ e])
      | _ => .error (.trap "lift: not a readable end")

/-- `lower_async_value` (L1734–1742) of a result into instance `i`; numbers pass through. -/
def lowerVal (st : Store α) (i : Nat) : AVal → M (Store α × Nat)
  | .num n => pure (st, n)
  | .end_ e => do
    let y ← st.getEnd e
    check (y.kind.isReadable && y.state = .idle) "lower: readable idle end"
    let (st, n) ← st.addHandle i (.end_ e)
    let y ← st.getEnd e
    pure (st.setEnd e { y with owner := some i, index := some n }, n)

/-- `on_resolve` of the caller (`canon lower`, L2178–2189, or the embedder). -/
def onResolve (st : Store α) (c : Caller) (task : Nat) (r : Option (List AVal)) :
    M (Store α) :=
  match c with
  | .host _ => do
    let x ← st.getTask task
    pure (st.setTask task { x with hostResult := some r })
  | .sub s => do
    let x ← st.getSub s
    let st := if x.onProgress then st.setSub s { x with pending := true } else st
    let x ← st.getSub s
    match r with
    | none => do
      check x.cancelRequested "on_resolve(None): cancellation requested"
      let ns : SubState := if x.state = .starting then .cancelledBeforeStarted
        else .cancelledBeforeReturned
      check (x.state = .starting || x.state = .started) "on_resolve(None): state"
      check (!x.state.resolved) "resolve: not resolved"
      pure (st.setSub s { x with state := ns, flatResults := [] })
    | some vs => do
      check (x.state = .started) "on_resolve: STARTED"
      let (st, ns) ← vs.foldlM (init := (st, [])) fun (st, acc) v => do
        let (st, n) ← st.lowerVal x.callerInst v
        pure (st, acc ++ [n])
      let x ← st.getSub s
      let (flat, stored) := if x.async || ns.length > 1 then ([], ns) else (ns, [])
      pure (st.setSub s { x with state := .returned, flatResults := flat, stored := stored })

/-- `Task.return_` (L493–498). -/
def taskReturn (st : Store α) (task : Nat) (r : List AVal) : M (Store α) := do
  let x ← st.getTask task
  trapIf (x.state = .resolved) "task.return: resolved"
  trapIf (x.numBorrows > 0) "task.return: borrows"
  let st ← st.onResolve x.caller task (some r)
  let x ← st.getTask task
  pure (st.setTask task { x with state := .resolved })

/-- `Task.cancel` (L500–505). -/
def taskCancel (st : Store α) (task : Nat) : M (Store α) := do
  let x ← st.getTask task
  trapIf (x.state != .cancelDelivered) "task.cancel: not delivered"
  trapIf (x.numBorrows > 0) "task.cancel: borrows"
  let st ← st.onResolve x.caller task none
  let x ← st.getTask task
  pure (st.setTask task { x with state := .resolved })

/-- `Task.deliver_pending_cancel` (L481–486). -/
def deliverPendingCancel (st : Store α) (task : Nat) : M (Store α × Bool) := do
  let x ← st.getTask task
  if x.state = .pendingCancel then pure (st.setTask task { x with state := .cancelDelivered }, true)
  else pure (st, false)

/-- `Task.needs_exclusive` (L421–423). -/
def Task.needsExclusive (x : Task) : Bool := !x.optsAsync || x.callback

/-- The end of `enter_implicit_thread` (L436–443) once the thread may enter: set the
exclusive thread, register, then `task.start()` (`on_start`), whose arguments become the
thread's output. -/
def enterRest (st : Store α) (task th : Nat) : M (Store α) := do
  let x ← st.getTask task
  let st ← if x.ftAsync && Task.needsExclusive x then do
      let ins ← st.getInst x.inst
      check ins.exclusive.isNone "enter: exclusive is None"
      pure (st.setInst x.inst { ins with exclusive := some th })
    else pure st
  let st ← st.registerThread task th
  let x ← st.getTask task
  check (x.state = .initial) "start: INITIAL"
  let st := st.setTask task { x with state := .started }
  let (st, args) ← st.onStart x.caller
  -- `lower_flat_values` (L2064) into the callee's instance: ends get handles there
  let (st, flat) ← args.foldlM (init := (st, [])) fun (st, acc) v => do
    let (st, n) ← st.lowerVal x.inst v
    pure (st, acc ++ [n])
  let t ← st.getThread th
  pure (st.setThread th { t with hostArgs := args, out := flat })

/-- `exit_implicit_thread` (L451–456). -/
def exitImplicit (st : Store α) (task th : Nat) : M (Store α) := do
  let st ← st.unregisterThread task th
  let x ← st.getTask task
  let st ← if x.ftAsync && Task.needsExclusive x then do
      let ins ← st.getInst x.inst
      check (ins.exclusive == some th) "exit: exclusive"
      pure (st.setInst x.inst { ins with exclusive := none })
    else pure st
  let t ← st.getThread th
  pure (st.setThread th { t with status := .exited })

end Store

/-! ## Finishing a blocked operation -/

namespace Store

variable {α : Type} [Inhabited α]

/-- The end of a callback-loop iteration (L2111–2113): retake the exclusive thread. -/
def cbReenter (st : Store α) (task th : Nat) : M (Store α) := do
  let x ← st.getTask task
  let ins ← st.getInst x.inst
  check ins.exclusive.isNone "callback: exclusive is None"
  let t ← st.getThread th
  let st := st.setThread th { t with cancellable := false }
  pure (st.setInst x.inst { ins with exclusive := some th })

/-- Run the rest of a blocked operation of thread `th` (its status is set to running by the
caller). Returns the operation's results, or `none` when the thread exited instead (a
cancelled `enter`). -/
def finish (st : Store α) (th : Nat) : Cont → M (Store α × Option (List Nat))
  | .copyDone e => do
    let x ← st.getEnd e
    let st := st.setEnd e { x with syncWaiter := false }
    let (st, (_, _, payload)) ← st.deliverEnd e
    pure (st, some [payload])
  | .wsWait w => do
    let ws ← st.getWs w
    let st := st.setWs w { ws with numWaiting := ws.numWaiting - 1 }
    let (st, (c, p1, p2)) ← st.wsGetEvent w
    pure (st, some [c.toNat, p1, p2])
  | .lowerSync s => do
    let st ← st.deliverResolve s
    let x ← st.getSub s
    pure (st, some x.flatResults)
  | .cancelSync s => do
    let x ← st.getSub s
    let st := st.setSub s { x with syncWaiter := false }
    let (st, (_, _, p)) ← st.deliverSub s
    pure (st, some [p])
  | .retZero => pure (st, some [0])
  | .start c => pure (st, some [c])
  | .enter task => do
    let x ← st.getTask task
    let ins ← st.getInst x.inst
    let st := st.setInst x.inst { ins with numWaitingToEnter := ins.numWaitingToEnter - 1 }
    let (st, cancelled) ← st.deliverPendingCancel task
    if cancelled then do
      let st ← st.taskCancel task
      let t ← st.getThread th
      pure (st.setThread th { t with status := .exited }, none)
    else do
      let st ← st.enterRest task th
      let t ← st.getThread th
      pure (st, some t.out)
  | .cbYield task => do
    let (st, c) ← st.deliverPendingCancel task
    let st ← st.cbReenter task th
    pure (st, some [if c then EventCode.taskCancelled.toNat else 0, 0, 0])
  | .cbWait task w => do
    let ws ← st.getWs w
    let st := st.setWs w { ws with numWaiting := ws.numWaiting - 1 }
    let (st, c) ← st.deliverPendingCancel task
    if c then do
      let st ← st.cbReenter task th
      pure (st, some [EventCode.taskCancelled.toNat, 0, 0])
    else do
      let (st, (code, p1, p2)) ← st.wsGetEvent w
      let st ← st.cbReenter task th
      pure (st, some [code.toNat, p1, p2])
  | .hostPending _ => pure (st, some [])
  | .hostTask _ => pure (st, some [])
  | .flag _ => pure (st, some [])
  | .hostReader _ => pure (st, some [])

/-- `canon lower` after the callee returned (L2193–2213). `true`: the resumer `c` blocked
again. -/
def afterLower (st : Store α) (c s : Nat) : M (Store α × Bool) := do
  let x ← st.getSub s
  if !x.async then
    if !x.state.resolved then do
      let st ← st.blockWaiting c (.lowerSync s)
      pure (st, true)
    else do
      let st ← st.deliverResolve s
      let x ← st.getSub s
      pure (← st.setOut c x.flatResults, false)
  else if x.state.resolved then do
    let st ← st.deliverResolve s
    let x ← st.getSub s
    check x.flatResults.isEmpty "async lower: no flat results"
    pure (← st.setOut c [SubState.returned.toNat], false)
  else do
    let (st, i) ← st.addHandle x.callerInst (.sub s)
    let x ← st.getSub s
    let st := st.setSub s { x with index := i, onProgress := true }
    pure (← st.setOut c [x.state.toNat + 16 * i], false)

/-- `subtask.cancel` after `on_cancel()` returned (L2389–2398). `true`: `c` blocked again. -/
def afterCancel (st : Store α) (c s : Nat) (async : Bool) : M (Store α × Bool) := do
  let x ← st.getSub s
  if !async && !x.state.resolved then do
    let st ← st.blockWaiting c (.cancelSync s)
    pure (st, true)
  else do
    let st := st.setSub s { x with syncWaiter := false }
    if !x.state.resolved then pure (← st.setOut c [BLOCKED], false)
    else do
      let (st, (_, _, p)) ← st.deliverSub s
      pure (← st.setOut c [p], false)

/-- Resume the blocked thread `th` as the running thread, the current thread (if any)
becoming its resumer with `after`, and finish its blocked operation (one level of
`Thread.resume`, L329–338). -/
def resumeCore (st : Store α) (th : Nat) (after : After) : M (Store α × Option (List Nat)) := do
  let t ← st.getThread th
  let k ← match t.status with
    | .waiting k => pure k
    | .suspended k => pure k
    | _ => .error (.assert "resume: blocked")
  let st := st.stopWaiting th
  let st := st.setThread th { t with status := .running }
  let st := match st.cur with
    | some c => { st with stack := (c, after) :: st.stack }
    | none => st
  let st := { st with cur := some th }
  st.finish th k

/-- A ready thread of instance `i` for the `canon lift` loop of a sync-typed callee
(`random.choice` of the ready threads in `inst.threads`, L2121–2124): the next of the
script's `picks` (which must be one of them), else the first in table order; a trap when
there is none. -/
def pickReady (st : Store α) (i : Nat) : M (Store α × Nat) := do
  let ins ← st.getInst i
  let cands := (ins.threads.arr.filterMap id).filter st.ready
  match cands, st.picks with
  | [], _ => .error (.trap "canon lift: no ready thread")
  | th :: _, [] => pure (st, th)
  | _, p :: ps => do
    check (cands.contains p) "canon lift: the picked thread is ready"
    pure ({ st with picks := ps }, p)

/-- One turn of the `canon lift` loop: resume a ready thread of instance `i` with the
resumer's continuation `after`. A thread of the instance's table never exits on its resume
(only a thread waiting to enter does, and it is not yet in the table). -/
def loopResume (st : Store α) (i : Nat) (after : After) : M (Store α) := do
  let (st, th) ← st.pickReady i
  let (st, r) ← st.resumeCore th after
  match r with
  | some vs => st.setOut th vs
  | none => .error (.assert "canon lift: a resumed thread exited")

/-- The resumer `c` continues with `a`. -/
def afterResume (st : Store α) (c : Nat) : After → M (Store α × Bool)
  | .nothing => pure (st, false)
  | .lower s => st.afterLower c s
  | .cancel s async => st.afterCancel c s async
  | .liftLoop task a => do
    let x ← st.getTask task
    if x.state = .resolved then st.afterResume c a
    else do
      let st ← st.loopResume x.inst (.liftLoop task a)
      pure (st, false)

/-- Control returns to the resumers in `stk` (innermost first), while they block again. With
no resumer left, the `canon lift` loop of a sync-typed callee invoked by the embedder
(`topLoop`) continues. -/
def popControl (st : Store α) : List (Nat × After) → M (Store α)
  | [] => do
    let st := { st with cur := none, stack := [] }
    match st.topLoop with
    | none => pure st
    | some task => do
      let x ← st.getTask task
      if x.state = .resolved then pure { st with topLoop := none }
      else st.loopResume x.inst .nothing
  | (c, a) :: rest => do
    let (st, blocked) ← afterResume { st with cur := some c, stack := rest } c a
    if blocked then popControl st rest else pure st

/-- The running thread has blocked or exited: control returns to its resumer. -/
def returnControl (st : Store α) : M (Store α) := st.popControl st.stack

/-- Resume the blocked thread `th` (`Thread.resume`, L329–338, one level): it becomes the
running thread and finishes its operation. The current thread, if any, becomes its resumer
with `after`. -/
def resumeThread (st : Store α) (th : Nat) (after : After) : M (Store α) := do
  let (st, r) ← st.resumeCore th after
  match r with
  | some vs => st.setOut th vs
  | none => st.returnControl

end Store

/-! ## The built-ins and core returns of the running thread -/

/-- Operations of the running thread: built-ins, calls, and the returns of core code. -/
inductive Op (α : Type) where
  | contextGet (i : Nat)
  | contextSet (i v : Nat)
  | backpressureInc
  | backpressureDec
  /-- `task.return` with the result type tag and values. -/
  | taskReturn (resultTy : Nat) (vs : List AVal)
  | taskCancel
  | wsNew
  | wsWait (si : Nat)
  | wsPoll (si : Nat)
  | wsDrop (si : Nat)
  | join (wi si : Nat)
  | subtaskCancel (async : Bool) (i : Nat)
  | subtaskDrop (i : Nat)
  | streamNew (t : Ty)
  | futureNew (t : Ty)
  /-- `stream.read`/`stream.write`/`future.read`/`future.write` (`kind` is the end kind the
  handle must have). -/
  | copy (kind : EndKind) (t : Ty) (async : Bool) (i ptr len : Nat)
  /-- `{stream,future}.cancel-{read,write}`; `coin` is `random.randint(0,1)`. -/
  | cancelCopy (kind : EndKind) (t : Ty) (async : Bool) (i : Nat) (coin : Bool)
  | dropEnd (kind : EndKind) (t : Ty) (i : Nat)
  | forward (stream : Bool) (t : Ty) (ri wi : Nat)
  | threadIndex
  /-- `thread.new-indirect` with the closure argument `c` (the function is abstract). -/
  | threadNewIndirect (c : Nat)
  | threadResumeLater (i : Nat)
  | threadSuspend
  | threadYield
  | threadSuspendThenResume (i : Nat)
  | threadYieldThenResume (i : Nat)
  | threadSuspendThenPromote (i : Nat)
  | threadYieldThenPromote (i : Nat)
  | errNew (msg : Nat)
  | errDrop (i : Nat)
  /-- `canon lower` of the callee `f` with `opts.async_ = async`. -/
  | lower (f : Callee) (async : Bool) (args : List LArg)
  /-- A guest store to memory (core code). -/
  | memSet (ptr : Nat) (vs : List α)
  /-- A lifted function with sync options returned these results (L2068–2077). -/
  | coreReturn (vs : List Nat)
  /-- The same, with results that are handles of readable ends to lift (`lift_flat_values`). -/
  | coreReturnL (vs : List LArg)
  /-- `task.return` with results that are handles of readable ends to lift. -/
  | taskReturnL (resultTy : Nat) (vs : List LArg)
  /-- An async (stackful) lifted function returned (L2079–2083). -/
  | coreExit
  /-- An async callback lifted function, or its callback, returned `packed` (L2085–2114). -/
  | cbReturn (packed : Nat)
  /-- A thread of `thread.new-indirect` returned. -/
  | threadExit
  -- host actions of a host thread (`mk_host_func`, `run_tests.py`)
  /-- `on_start()` of a host task. -/
  | hostStart
  /-- `on_resolve(vs)` of a host task. -/
  | hostResolve (vs : List AVal)
  /-- `wait_until(e.has_pending_event)`. -/
  | hostWaitPending (e : Nat)
  /-- The host function returned. -/
  | hostExit
  /-- Core code: `wait_until(flag.is_set)` on a `RacyBool`. -/
  | waitFlag (f : Nat)
  /-- Core code: `flag.set()`. -/
  | setFlag (f : Nat)
  /-- Host code: `wait_until(lambda: reader.received or reader.dropped)` on the reader pump
  `p`. -/
  | hostWaitReader (p : Nat)

/-- Steps of a script. -/
inductive Step (α : Type) where
  /-- The running thread performs an operation. -/
  | op (o : Op α)
  /-- `Store.tick` resumes the ready waiting thread `th`. -/
  | tick (th : Nat)
  /-- `Store.invoke` from the embedder of the guest callee `f` with arguments. -/
  | invoke (f : Callee) (args : List AVal)
  /-- Host code: `new_stream`/`new_future(t, owner = None)`. -/
  | hostNew (stream : Bool) (t : Ty)
  /-- Host code: `e.copy(HostReadableBuffer(vs))`. -/
  | hostWrite (e : Nat) (vs : List α)
  /-- Host code: `e.copy(HostWritableBuffer(n))`. -/
  | hostRead (e n : Nat)
  /-- Host code: `e.get_pending_event()`. -/
  | hostTake (e : Nat)
  /-- Host code: `e.drop()`. -/
  | hostDrop (e : Nat)
  /-- Host code: `e.cancel()`. -/
  | hostCancel (e : Nat) (coin : Bool)
  /-- Host code: `inst.backpressure = v` (`test_callback_interleaving`). -/
  | setBackpressure (i v : Nat)
  /-- The choices of the next turns of a `canon lift` loop (`Store.picks`). -/
  | loopPicks (ths : List Nat)
  /-- Host code: `HostWriter(t, vs, chunk, drop_when_empty)`; the pump is `nPumps`, its
  ends `(nEnds, nEnds + 1)`. -/
  | writerNew (t : Ty) (vs : List α) (chunk : Nat) (dropWhenEmpty : Bool)
  /-- Host code: `HostReader(e, remain, on_data)`; the pump is `nPumps`. -/
  | readerNew (e remain : Nat) (onData : Option (Nat × (α → α)))
  /-- Host code: `writer.write(vs)`. -/
  | writerWrite (p : Nat) (vs : List α)
  /-- Host code: `writer.end_when_empty()`. -/
  | writerEndWhenEmpty (p : Nat)
  /-- Host code: `reader.set_remain(n)`. -/
  | readerSetRemain (p n : Nat)
  /-- Host code: `vs = reader.take()`, then `writer.write(map f vs)` if `vs` is not empty
  (the loop body of `test_async_stream_ops`'s `host_func`). -/
  | readerTakeTo (p wp : Nat) (f : α → α)

namespace Store

variable {α : Type} [Inhabited α]

/-- The running thread, its task and instance. -/
def ctx (st : Store α) : M (Nat × Thread × Task × Inst α) := do
  let th ← need st.cur "no running thread"
  let t ← st.getThread th
  let x ← st.getTask t.task
  let ins ← st.getInst x.inst
  pure (th, t, x, ins)

/-- The running thread blocks or exits: return control to its resumer. -/
def yieldControl (st : Store α) : M (Store α) := st.returnControl

/-- Block the running thread `th` with `wait_until` and continuation `k`. -/
def waitUntil (st : Store α) (th : Nat) (k : Cont) : M (Store α) := do
  let st ← st.blockWaiting th k
  st.yieldControl

/-- Start a callee: a task and its implicit thread, resumed now (`canon_lift`, L2116–2118, or
`mk_host_func`). The current thread (if any) becomes the resumer with `after`. -/
def startCallee (st : Store α) (f : Callee) (caller : Caller) (after : After) :
    M (Store α × Nat) := do
  let (st, task, inst, isHost, ftAsync, optsAsync, cb, rty) ← match f with
    | .guest i ftA oA cb rty => pure (st, st.nTasks, i, false, ftA, oA, cb, rty)
    | .host =>
      let i := st.nInsts
      pure ({ st with insts := upd st.insts i (some { mem := fun _ => default }),
                      nInsts := i + 1 }, st.nTasks, i, true, false, false, false, 0)
  let th := st.nThreads
  let st := { st with tasks := upd st.tasks task (some
      { inst := inst, ftAsync := ftAsync, optsAsync := optsAsync, callback := cb, isHost := isHost,
        caller := caller, resultTy := rty, implicitThread := some th }), nTasks := task + 1 }
  let st := { st with threads := upd st.threads th (some { task := task, status := .running }),
                      nThreads := th + 1 }
  -- a sync-typed guest callee: its caller runs the `canon lift` loop (L2119–2124) once the
  -- callee's thread blocks or exits
  let loop := !isHost && !ftAsync
  let st := match st.cur with
    | some c => { st with stack := (c, if loop then .liftLoop task after else after) :: st.stack }
    | none => if loop then { st with topLoop := some task } else st
  let st := { st with cur := some th }
  if isHost then pure (st, task)
  else do
    -- `enter_implicit_thread` (L425–443); a sync-typed callee enters at once
    let x ← st.getTask task
    let ins ← st.getInst inst
    let hasBp := ins.backpressure > 0 || (Task.needsExclusive x && ins.exclusive.isSome)
    if ftAsync && (hasBp || ins.numWaitingToEnter > 0) then do
      let st := st.setInst inst { ins with numWaitingToEnter := ins.numWaitingToEnter + 1 }
      let st ← st.waitUntil th (.enter task)
      pure (st, task)
    else do
      let st ← st.enterRest task th
      pure (st, task)

/-- `copy` (L2442–2460). -/
def opCopy (st : Store α) (kind : EndKind) (t : Ty) (async : Bool) (i ptr len : Nat) :
    M (Store α) := do
  let (th, _, x, ins) ← st.ctx
  trapIf (!ins.mayLeave) "may_leave"
  let ent ← ins.handles.get i
  let e ← match ent with
    | .end_ e => pure e
    | _ => .error (.trap "copy: not an end")
  let y ← st.getEnd e
  trapIf (y.kind != kind) "copy: wrong end type"
  trapIf (y.t != t) "copy: element type"
  trapIf (y.state != .idle) "copy: not idle"
  trapIf (y.wset.isSome && !async) "copy: sync in a waitable set"
  trapIf (len > MAX_LENGTH) "buffer too long"
  let (st, b) := st.newBuf { inst := some x.inst, typed := t.kind != .none, ptr := ptr, length := len }
  let st ← copyH pumpFuel st e b
  if !(st.hasPending (.end_ e)) then
    if !async then do
      let y ← st.getEnd e
      check (y.wset.isNone && !y.syncWaiter) "wait_for_pending_event"
      let st := st.setEnd e { y with syncWaiter := true }
      st.waitUntil th (.copyDone e)
    else st.setOut th [BLOCKED]
  else do
    let (st, (_, _, p)) ← st.deliverEnd e
    st.setOut th [p]

/-- `cancel_copy` (L2476–2494). -/
def opCancel (st : Store α) (kind : EndKind) (t : Ty) (async : Bool) (i : Nat) (coin : Bool) :
    M (Store α) := do
  let (th, _, _, ins) ← st.ctx
  trapIf (!ins.mayLeave) "may_leave"
  let e ← match ← ins.handles.get i with
    | .end_ e => pure e
    | _ => .error (.trap "cancel: not an end")
  let y ← st.getEnd e
  trapIf (y.kind != kind) "cancel: wrong end type"
  trapIf (y.t != t) "cancel: element type"
  trapIf (y.state != .copying) "cancel: not copying"
  trapIf y.syncWaiter "cancel: sync waiter"
  trapIf (y.wset.isSome && !async) "cancel: sync in a waitable set"
  let st ← st.cancelEnd e coin
  if !(st.hasPending (.end_ e)) then
    if !async then do
      let y ← st.getEnd e
      check (y.wset.isNone && !y.syncWaiter) "wait_for_pending_event"
      let st := st.setEnd e { y with syncWaiter := true }
      st.waitUntil th (.copyDone e)
    else st.setOut th [BLOCKED]
  else do
    let (st, (_, _, p)) ← st.deliverEnd e
    st.setOut th [p]

/-- The thread `i` of the running thread's instance. -/
def threadAt (ins : Inst α) (i : Nat) : M Nat := ins.threads.get i

/-- The suspended thread `o` is switched to (`block(switch_to = o)`): it runs in place of the
current thread, with the same resumers. -/
def switchTo (st : Store α) (o : Nat) : M (Store α) := do
  let t ← st.getThread o
  let k ← match t.status with
    | .suspended k => pure k
    | .waiting k => pure k
    | _ => .error (.assert "switch: blocked")
  let st := (st.stopWaiting o).setThread o { t with status := .running }
  let st := { st with cur := some o }
  let (st, r) ← st.finish o k
  match r with
  | some vs => st.setOut o vs
  | none => st.yieldControl

/-- Is the thread suspended (blocked without `ready_func`)? -/
def isSuspended (st : Store α) (th : Nat) : Bool :=
  match st.threads th with
  | some { status := .suspended _, .. } => true
  | _ => false

/-- **One operation of the running thread.** -/
def runOp (st : Store α) : Op α → M (Store α)
  | .contextGet i => do
    let (th, t, _, _) ← st.ctx
    check (i < 2) "context index"
    st.setOut th [if i = 0 then t.storage.1 else t.storage.2]
  | .contextSet i v => do
    let (th, t, _, _) ← st.ctx
    check (i < 2) "context index"
    let st := st.setThread th { t with storage := if i = 0 then (v, t.storage.2) else (t.storage.1, v) }
    st.setOut th []
  | .backpressureInc => do
    let (th, _, x, ins) ← st.ctx
    trapIf (ins.backpressure + 1 = 2 ^ 16) "backpressure overflow"
    let st := st.setInst x.inst { ins with backpressure := ins.backpressure + 1 }
    st.setOut th []
  | .backpressureDec => do
    let (th, _, x, ins) ← st.ctx
    trapIf (ins.backpressure = 0) "backpressure underflow"
    let st := st.setInst x.inst { ins with backpressure := ins.backpressure - 1 }
    st.setOut th []
  | .taskReturn rty vs => do
    let (th, t, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    trapIf (!x.optsAsync) "task.return: sync options"
    trapIf (rty != x.resultTy) "task.return: result type"
    let st ← st.taskReturn t.task vs
    st.setOut th []
  | .taskCancel => do
    let (th, t, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    trapIf (!x.optsAsync) "task.cancel: sync options"
    let st ← st.taskCancel t.task
    st.setOut th []
  | .wsNew => do
    let (th, _, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let w := st.nWsets
    let st := { st with wsets := upd st.wsets w (some {}), nWsets := w + 1 }
    let (st, i) ← st.addHandle x.inst (.wset w)
    st.setOut th [i]
  | .wsWait si => do
    let (th, _, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let w ← match ← ins.handles.get si with
      | .wset w => pure w
      | _ => .error (.trap "wait: not a waitable set")
    let ws ← st.getWs w
    let st := st.setWs w { ws with numWaiting := ws.numWaiting + 1 }
    st.waitUntil th (.wsWait w)
  | .wsPoll si => do
    let (th, _, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let w ← match ← ins.handles.get si with
      | .wset w => pure w
      | _ => .error (.trap "poll: not a waitable set")
    if !st.wsHasPending w then st.setOut th [0, 0, 0]
    else do
      let (st, (c, p1, p2)) ← st.wsGetEvent w
      st.setOut th [c.toNat, p1, p2]
  | .wsDrop si => do
    let (th, _, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let (st, ent) ← st.removeHandle x.inst si
    let w ← match ent with
      | .wset w => pure w
      | _ => .error (.trap "drop: not a waitable set")
    let ws ← st.getWs w
    trapIf (!ws.elems.isEmpty) "waitable-set.drop: members"
    trapIf (ws.numWaiting > 0) "waitable-set.drop: waiters"
    st.setOut th []
  | .join wi si => do
    let (th, _, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let w ← match ← ins.handles.get wi with
      | .end_ e => pure (WRef.end_ e)
      | .sub s => pure (WRef.sub s)
      | _ => .error (.trap "join: not a waitable")
    trapIf (st.syncWaiterOf w) "join: sync waiter"
    if si = 0 then do
      let st ← st.join w none
      st.setOut th []
    else do
      let n ← match ← ins.handles.get si with
        | .wset n => pure n
        | _ => .error (.trap "join: not a waitable set")
      let st ← st.join w (some n)
      st.setOut th []
  | .subtaskCancel async i => do
    let (th, _, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let s ← match ← ins.handles.get i with
      | .sub s => pure s
      | _ => .error (.trap "subtask.cancel: not a subtask")
    let x ← st.getSub s
    trapIf x.delivered "subtask.cancel: resolve delivered"
    trapIf x.cancelRequested "subtask.cancel: already requested"
    trapIf x.wset.isSome "subtask.cancel: in a waitable set"
    if !x.state.resolved then do
      let st := st.setSub s { x with cancelRequested := true, syncWaiter := true }
      -- `on_cancel()`: `Task.request_cancellation` (L467–476) of the callee
      let task ← st.getTask x.callee
      if task.isHost then
        afterCancelHere st th s async
      else if task.state = .initial then do
        -- the implicit thread waits to enter: resumed, it cancels the task and exits, and
        -- control comes back here through `After.cancel`
        let st := st.setTask x.callee { task with state := .pendingCancel }
        let it ← need task.implicitThread "implicit thread"
        st.resumeThread it (.cancel s async)
      else do
        check (task.state = .started) "request_cancellation: STARTED"
        let st := st.setTask x.callee { task with state := .pendingCancel }
        let it ← need task.implicitThread "implicit thread"
        let itT ← st.getThread it
        if itT.cancellable && st.ready it then st.resumeThread it (.cancel s async)
        else afterCancelHere st th s async
    else do
      let (st, (_, _, p)) ← st.deliverSub s
      st.setOut th [p]
  | .subtaskDrop i => do
    let (th, _, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let (st, ent) ← st.removeHandle x.inst i
    let s ← match ent with
      | .sub s => pure s
      | _ => .error (.trap "subtask.drop: not a subtask")
    let y ← st.getSub s
    trapIf (!y.delivered) "subtask.drop: not delivered"
    let st ← st.join (.sub s) none
    st.setOut th []
  | .streamNew t => newEnds st true t
  | .futureNew t => newEnds st false t
  | .copy kind t async i ptr len => st.opCopy kind t async i ptr len
  | .cancelCopy kind t async i coin => st.opCancel kind t async i coin
  | .dropEnd kind t i => do
    let (th, _, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let (st, ent) ← st.removeHandle x.inst i
    let e ← match ent with
      | .end_ e => pure e
      | _ => .error (.trap "drop: not an end")
    let y ← st.getEnd e
    trapIf (y.kind != kind) "drop: wrong end type"
    trapIf (y.t != t) "drop: element type"
    trapIf (y.state = .copying || y.state = .cancelling) "drop: copying"
    trapIf (kind = .futureW && y.state != .done) "drop: future not written"
    let st ← dropH pumpFuel st e
    st.setOut th []
  | .forward stream t ri wi => do
    let (th, _, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let (st, ent) ← st.removeHandle x.inst ri
    let r ← match ent with
      | .end_ e => pure e
      | _ => .error (.trap "forward: not an end")
    let y ← st.getEnd r
    trapIf (y.kind != (if stream then .streamR else .futureR)) "forward: readable"
    trapIf (y.t != t) "forward: type"
    trapIf (y.state != .idle) "forward: idle"
    trapIf y.wset.isSome "forward: in set"
    let (st, ent) ← st.removeHandle x.inst wi
    let w ← match ent with
      | .end_ e => pure e
      | _ => .error (.trap "forward: not an end")
    let z ← st.getEnd w
    trapIf (z.kind != (if stream then .streamW else .futureW)) "forward: writable"
    trapIf (z.t != t) "forward: type"
    trapIf (z.state != .idle) "forward: idle"
    trapIf z.wset.isSome "forward: in set"
    let st ← st.forwardEnd r w
    st.setOut th []
  | .threadIndex => do
    let (th, t, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let i ← need t.index "thread.index"
    st.setOut th [i]
  | .threadNewIndirect c => do
    let (th, t, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let n := st.nThreads
    let st := { st with threads := upd st.threads n (some { task := t.task, status := .suspended (.start c) }),
                        nThreads := n + 1 }
    let st ← st.registerThread t.task n
    let nt ← st.getThread n
    st.setOut th [nt.index.getD 0]
  | .threadResumeLater i => do
    let (th, _, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let o ← threadAt ins i
    trapIf (!st.isSuspended o) "resume-later: not suspended"
    check (o != th) "resume-later: other"
    let ot ← st.getThread o
    let k ← match ot.status with
      | .suspended k => pure k
      | _ => .error (.assert "suspended")
    let st ← st.blockWaiting o k
    st.setOut th []
  | .threadSuspend => do
    let (th, _, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let st ← st.blockSuspended th .retZero
    st.yieldControl
  | .threadYield => do
    let (th, _, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    st.waitUntil th .retZero
  | .threadSuspendThenResume i => do
    let (th, _, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let o ← threadAt ins i
    trapIf (!st.isSuspended o) "not suspended"
    check (o != th) "other"
    let st ← st.blockSuspended th .retZero
    st.switchTo o
  | .threadYieldThenResume i => do
    let (th, _, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let o ← threadAt ins i
    trapIf (!st.isSuspended o) "not suspended"
    check (o != th) "other"
    let st ← st.blockWaiting th .retZero
    st.switchTo o
  | .threadSuspendThenPromote i => do
    let (th, t, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    trapIf (t.index == some i) "promote self"
    let o ← threadAt ins i
    if st.ready o then do
      let st ← st.blockSuspended th .retZero
      st.switchTo o
    else do
      let st ← st.blockSuspended th .retZero
      st.yieldControl
  | .threadYieldThenPromote i => do
    let (th, t, _, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    trapIf (t.index == some i) "promote self"
    let o ← threadAt ins i
    if st.ready o then do
      let st ← st.blockWaiting th .retZero
      st.switchTo o
    else st.waitUntil th .retZero
  | .errNew msg => do
    let (th, _, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let (st, i) ← st.addHandle x.inst (.errctx (if st.det then 0 else msg))
    st.setOut th [i]
  | .errDrop i => do
    let (th, _, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let (st, ent) ← st.removeHandle x.inst i
    match ent with
    | .errctx _ => st.setOut th []
    | _ => .error (.trap "error-context.drop: not an error context")
  | .lower f async args => do
    let (_, _, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let s := st.nSubs
    let st := { st with subs := upd st.subs s (some
      { callerInst := x.inst, async := async, args := args, callee := st.nTasks }), nSubs := s + 1 }
    let (st, _) ← st.startCallee f (.sub s) (.lower s)
    pure st
  | .memSet ptr vs => do
    let (_, _, x, ins) ← st.ctx
    pure (st.setInst x.inst { ins with mem := fun a =>
      if ptr ≤ a ∧ a < ptr + vs.length then vs.getD (a - ptr) default else ins.mem a })
  | .coreReturn vs => do
    let (th, t, x, _) ← st.ctx
    check (!x.optsAsync) "coreReturn: sync options"
    let st ← st.taskReturn t.task (vs.map .num)
    let st ← st.exitImplicit t.task th
    st.yieldControl
  | .coreReturnL vs => do
    let (th, t, x, _) ← st.ctx
    check (!x.optsAsync) "coreReturn: sync options"
    let (st, rs) ← st.liftArgs x.inst vs
    let st ← st.taskReturn t.task rs
    let st ← st.exitImplicit t.task th
    st.yieldControl
  | .taskReturnL rty vs => do
    let (th, t, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    trapIf (!x.optsAsync) "task.return: sync options"
    trapIf (rty != x.resultTy) "task.return: result type"
    let (st, rs) ← st.liftArgs x.inst vs
    let st ← st.taskReturn t.task rs
    st.setOut th []
  | .coreExit => do
    let (th, t, x, _) ← st.ctx
    check (x.optsAsync && !x.callback) "coreExit: async stackful"
    let st ← st.exitImplicit t.task th
    st.yieldControl
  | .cbReturn packed => do
    let (th, t, x, _) ← st.ctx
    check (x.optsAsync && x.callback) "cbReturn: callback"
    let (code, si) ← unpackCallback packed
    if code = .exit then do
      let st ← st.exitImplicit t.task th
      st.yieldControl
    else do
      let (st, c) ← st.deliverPendingCancel t.task
      if c then st.setOut th [EventCode.taskCancelled.toNat, 0, 0]
      else do
        let ins ← st.getInst x.inst
        check (ins.exclusive == some th) "callback: exclusive is the implicit thread"
        let st := st.setInst x.inst { ins with exclusive := none }
        let t ← st.getThread th
        let st := st.setThread th { t with cancellable := true }
        if code = .yield then st.waitUntil th (.cbYield t.task)
        else do
          let ins ← st.getInst x.inst
          let w ← match ← ins.handles.get si with
            | .wset w => pure w
            | _ => .error (.trap "callback WAIT: not a waitable set")
          let ws ← st.getWs w
          let st := st.setWs w { ws with numWaiting := ws.numWaiting + 1 }
          st.waitUntil th (.cbWait t.task w)
  | .threadExit => do
    let (th, t, _, _) ← st.ctx
    let st ← st.unregisterThread t.task th
    let t ← st.getThread th
    let st := st.setThread th { t with status := .exited }
    st.yieldControl
  | .hostStart => do
    let (th, t, x, _) ← st.ctx
    check x.isHost "hostStart: host task"
    check (x.state = .initial) "start: INITIAL"
    let st := st.setTask t.task { x with state := .started }
    let (st, args) ← st.onStart x.caller
    let t ← st.getThread th
    pure (st.setThread th { t with hostArgs := args })
  | .hostResolve vs => do
    let (th, t, x, _) ← st.ctx
    check x.isHost "hostResolve: host task"
    let st ← st.taskReturn t.task vs
    st.setOut th []
  | .hostWaitPending e => do
    let (th, _, _, _) ← st.ctx
    st.waitUntil th (.hostPending e)
  | .hostExit => do
    let (th, t, x, _) ← st.ctx
    check x.isHost "hostExit: host task"
    let st := st.setThread th { t with status := .exited }
    st.yieldControl
  | .waitFlag f => do
    let (th, _, _, _) ← st.ctx
    st.waitUntil th (.flag f)
  | .setFlag f => pure { st with flags := upd st.flags f true }
  | .hostWaitReader p => do
    let (th, _, _, _) ← st.ctx
    st.waitUntil th (.hostReader p)
where
  /-- `afterCancel` in the calling thread itself (no thread was resumed). -/
  afterCancelHere (st : Store α) (th s : Nat) (async : Bool) : M (Store α) := do
    let (st, blocked) ← st.afterCancel th s async
    if blocked then st.returnControl else pure st
  /-- `canon_{stream,future}_new` (L2412–2426): the result packs `r | w << 32`. -/
  newEnds (st : Store α) (stream : Bool) (t : Ty) : M (Store α) := do
    let (th, _, x, ins) ← st.ctx
    trapIf (!ins.mayLeave) "may_leave"
    let (st, r, w) := st.newPair stream t (some x.inst)
    let (st, ri) ← st.addHandle x.inst (.end_ r)
    let y ← st.getEnd r
    let st := st.setEnd r { y with index := some ri }
    let (st, wi) ← st.addHandle x.inst (.end_ w)
    let z ← st.getEnd w
    let st := st.setEnd w { z with index := some wi }
    st.setOut th [ri + wi * 2 ^ 32]

/-- **One step of a script.** -/
def runStep (st : Store α) : Step α → M (Store α)
  | .op o => st.runOp o
  | .tick th => do
    check st.stack.isEmpty "tick: nesting depth 0"
    check st.cur.isNone "tick: no running thread"
    check st.topLoop.isNone "tick: nesting depth 0 (no canon lift loop running)"
    check (st.waiting.contains th && st.ready th) "tick: a ready waiting thread"
    st.resumeThread th .nothing
  | .invoke f args => do
    check st.cur.isNone "invoke: from the embedder"
    check st.topLoop.isNone "invoke: no canon lift loop running"
    let (st, _) ← st.startCallee f (.host args) .nothing
    pure st
  | .hostNew stream t => pure (st.newPair stream t none).1
  | .hostWrite e vs => do
    let (st, b) := st.newBuf { inst := none, length := vs.length, src := vs }
    copyH pumpFuel st e b
  | .hostRead e n => do
    let (st, b) := st.newBuf { inst := none, length := n }
    copyH pumpFuel st e b
  | .hostTake e => do
    let (st, ev) ← st.deliverEnd e
    pure { st with hostEvents := ev :: st.hostEvents }
  | .hostDrop e => dropH pumpFuel st e
  | .hostCancel e coin => st.cancelEnd e coin
  | .setBackpressure i v => do
    let ins ← st.getInst i
    pure (st.setInst i { ins with backpressure := v })
  | .loopPicks ths => pure { st with picks := ths }
  | .writerNew t vs chunk dwe => st.newWriter t vs chunk dwe
  | .readerNew e remain onData => st.newReader e remain onData
  | .writerWrite p vs => do
    let w ← st.getWriter p
    runPump pumpFuel (st.setPump p (.writer { w with queue := w.queue ++ vs })) p
  | .writerEndWhenEmpty p => do
    let w ← st.getWriter p
    runPump pumpFuel (st.setPump p (.writer { w with dropWhenEmpty := true })) p
  | .readerSetRemain p n => do
    let r ← st.getReader p
    runPump pumpFuel (st.setPump p (.reader { r with remain := n })) p
  | .readerTakeTo p wp f => do
    let r ← st.getReader p
    let st := st.setPump p (.reader { r with received := [] })
    if r.received.isEmpty then pure st else do
      let w ← st.getWriter wp
      runPump pumpFuel (st.setPump wp (.writer { w with queue := w.queue ++ r.received.map f })) wp

/-- Run a script. -/
def run (st : Store α) : List (Step α) → M (Store α)
  | [] => pure st
  | s :: ss => do
    let st ← st.runStep s
    st.run ss

end Store

/-- A store with `n` guest instances with empty tables and memory filled with `default`. -/
def Store.init {α : Type} [Inhabited α] (n : Nat) : Store α :=
  { insts := fun i => if i < n then some { mem := fun _ => default } else none, nInsts := n }

end Silmaril.Wasm.Component.Async.Cabi
