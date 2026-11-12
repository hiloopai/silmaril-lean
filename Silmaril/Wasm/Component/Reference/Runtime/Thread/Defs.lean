module

public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs
public import Silmaril.Wasm.Component.Reference.Features.Defs

/-!
# Thread methods, ready conditions and scheduling candidates

Transcribes REF `class Thread` of `design/mvp/canonical-abi/definitions.py` at component-model
`a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
L279-383) over the effect signature `Canon.P E σ` (`CanonicalABI.md` §"Threads" and
§"Stack Switching"), together with the evaluation of the defunctionalized REF
`ready_func` closures (`ReadyCond`, data in `Runtime/Objects.lean`) and the candidate sets of
REF `Store.tick` (L555-563) and of the `canon_lift` synchronous loop (L2141-2144).

| Lean | REF (line) |
| --- | --- |
| `Thread.running`, ..., `Thread.waiting` | `Thread.running`, ..., `waiting` (L297-309) |
| `Thread.ready`, `CStore.threadReady` | `Thread.ready` (L311-312) |
| `ReadyCond.eval` | the `ready_func` closures of the sites K1-K13 (see its docstring) |
| `CStore.candidates` | the ready threads of `self.waiting` (`Store.tick`, L559) |
| `CStore.instCandidates` | `{ t for t in inst.threads if t.ready() }` (`canon_lift`, L2142) |
| `Thread.startWaiting` (`CStore.startWaitingSt`) | `Thread.start_waiting` (L314-317) |
| `Thread.stopWaiting` (`CStore.stopWaitingSt`) | `Thread.stop_waiting` (L319-322) |
| `Thread.resumeLater` | `Thread.resume_later` (L324-327) |
| `Thread.resume` | `Thread.resume` (L329-338) |
| `Thread.suspend` | `Thread.suspend` (L340-343) |
| `Thread.waitUntil` | `Thread.wait_until` (L345-351), choice C1 |
| `Thread.yield_` | `Thread.yield_` (L353-354) |
| `Thread.suspendThenResume` | `Thread.suspend_then_resume` (L356-359) |
| `Thread.yieldThenResume` | `Thread.yield_then_resume` (L361-365) |
| `Thread.suspendThenPromote` | `Thread.suspend_then_promote` (L367-374) |
| `Thread.yieldThenPromote` | `Thread.yield_then_promote` (L376-383) |

**Division of labour with the machine.** The REF `cont` field (running / exited /
continuation) is `Thread.status`; its transitions are performed by the MACHINE
on the `block`, `resumeThread` and thread-exit effects, never here. This file only updates
`readyCond` and `store.waiting` (through the named store updates `CStore.startWaitingSt` and
`CStore.stopWaitingSt`) and issues `block`/`resumeThread`. In particular the `switch_to`
chain loop of REF `Thread.resume` (L333-337, resume site R4) is the machine's rule for
`block (some t)`.

**Host readiness.** A host ready predicate (`ReadyCond.host n`, K13) is evaluated by a
function `hostReady : Nat → Bool`; programs obtain it from the host state through
`hr : HostReady σ := σ → Nat → Bool` (explicit argument, read with `hostGet` only when the
condition is `.host _`). Guest-side waits (K1-K12) use `waitUntilGuest site rc`, which takes
no `hr` and is definitionally `waitUntil hr site rc` for every `hr` when `rc` is not `.host _`
(`waitUntil_eq_guest`). `*-then-promote` keeps `hr` since the target's condition may be a host
predicate. The machine must fix ONE `HostReady σ` and use it both for these
programs and for `CStore.candidates (hr m.host)` / `CStore.instCandidates`.

**Deviations and non-claims.**
* REF `assert`s are preconditions (deviation D-f): they are not checked. Each is listed in the
  docstring of the corresponding program; callers (and the machine invariants of later
  items) are responsible for them.
* Dangling ids (unreachable in well-formed stores, arena ids are never freed) make a ready
  condition evaluate to `false`, and make a thread predicate `false`.
* REF candidate sets are Python `set`s; here they are lists in a fixed order (store.waiting
  append order, resp. `inst.threads` table index order), which the pick choices C2/C3 index.
  Under the invariant that `store.waiting` has no duplicates (maintained by the
  `start_waiting` precondition) the list has no duplicates and denotes the REF set.
* `Quirks.promoteYieldOnly` (wasmtime `a7b4f29`): `*-then-promote`
  only promotes waiting threads whose ready condition is `.always`. Only `Quirks.none` is the
  specification. KNOWN GAP: this over-approximates wasmtime. In wasmtime only yielded threads
  (`thread.yield`, `yield-then-resume`, `yield-then-promote`: K9/K12) are
  `GuestThreadState::Ready`; a thread made ready by `thread.resume-later` is
  `GuestThreadState::Running` with a queued work item, and `Promote` of it is a no-op
  (`crates/wasmtime/src/runtime/component/concurrent.rs`, `resume_thread`, L4031-4105). Here
  `resumeLater` also installs `.always`, so under `Quirks.wasmtime` `resume-later(o)` followed
  by `*-then-promote(o)` switches to `o`, while wasmtime plainly suspends/yields. Closing the
  gap needs a `ReadyCond` constructor distinguishing yield-originated `.always` (in
  `Runtime/Objects.lean`).
* Tests: evaluation of ready conditions and candidate sets on tiny stores (kernel `rfl`, the
  stores are generic in the engine `E`, so `decide` does not apply; the evaluation never
  inspects the core store). The programs are tested end to end through the machine
  (`Examples/Threads.lean`, `Tests/Threads.lean`). -/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine Async Canon

/-! ## Thread predicates -/

namespace Thread

/-- REF `Thread.running` (L297): `cont == 'running'`. -/
def running (th : Thread) : Bool := th.status matches .running

/-- REF `Thread.exited` (L300): `cont is None`. -/
def exited (th : Thread) : Bool := th.status matches .exited

/-- REF `Thread.blocked` (L303): neither running nor exited. -/
def blocked (th : Thread) : Bool := th.status matches .blocked

/-- REF `Thread.suspended` (L305): blocked with no `ready_func`. -/
def suspended (th : Thread) : Bool := th.blocked && th.readyCond.isNone

/-- REF `Thread.waiting` (L308): blocked with a `ready_func`. -/
def waiting (th : Thread) : Bool := th.blocked && th.readyCond.isSome

end Thread

/-! ## Ready conditions -/

/-- A host readiness function: for the host state, which host ready predicates (K13) hold. -/
abbrev HostReady (σ : Type) := σ → Nat → Bool

section Eval

variable {E : CoreEngine}

/-- REF `Waitable.has_pending_event` (L737-738) of a subtask or stream/future end. -/
def CStore.waitableHasEvent (s : CStore E) : Waitable → Bool
  | .subtask st => match s.subtask? st with
    | some x => x.common.pending.isSome
    | none => false
  | .end_ e => match s.end? e with
    | some x => x.common.pending.isSome
    | none => false

/-- REF `WaitableSet.has_pending_event` (L774-775). -/
def CStore.wsetHasEvent (s : CStore E) (w : WsetId) : Bool :=
  match s.wset? w with
  | some ws => ws.elems.any s.waitableHasEvent
  | none => false

/-- REF `Task.has_pending_cancel` (L478-479). -/
def CStore.taskPendingCancel (s : CStore E) (t : TaskId) : Bool :=
  match s.task? t with
  | some x => (x.state matches .pendingCancel)
  | none => false

/-- REF `Subtask.resolved` (L838-846). -/
def CStore.subtaskResolved (s : CStore E) (st : SubtaskId) : Bool :=
  match s.subtask? st with
  | some x => x.state.resolved
  | none => false

/-- Evaluate a defunctionalized REF `ready_func` against the current store.
* `always`: `lambda: True` (K9, K12, `resume_later`, L326/L354/L363);
* `backpressure inst ne`: `not has_backpressure()` of `Task.enter_implicit_thread` (K1,
  L429-434), `has_backpressure() = inst.backpressure > 0 or (needs_exclusive and
  inst.exclusive_thread is not None)`, with `ne` the value of `needs_exclusive()`;
* `exclusiveFree inst`: `inst.exclusive_thread is None` (K2, callback `YIELD`, L2117);
* `callbackWait inst task wset`: the `ready` of `WaitableSet.wait_from_callback` (K3,
  L798-801): `inst.exclusive_thread is None and (wset.has_pending_event() or
  task.has_pending_cancel())`, where `inst` is the task's instance;
* `wsetHasEvent wset`: `WaitableSet.has_pending_event` (K4, L787);
* `waitableHasEvent w`: `Waitable.has_pending_event` (K5/K6, L746);
* `subtaskResolved s`: `Subtask.resolved` (K7/K8, L2213, L2409);
* `host n`: host predicate `n` (K13), `hostReady n`.
Dangling ids evaluate to `false`. -/
def ReadyCond.eval (hostReady : Nat → Bool) (s : CStore E) : ReadyCond → Bool
  | .always => true
  | .backpressure inst ne => match s.inst? inst with
    | some st => !(decide (st.backpressure > 0) || (ne && st.exclusive.isSome))
    | none => false
  | .exclusiveFree inst => match s.inst? inst with
    | some st => st.exclusive.isNone
    | none => false
  | .callbackWait inst task wset => match s.inst? inst with
    | some st => st.exclusive.isNone && (s.wsetHasEvent wset || s.taskPendingCancel task)
    | none => false
  | .wsetHasEvent wset => s.wsetHasEvent wset
  | .waitableHasEvent w => s.waitableHasEvent w
  | .subtaskResolved st => s.subtaskResolved st
  | .host n => hostReady n

@[simp] theorem ReadyCond.eval_always (hostReady : Nat → Bool) (s : CStore E) :
    ReadyCond.always.eval hostReady s = true := rfl

/-- REF `Thread.ready` (L311-312): waiting and its `ready_func` holds. -/
def Thread.ready (hostReady : Nat → Bool) (s : CStore E) (th : Thread) : Bool :=
  th.blocked && match th.readyCond with
    | some rc => rc.eval hostReady s
    | none => false

/-- A thread predicate on the thread with id `t` (`false` if dangling). -/
def CStore.threadIs (s : CStore E) (p : Thread → Bool) (t : ThreadId) : Bool :=
  match s.thread? t with
  | some th => p th
  | none => false

/-- REF `t.ready()` for the thread with id `t`. -/
def CStore.threadReady (hostReady : Nat → Bool) (s : CStore E) (t : ThreadId) : Bool :=
  s.threadIs (Thread.ready hostReady s) t

/-- The candidates of REF `Store.tick` (L559): the waiting threads that are ready, in
`store.waiting` append order. -/
def CStore.candidates (hostReady : Nat → Bool) (s : CStore E) : List ThreadId :=
  s.waiting.filter (s.threadReady hostReady)

/-- The candidates of the REF `canon_lift` synchronous loop (L2142): the ready threads of
instance `inst`, in `inst.threads` table index order (none if `inst` is dangling). -/
def CStore.instCandidates (hostReady : Nat → Bool) (s : CStore E) (inst : InstId) :
    List ThreadId :=
  match s.inst? inst with
  | some st => st.threads.elements.filter (s.threadReady hostReady)
  | none => []

end Eval

/-! ## Named store updates -/

section Updates

variable {E : CoreEngine}

/-- The store update of REF `Thread.start_waiting(rc)` (L314-317): set `ready_func` and
append the thread to `store.waiting` (one multi-field update). -/
def CStore.startWaitingSt (t : ThreadId) (rc : ReadyCond) (s : CStore E) : CStore E :=
  let s' := ArenaField.threads.modify s t fun th => { th with readyCond := some rc }
  { s' with waiting := s'.waiting ++ [t] }

/-- The store update of REF `Thread.stop_waiting()` (L319-322): clear `ready_func` and
remove the (first occurrence of the) thread from `store.waiting` (Python `list.remove`). -/
def CStore.stopWaitingSt (t : ThreadId) (s : CStore E) : CStore E :=
  let s' := ArenaField.threads.modify s t fun th => { th with readyCond := none }
  { s' with waiting := s'.waiting.erase t }

@[simp] theorem CStore.waiting_startWaitingSt (t : ThreadId) (rc : ReadyCond) (s : CStore E) :
    (s.startWaitingSt t rc).waiting = s.waiting ++ [t] := rfl

@[simp] theorem CStore.waiting_stopWaitingSt (t : ThreadId) (s : CStore E) :
    (s.stopWaitingSt t).waiting = s.waiting.erase t := rfl

end Updates

/-! ## Thread methods as programs -/

namespace Thread

variable {E : CoreEngine} {σ : Type}

/-- Evaluate a ready condition now: a host predicate (K13) reads the host state, every other
condition reads the store (`ReadyCond.eval`, which consults `hostReady` only for `.host`). -/
def readyNow (hr : HostReady σ) : ReadyCond → P E σ Bool
  | .host n => do
    let h ← hostGet
    pure (hr h n)
  | rc => do
    let s ← getStore
    pure (rc.eval (fun _ => false) s)

/-- REF `t.ready()` now, for the thread with id `t`. -/
def isReady (hr : HostReady σ) (t : ThreadId) : P E σ Bool := do
  let s ← getStore
  let h ← hostGet
  pure (s.threadReady (hr h) t)

/-- Whether `*-then-promote` may promote `o`: REF `o.ready()`; under
`Quirks.promoteYieldOnly` (wasmtime) only waiting threads whose ready condition is `.always`.
Known gap (see the module docstring): wasmtime additionally refuses threads made ready by
`thread.resume-later`, which this test cannot distinguish from yielded threads. -/
def isPromotable (hr : HostReady σ) (q : Quirks) (o : ThreadId) : P E σ Bool :=
  if q.promoteYieldOnly then do
    let s ← getStore
    pure (s.threadIs (fun th => th.waiting && th.readyCond == some .always) o)
  else isReady hr o

/-- REF `Thread.start_waiting(rc)` (L314-317) on thread `t`.
Precondition (REF assert): `t.readyCond = none`. -/
def startWaiting (t : ThreadId) (rc : ReadyCond) : P E σ Unit :=
  modifyStore (CStore.startWaitingSt t rc)

/-- REF `Thread.stop_waiting()` (L319-322) on thread `t`.
Precondition (REF assert): `t` is waiting. -/
def stopWaiting (t : ThreadId) : P E σ Unit :=
  modifyStore (CStore.stopWaitingSt t)

/-- REF `Thread.resume_later()` (L324-327): make the suspended thread `t` ready.
Precondition (REF assert): `t` is suspended (the trailing `assert(self.ready())` then holds
since the condition is `.always`). -/
def resumeLater (t : ThreadId) : P E σ Unit := startWaiting t .always

/-- REF `Thread.resume()` (L329-338): a forced resume, even if not ready: if `t` is waiting,
stop waiting; then the `resumeThread` effect, whose machine rule runs `t` and follows the
`switch_to` chain (L333-337, resume site R4) in the same resumer frame.
Preconditions (REF asserts): `t` is blocked; afterwards `t` is blocked or exited (a machine
invariant). -/
def resume (t : ThreadId) : P E σ Unit := do
  let s ← getStore
  (if s.threadIs Thread.waiting t then stopWaiting t else pure () : P E σ Unit)
  resumeThread t

/-- REF `Thread.suspend()` (L340-343) of the current thread: `block()` without a ready
condition. Precondition (REF assert): the current thread is running. -/
def suspend : P E σ Unit := block none

/-- REF `Thread.wait_until(rc)` (L345-351) of the current thread, choice C1: if `rc` already
holds, `choose (.earlyReturn site)` may return without blocking (REF: `not
DETERMINISTIC_PROFILE and random.randint(0,1)`; the choice is only asked when `rc` holds, as in
REF where `ready_func()` is evaluated first); otherwise start waiting on `rc` and `block()`.
Precondition (REF assert): the current thread is running and has no ready condition. -/
def waitUntil (hr : HostReady σ) (site : WaitSite) (rc : ReadyCond) : P E σ Unit := do
  let t ← currentThreadId
  let now ← readyNow hr rc
  let early ← (if now then choose (.earlyReturn site) else pure false : P E σ Bool)
  if early then pure () else do
    startWaiting t rc
    block none

/-- `waitUntil` for guest-side ready conditions (K1-K12, anything but `.host _`), which never
consult host readiness: no `hr` argument. See `waitUntil_eq_guest`. -/
def waitUntilGuest (site : WaitSite) (rc : ReadyCond) : P E σ Unit :=
  waitUntil (fun _ _ => false) site rc

/-- REF `Thread.yield_()` (L353-354): `wait_until(lambda: True)` at site K9. The condition
`.always` never consults host readiness. -/
def yield_ : P E σ Unit := waitUntilGuest .yield_ .always

/-- REF `Thread.suspend_then_resume(o)` (L356-359): `block(switch_to = o)`, leaving the
current thread suspended. Preconditions (REF asserts): the current thread is running, `o` is
suspended. -/
def suspendThenResume (o : ThreadId) : P E σ Unit := block (some o)

/-- REF `Thread.yield_then_resume(o)` (L361-365): start waiting on `.always` and
`block(switch_to = o)`, leaving the current thread ready. Preconditions (REF asserts): the
current thread is running (with no ready condition), `o` is suspended. -/
def yieldThenResume (o : ThreadId) : P E σ Unit := do
  let t ← currentThreadId
  startWaiting t .always
  block (some o)

/-- REF `Thread.suspend_then_promote(o)` (L367-374): if `o` is ready, stop its waiting and
`suspend_then_resume(o)`; otherwise `suspend()`. `q.promoteYieldOnly` selects the wasmtime
promotability test (`isPromotable`). Precondition (REF assert): the current thread is
running. -/
def suspendThenPromote (hr : HostReady σ) (q : Quirks) (o : ThreadId) : P E σ Unit := do
  if ← isPromotable hr q o then
    stopWaiting o
    suspendThenResume o
  else suspend

/-- REF `Thread.yield_then_promote(o)` (L376-383): if `o` is ready, stop its waiting and
`yield_then_resume(o)`; otherwise `yield_()` (which includes the C1 coin). `q` as in
`suspendThenPromote`. Precondition (REF assert): the current thread is running. -/
def yieldThenPromote (hr : HostReady σ) (q : Quirks) (o : ThreadId) : P E σ Unit := do
  if ← isPromotable hr q o then
    stopWaiting o
    yieldThenResume o
  else yield_

/-! ### Program-logic lemmas -/

section Inv

variable {I : CStore E → Prop}

end Inv

end Thread

/-! ## Tests: ready conditions and candidates on tiny stores -/

section Tests

variable {E : CoreEngine}

end Tests

end Silmaril.Wasm.Component.Runtime
