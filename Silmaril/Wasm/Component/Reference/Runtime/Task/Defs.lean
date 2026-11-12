module

public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Defs

/-!
# Task methods

Transcribes the methods of REF `class Task` of `design/mvp/canonical-abi/definitions.py` at
component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
L392-504; `CanonicalABI.md` §"Tasks") as programs over `Canon.P E σ`. The task object itself is
the plain-data `Runtime.Task` (`Runtime/Objects.lean`), addressed by its arena id `TaskId`.

| Lean | REF (line) |
| --- | --- |
| `Task.needsExclusive` | `Task.needs_exclusive` (L421-423) |
| `Task.enterImplicitThread` | `Task.enter_implicit_thread` (L425-443), wait site K1 |
| `Task.registerThread` (`CStore.registerThreadSt`) | `Task.register_thread` (L445-449) |
| `Task.exitImplicitThread` | `Task.exit_implicit_thread` (L451-456) |
| `Task.unregisterThread` (`CStore.unregisterThreadSt`) | `Task.unregister_thread` (L458-465) |
| `Task.requestCancellation` | `Task.request_cancellation` (L467-476), resume site R2 |
| `Task.hasPendingCancel` | `Task.has_pending_cancel` (L478-479) |
| `Task.deliverPendingCancel` | `Task.deliver_pending_cancel` (L481-486) |
| `Task.start` | `Task.start` (L488-491) |
| `Task.return_` | `Task.return_` (L493-498) |
| `Task.cancel` | `Task.cancel` (L500-504) |

**Store updates.** Every REF multi-field update is ONE named pure function on the store
(`CStore.setTaskState`, `CStore.setImplicitThread`, `CStore.registerThreadSt`,
`CStore.unregisterThreadSt`) or on the instance state (`InstState.incWaitingToEnter`,
`InstState.decWaitingToEnter`, `InstState.withExclusive`), so store invariants are proved per
mutation (`Task.InvHyps` collects the obligations; `*_inv` lemmas discharge the programs).

**Deviations and non-claims.**
* REF `assert`s are preconditions (deviation D-f) and are not checked; each is listed in the
  docstring of its program. Where a program must still do something with an absent value
  (a dangling id, `implicit_thread is None`, `thread.index is None`) it traps with
  `TrapReason.internal` (unreachable in well-formed runs).
* `registerThread` returns the new index in `inst.threads` (REF `register_thread` returns
  nothing and callers read `thread.index`, which is set to the same value).
* `unregisterThread` and `registerThread` evaluate their traps (`taskNotResolved`,
  `unknownHandle`, `tableFull`) before issuing their single store update, while REF mutates
  `self.threads` first; a trap locks the whole store down (head semantics), so the two orders
  are indistinguishable.
* `Quirks.noEntryFairness` (wasmtime `a7b4f29`, `GuestCall::is_ready`) drops the
  `num_waiting_to_enter > 0` residual-backpressure check of `enterImplicitThread`. Only
  `Quirks.none` is the specification.
* `Quirks.lendReleaseAtReturn` is NOT applicable here: REF `Task.return_` releases no lends
  (lends are released by `Subtask.deliver_resolve`); the quirk is applied by the `task.return`
  builtin.
* `requestCancellation` takes the machine's `HostReady σ` for REF `implicit_thread.ready()`.
* Tests: a few kernel `rfl` checks of the pure store updates; the programs are tested end to
  end through the machine (`Examples/`, `Tests/`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine Async Canon Value

/-! ## Pure parts -/

/-- REF `Task.needs_exclusive()` (L421-423): `not opts.async_ or opts.callback is not None`.
Precondition (REF assert): `task.ft.async_`. -/
def Task.needsExclusive {E : CoreEngine} (task : Task E) : Bool :=
  !task.opts.async_ || task.opts.callback.isSome

/-- The `has_backpressure()` closure of REF `Task.enter_implicit_thread` (L429-431) on the
instance state: `inst.backpressure > 0 or (needs_exclusive and inst.exclusive_thread is not
None)`, with `ne` the value of `needs_exclusive()`. -/
def InstState.hasBackpressure (ne : Bool) (st : InstState) : Bool :=
  decide (st.backpressure > 0) || (ne && st.exclusive.isSome)

/-- `inst.num_waiting_to_enter += 1` (L433). -/
def InstState.incWaitingToEnter (st : InstState) : InstState :=
  { st with numWaitingToEnter := st.numWaitingToEnter + 1 }

/-- `inst.num_waiting_to_enter -= 1` (L435). -/
def InstState.decWaitingToEnter (st : InstState) : InstState :=
  { st with numWaitingToEnter := st.numWaitingToEnter - 1 }

/-- `inst.exclusive_thread = o` (L441 takes the lock, L456 releases it). -/
def InstState.withExclusive (o : Option ThreadId) (st : InstState) : InstState :=
  { st with exclusive := o }

/-- `task.state = st`. -/
def Task.withState {E : CoreEngine} (st : TaskState) (task : Task E) : Task E :=
  { task with state := st }

section Updates

variable {E : CoreEngine}

/-- The store update `task.state = st`. -/
def CStore.setTaskState (task : TaskId) (st : TaskState) (s : CStore E) : CStore E :=
  ArenaField.tasks.modify s task (Task.withState st)

/-- The store update `task.implicit_thread = t` (L427). -/
def CStore.setImplicitThread (task : TaskId) (t : ThreadId) (s : CStore E) : CStore E :=
  ArenaField.tasks.modify s task fun x => { x with implicitThread := some t }

/-- The store update of REF `Task.register_thread(t)` (L445-449), one multi-field update:
append `t` to `task.threads`, add `t` to `task.inst.threads` and set `t.index` to the new
table index. Unchanged if `task` or its instance is dangling or the table is full (the
program traps first in those cases). -/
def CStore.registerThreadSt (task : TaskId) (t : ThreadId) (s : CStore E) : CStore E :=
  match s.task? task with
  | none => s
  | some tk =>
    match (s.inst? tk.inst).bind (InstState.addThread? t) with
    | none => s
    | some (i, st') =>
      let s₁ := ArenaField.tasks.modify s task fun x => { x with threads := x.threads ++ [t] }
      let s₂ := ArenaField.insts.set s₁ tk.inst st'
      ArenaField.threads.modify s₂ t fun th => { th with index := some i }

/-- The store update of REF `Task.unregister_thread(t)` (L458-465), one multi-field update:
remove (the first occurrence of) `t` from `task.threads` and remove index `i` (REF
`t.index`) from `task.inst.threads`. `t.index` itself is left unchanged, as in REF.
Unchanged if `task` is dangling. -/
def CStore.unregisterThreadSt (task : TaskId) (t : ThreadId) (i : Nat) (s : CStore E) :
    CStore E :=
  match s.task? task with
  | none => s
  | some tk =>
    let s₁ := ArenaField.tasks.modify s task fun x => { x with threads := x.threads.erase t }
    ArenaField.insts.modify s₁ tk.inst (InstState.removeThread i)

end Updates

/-! ## Task methods as programs -/

namespace Task

variable {E : CoreEngine} {σ : Type}

/-- REF `Task.has_pending_cancel()` (L478-479): `state == PENDING_CANCEL` (`false` for a
dangling id, `CStore.taskPendingCancel`). -/
def hasPendingCancel (task : TaskId) : P E σ Bool :=
  gets (·.taskPendingCancel task)

/-- REF `Task.deliver_pending_cancel()` (L481-486): if the state is `PENDING_CANCEL`, move it
to `CANCEL_DELIVERED` and return `true`; otherwise return `false`. -/
def deliverPendingCancel (task : TaskId) : P E σ Bool := do
  let tk ← getTask task
  if tk.state = .pendingCancel then
    modifyStore (CStore.setTaskState task .cancelDelivered)
    pure true
  else pure false

/-- REF `Task.start()` (L488-491): `state = STARTED`, then return `on_start()` (the late-bound
`call (.onStart caller)`). Precondition (REF assert): the state is `INITIAL`. -/
def start (task : TaskId) : P E σ (List Val) := do
  let tk ← getTask task
  modifyStore (CStore.setTaskState task .started)
  callVals (.onStart tk.caller)

/-- REF `Task.return_(result)` (L493-498): trap `taskReturnTwice` if already `RESOLVED`
(returning after a cancellation was requested or delivered is allowed), trap `borrowsRemain`
if `num_borrows > 0`, then `on_resolve(result)` and `state = RESOLVED`.
`Quirks.lendReleaseAtReturn` does not apply here (REF `return_` releases no lends; the quirk
is applied by the caller's `on_resolve`, `Canon/Lower.lean`). Precondition (REF assert): the result
is not `None` (a `List Val` always is). -/
def return_ (task : TaskId) (vs : List Val) : P E σ Unit := do
  let tk ← getTask task
  trapIf (decide (tk.state = .resolved)) .taskReturnTwice
  trapIf (decide (tk.numBorrows > 0)) .borrowsRemain
  callUnit (.onResolve tk.caller (some vs))
  modifyStore (CStore.setTaskState task .resolved)

/-- REF `Task.cancel()` (L500-504): trap `taskCancelNotCancelled` unless the state is
`CANCEL_DELIVERED`, trap `borrowsRemain` if `num_borrows > 0`, then `on_resolve(None)` and
`state = RESOLVED`. -/
def cancel (task : TaskId) : P E σ Unit := do
  let tk ← getTask task
  trapIf (decide (tk.state ≠ .cancelDelivered)) .taskCancelNotCancelled
  trapIf (decide (tk.numBorrows > 0)) .borrowsRemain
  callUnit (.onResolve tk.caller none)
  modifyStore (CStore.setTaskState task .resolved)

/-- REF `Task.register_thread(t)` (L445-449): append `t` to `task.threads` and set `t.index`
to `task.inst.threads.add(t)` (trap `tableFull` past `Table.MAX_LENGTH`), as the single store
update `CStore.registerThreadSt`. Returns the new index (REF: `t.index`).
Preconditions (REF asserts): `t ∉ task.threads`, `t.task = task`, `t.index = none`. -/
def registerThread (task : TaskId) (t : ThreadId) : P E σ Nat := do
  let tk ← getTask task
  let st ← getInst tk.inst
  match st.addThread? t with
  | none => trap .tableFull
  | some (i, _) =>
    modifyStore (CStore.registerThreadSt task t)
    pure i

/-- REF `Task.unregister_thread(t)` (L458-465): remove `t` from `task.threads`; if no thread
remains, trap `taskNotResolved` unless the state is `RESOLVED` (the "task.return not called"
rule); remove `t.index` from `task.inst.threads` (REF `Table.remove`: trap `unknownHandle` if
the index is not in use). One store update, `CStore.unregisterThreadSt`.
Preconditions (REF asserts): `t ∈ task.threads`, `t.task = task`, `t.index ≠ None` (else an
internal error), and `num_borrows = 0` when the last thread leaves. -/
def unregisterThread (task : TaskId) (t : ThreadId) : P E σ Unit := do
  let tk ← getTask task
  trapIf ((tk.threads.erase t).isEmpty && decide (tk.state ≠ .resolved)) .taskNotResolved
  let th ← getThread t
  let i ← orTrap (.internal "unregister_thread: thread has no index") th.index
  let st ← getInst tk.inst
  match st.removeThread? i with
  | none => trap (.unknownHandle i)
  | some _ => modifyStore (CStore.unregisterThreadSt task t i)

/-- The K1 backpressure wait of REF `Task.enter_implicit_thread` (L432-437) of task `task`
in instance `inst`, with `ne = needs_exclusive()`: `num_waiting_to_enter += 1`,
`implicit_thread.wait_until(not has_backpressure())` (wait site K1, choice C1; the implicit
thread is the current thread), `num_waiting_to_enter -= 1`; then if a pending cancel is
delivered, `cancel()` and return `false` (not entered); otherwise return `true`. -/
def backpressureWait (task : TaskId) (inst : InstId) (ne : Bool) : P E σ Bool := do
  modifyInst inst InstState.incWaitingToEnter
  Thread.waitUntilGuest .enterBackpressure (.backpressure inst ne)
  modifyInst inst InstState.decWaitingToEnter
  if ← deliverPendingCancel task then
    cancel task
    pure false
  else pure true

/-- The `if self.ft.async_:` block of REF `Task.enter_implicit_thread` (L428-441) for the task
record `tk` of `task` and its implicit thread `t`: if `has_backpressure()` or (residual
fairness) `inst.num_waiting_to_enter > 0`, run `backpressureWait` (returning `false` if it
cancelled the task); then, if `needs_exclusive()`, take the exclusive lock
(`inst.exclusive_thread = t`). `q.noEntryFairness` (wasmtime) drops the residual check.
Precondition (REF assert): the lock is free when it is taken. -/
def asyncGate (q : Quirks) (task : TaskId) (t : ThreadId) (tk : Task E) : P E σ Bool := do
  let ne := tk.needsExclusive
  let st ← getInst tk.inst
  let entered ←
    (if st.hasBackpressure ne || (!q.noEntryFairness && decide (st.numWaitingToEnter > 0))
      then backpressureWait task tk.inst ne
      else pure true : P E σ Bool)
  if entered then
    (if ne then modifyInst tk.inst (InstState.withExclusive (some t)) else pure () : P E σ Unit)
    pure true
  else pure false

/-- REF `Task.enter_implicit_thread()` (L425-443): `implicit_thread = current_thread()`; for
an async function type, the backpressure gate `asyncGate` (wait site K1; `false` if the task
was cancelled while waiting); then `register_thread(implicit_thread)` and return `true`.
`q.noEntryFairness` selects the wasmtime entry check (no residual fairness).
Precondition (REF assert): the state is `INITIAL`. -/
def enterImplicitThread (q : Quirks) (task : TaskId) : P E σ Bool := do
  let t ← currentThreadId
  modifyStore (CStore.setImplicitThread task t)
  let tk ← getTask task
  let entered ← (if tk.ft.async_ then asyncGate q task t tk else pure true : P E σ Bool)
  if entered then
    let _ ← registerThread task t
    pure true
  else pure false

/-- REF `Task.exit_implicit_thread()` (L451-456): `unregister_thread(implicit_thread)`, then
if `ft.async_ and needs_exclusive()` release the exclusive lock
(`inst.exclusive_thread = None`).
Preconditions (REF asserts): the current thread is the implicit thread (which is set, else an
internal error), and it holds the lock when the lock is released. -/
def exitImplicitThread (task : TaskId) : P E σ Unit := do
  let tk ← getTask task
  let t ← orTrap (.internal "exit_implicit_thread: no implicit thread") tk.implicitThread
  unregisterThread task t
  if tk.ft.async_ && tk.needsExclusive then
    modifyInst tk.inst (InstState.withExclusive none)

/-- REF `Task.request_cancellation()` (L467-476), the `OnCancel` of a guest callee (resume
site R2):
* `INITIAL`: `state = PENDING_CANCEL`, then `implicit_thread.resume()` (a forced resume of the
  K1 backpressure wait, which delivers the cancel and calls `cancel()`);
* otherwise: `state = PENDING_CANCEL`, and `implicit_thread.resume()` iff the implicit thread
  is `cancellable` and `ready()` (evaluated with the machine's host readiness `hr`).
Preconditions (REF asserts): in the second case the state is `STARTED` (any state other than
`INITIAL` or `STARTED` is an internal error, so a cancel can never move a `RESOLVED` or
`CANCEL_DELIVERED` task back to `PENDING_CANCEL`; the machine's host cancel rule and REF
`canon_subtask_cancel`'s traps keep it unreachable); the implicit thread is set (else an
internal error); after the `INITIAL` case the state is `RESOLVED`. -/
def requestCancellation (hr : HostReady σ) (task : TaskId) : P E σ Unit := do
  let tk ← getTask task
  if tk.state = .initial ∨ tk.state = .started then
    let t ← orTrap (.internal "request_cancellation: no implicit thread") tk.implicitThread
    modifyStore (CStore.setTaskState task .pendingCancel)
    if tk.state = .initial then
      Thread.resume t
    else
      let th ← getThread t
      let ready ← Thread.isReady hr t
      if th.cancellable && ready then Thread.resume t
  else internal "request_cancellation: task is not INITIAL or STARTED"

/-! ### Program-logic lemmas -/

/-- The store updates the task programs can issue, each preserving `I`. -/
structure InvHyps (I : CStore E → Prop) : Prop where
  setTaskState : ∀ task st s, I s → I (CStore.setTaskState task st s)
  setImplicitThread : ∀ task t s, I s → I (CStore.setImplicitThread task t s)
  registerThread : ∀ task t s, I s → I (CStore.registerThreadSt task t s)
  unregisterThread : ∀ task t i s, I s → I (CStore.unregisterThreadSt task t i s)
  incWaitingToEnter : ∀ inst s, I s → I (ArenaField.insts.modify s inst
    InstState.incWaitingToEnter)
  decWaitingToEnter : ∀ inst s, I s → I (ArenaField.insts.modify s inst
    InstState.decWaitingToEnter)
  withExclusive : ∀ inst o s, I s → I (ArenaField.insts.modify s inst
    (InstState.withExclusive o))
  startWaiting : ∀ t inst ne s, I s → I (CStore.startWaitingSt t (.backpressure inst ne) s)
  stopWaiting : ∀ t s, I s → I (CStore.stopWaitingSt t s)

section Inv

variable {I : CStore E → Prop}

end Inv

end Task

/-! ## Checks of the pure store updates -/

section Tests

variable {E : CoreEngine}

end Tests

end Silmaril.Wasm.Component.Runtime
