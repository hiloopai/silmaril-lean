module

public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Effects
public import Silmaril.Raw.Wasm.Component.Features

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

open Engine AsyncRef Canon

/-! ## Thread predicates -/

namespace Thread

theorem blocked_iff (th : Thread) :
    th.blocked = true ↔ th.running = false ∧ th.exited = false := by
  cases h : th.status <;> simp [blocked, running, exited, h]

theorem blocked_eq_suspended_or_waiting (th : Thread) :
    th.blocked = (th.suspended || th.waiting) := by
  cases h1 : th.blocked <;> cases h2 : th.readyCond <;> simp [suspended, waiting, h1, h2]

end Thread

/-! ## Ready conditions -/

section Eval

variable {E : CoreEngine}

/-- Only `.host` consults the host readiness function. -/
theorem ReadyCond.eval_hostReady_irrel (hostReady hostReady' : Nat → Bool) (s : CStore E)
    {rc : ReadyCond} (h : ∀ n, rc ≠ .host n) : rc.eval hostReady s = rc.eval hostReady' s := by
  cases rc <;> first | rfl | exact absurd rfl (h _)

theorem Thread.ready_waiting {hostReady : Nat → Bool} {s : CStore E} {th : Thread}
    (h : th.ready hostReady s = true) : th.waiting = true := by
  unfold Thread.ready at h
  unfold Thread.waiting
  cases hb : th.blocked <;> cases hr : th.readyCond <;> simp_all

theorem CStore.mem_candidates {hostReady : Nat → Bool} {s : CStore E} {t : ThreadId} :
    t ∈ s.candidates hostReady ↔ t ∈ s.waiting ∧ s.threadReady hostReady t = true := by
  simp [candidates]

theorem CStore.mem_instCandidates {hostReady : Nat → Bool} {s : CStore E} {inst : InstId}
    {st : InstState} (h : s.inst? inst = some st) {t : ThreadId} :
    t ∈ s.instCandidates hostReady inst ↔
      t ∈ st.threads.elements ∧ s.threadReady hostReady t = true := by
  simp [instCandidates, h]

end Eval

/-! ## Named store updates -/

section Updates

variable {E : CoreEngine}

theorem CStore.thread?_startWaitingSt (t u : ThreadId) (rc : ReadyCond) (s : CStore E) :
    (s.startWaitingSt t rc).thread? u =
      if t = u then (s.thread? u).map fun th => { th with readyCond := some rc }
      else s.thread? u := by
  simp only [startWaitingSt, thread?]
  exact (ArenaField.threads (E := E)).get?_modify _ _ _ _

theorem CStore.thread?_stopWaitingSt (t u : ThreadId) (s : CStore E) :
    (s.stopWaitingSt t).thread? u =
      if t = u then (s.thread? u).map fun th => { th with readyCond := none }
      else s.thread? u := by
  simp only [stopWaitingSt, thread?]
  exact (ArenaField.threads (E := E)).get?_modify _ _ _ _

/-- `start_waiting` touches only the thread arena and `waiting`. -/
theorem CStore.startWaitingSt_frame (t : ThreadId) (rc : ReadyCond) (s : CStore E) :
    let s' := s.startWaitingSt t rc
    s'.core = s.core ∧ s'.insts = s.insts ∧ s'.tasks = s.tasks ∧ s'.subtasks = s.subtasks ∧
      s'.ends = s.ends ∧ s'.wsets = s.wsets ∧ s'.nestingDepth = s.nestingDepth ∧
      s'.lockdown = s.lockdown :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `stop_waiting` touches only the thread arena and `waiting`. -/
theorem CStore.stopWaitingSt_frame (t : ThreadId) (s : CStore E) :
    let s' := s.stopWaitingSt t
    s'.core = s.core ∧ s'.insts = s.insts ∧ s'.tasks = s.tasks ∧ s'.subtasks = s.subtasks ∧
      s'.ends = s.ends ∧ s'.wsets = s.wsets ∧ s'.nestingDepth = s.nestingDepth ∧
      s'.lockdown = s.lockdown :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Updates

/-! ## Thread methods as programs -/

namespace Thread

variable {E : CoreEngine} {σ : Type}

/-- Only a host predicate reads `hr`. -/
theorem readyNow_hr_irrel (hr hr' : HostReady σ) {rc : ReadyCond} (h : ∀ n, rc ≠ .host n) :
    (readyNow hr rc : P E σ Bool) = readyNow hr' rc := by
  cases rc <;> first | rfl | exact absurd rfl (h _)

/-- For a non-host condition, `waitUntil` does not depend on `hr`. -/
theorem waitUntil_eq_guest (hr : HostReady σ) (site : WaitSite) {rc : ReadyCond}
    (h : ∀ n, rc ≠ .host n) : (waitUntil hr site rc : P E σ Unit) = waitUntilGuest site rc := by
  unfold waitUntilGuest waitUntil
  rw [readyNow_hr_irrel hr (fun _ _ => false) h]

/-! ### Program-logic lemmas -/

section Inv

variable {I : CStore E → Prop}

end Inv

end Thread

/-! ## Tests: ready conditions and candidates on tiny stores -/

section Tests

variable {E : CoreEngine}

/-- A tiny store: instance 0 with backpressure 0 and no exclusive thread, instance 1 with
backpressure 1, instance 2 with an exclusive thread; task 0 pending cancellation in instance
2; subtask 0 returned with a pending event, subtask 1 started; waitable set 0 containing
subtask 1, set 1 containing subtask 0; threads 0 (waiting on `.always`), 1 (waiting on
subtask 1), 2 (suspended), 3 (running, no condition); instance 0 registers threads 0-2. -/
private def tinyTask : Task E where
  ft := ⟨[], none, false⟩
  opts := {}
  inst := ⟨2⟩
  caller := ⟨0⟩
  state := .pendingCancel

private def tinySubtask0 : Subtask where
  inst := ⟨0⟩
  state := .returned
  common := { pending := some (.subtask ⟨0⟩) }

private def tiny : CStore E :=
  { CStore.empty with
    insts := [{ threads := ⟨#[none, some ⟨0⟩, some ⟨1⟩, some ⟨2⟩], []⟩ },
      { backpressure := 1 }, { exclusive := some ⟨3⟩ }]
    tasks := [tinyTask]
    subtasks := [tinySubtask0, { inst := ⟨0⟩, state := .started }]
    wsets := [{ elems := [.subtask ⟨1⟩] }, { elems := [.subtask ⟨0⟩] }]
    threads := [{ task := ⟨0⟩, readyCond := some .always },
      { task := ⟨0⟩, readyCond := some (.subtaskResolved ⟨1⟩) },
      { task := ⟨0⟩ }, { task := ⟨0⟩, status := .running }]
    waiting := [⟨1⟩, ⟨0⟩] }

private def noHost : Nat → Bool := fun _ => false

private abbrev ev (rc : ReadyCond) : Bool := ReadyCond.eval noHost (tiny : CStore E) rc

example : ev (E := E) (.backpressure ⟨0⟩ true) = true := rfl
example : ev (E := E) (.backpressure ⟨1⟩ false) = false := rfl
example : ev (E := E) (.backpressure ⟨2⟩ false) = true := rfl
example : ev (E := E) (.backpressure ⟨2⟩ true) = false := rfl
example : ev (E := E) (.backpressure ⟨9⟩ false) = false := rfl
example : ev (E := E) (.exclusiveFree ⟨0⟩) = true := rfl
example : ev (E := E) (.exclusiveFree ⟨2⟩) = false := rfl
example : ev (E := E) (.callbackWait ⟨0⟩ ⟨0⟩ ⟨0⟩) = true := rfl
example : ev (E := E) (.callbackWait ⟨1⟩ ⟨5⟩ ⟨1⟩) = true := rfl
example : ev (E := E) (.callbackWait ⟨1⟩ ⟨5⟩ ⟨0⟩) = false := rfl
example : ev (E := E) (.callbackWait ⟨2⟩ ⟨0⟩ ⟨1⟩) = false := rfl
example : ev (E := E) (.wsetHasEvent ⟨0⟩) = false := rfl
example : ev (E := E) (.wsetHasEvent ⟨1⟩) = true := rfl
example : ev (E := E) (.waitableHasEvent (.subtask ⟨0⟩)) = true := rfl
example : ev (E := E) (.waitableHasEvent (.end_ ⟨0⟩)) = false := rfl
example : ev (E := E) (.subtaskResolved ⟨0⟩) = true := rfl
example : ev (E := E) (.subtaskResolved ⟨1⟩) = false := rfl
example : ReadyCond.eval (· == 3) (tiny : CStore E) (.host 3) = true := rfl
example : ev (E := E) (.host 3) = false := rfl

example : (tiny : CStore E).candidates noHost = [⟨0⟩] := rfl
example : (tiny : CStore E).instCandidates noHost ⟨0⟩ = [⟨0⟩] := rfl
example : (tiny : CStore E).instCandidates noHost ⟨1⟩ = [] := rfl
example : (tiny : CStore E).threadIs Thread.suspended ⟨2⟩ = true := rfl
example : (tiny : CStore E).threadIs Thread.waiting ⟨1⟩ = true := rfl
example : (tiny : CStore E).threadIs Thread.running ⟨3⟩ = true := rfl
example : (tiny : CStore E).threadReady noHost ⟨3⟩ = false := rfl

/-- After subtask 1 resolves, thread 1 becomes a candidate too (in `waiting` order). -/
example : ({ (tiny : CStore E) with
    subtasks := [{ inst := ⟨0⟩, state := .returned }, { inst := ⟨0⟩, state := .returned }] }
    ).candidates noHost = [⟨1⟩, ⟨0⟩] := rfl

/-- `start_waiting` then `stop_waiting` on the suspended thread 2. -/
example : (((tiny : CStore E).startWaitingSt ⟨2⟩ .always).candidates noHost) = [⟨0⟩, ⟨2⟩] :=
  rfl
example : ((((tiny : CStore E).startWaitingSt ⟨2⟩ .always).stopWaitingSt ⟨2⟩).waiting) =
    [⟨1⟩, ⟨0⟩] := rfl
example : ((((tiny : CStore E).startWaitingSt ⟨2⟩ .always).stopWaitingSt ⟨2⟩).threadIs
    Thread.suspended ⟨2⟩) = true := rfl

end Tests

end Silmaril.Wasm.Component.Runtime
