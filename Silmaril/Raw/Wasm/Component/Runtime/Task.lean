module

public import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Thread

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

/-- The K1 ready condition is exactly `not has_backpressure()`. -/
theorem ReadyCond.eval_backpressure {E : CoreEngine} (hostReady : Nat → Bool) (s : CStore E)
    {inst : InstId} {st : InstState} (h : s.inst? inst = some st) (ne : Bool) :
    (ReadyCond.backpressure inst ne).eval hostReady s = !st.hasBackpressure ne := by
  simp [ReadyCond.eval, h, InstState.hasBackpressure]

section Updates

variable {E : CoreEngine}

theorem CStore.task?_setTaskState (task u : TaskId) (st : TaskState) (s : CStore E) :
    (s.setTaskState task st).task? u =
      if task = u then (s.task? u).map (Task.withState st) else s.task? u := by
  simp only [setTaskState, task?]
  exact (ArenaField.tasks (E := E)).get?_modify _ _ _ _

/-- Setting a task state touches only the task arena: the result is `s` with only its `tasks`
field replaced. -/
theorem CStore.setTaskState_frame (task : TaskId) (st : TaskState) (s : CStore E) :
    s.setTaskState task st = { s with tasks := (s.setTaskState task st).tasks } :=
  rfl

end Updates

/-! ## Task methods as programs -/

namespace Task

variable {E : CoreEngine} {σ : Type}

/-! ### Program-logic lemmas -/

section Inv

variable {I : CStore E → Prop}

theorem hasPendingCancel_inv (task : TaskId) : P.Inv I (hasPendingCancel task : P E σ Bool) :=
  P.Inv.gets _

end Inv

end Task

/-! ## Checks of the pure store updates -/

section Tests

variable {E : CoreEngine}

private def tk0 : Task E where
  ft := ⟨[], none, true⟩
  opts := { async_ := true }
  inst := ⟨0⟩
  caller := ⟨0⟩

/-- Instance 0 with an empty thread table, task 0 (stackful async), thread 0 of task 0. -/
private def s0 : CStore E :=
  { CStore.empty with
    insts := [{}]
    tasks := [tk0]
    threads := [{ task := ⟨0⟩ }] }

/-- A stackful async task does not need the exclusive lock; a callback one does. -/
example : (tk0 : Task E).needsExclusive = false := rfl
example : ({ (tk0 : Task E) with opts := ({} : CanonOpts E) } : Task E).needsExclusive =
    true := rfl

/-- `register_thread` gets index 1 (index 0 is reserved) and records it everywhere. -/
example : let s := (s0 : CStore E).registerThreadSt ⟨0⟩ ⟨0⟩
    (s.task? ⟨0⟩).map (·.threads) = some [⟨0⟩] ∧
    (s.thread? ⟨0⟩).map (·.index) = some (some 1) ∧
    (s.inst? ⟨0⟩).map (·.threads.get? 1) = some (some ⟨0⟩) := ⟨rfl, rfl, rfl⟩

/-- `unregister_thread` undoes it (the thread keeps its stale index, as in REF). -/
example : let s := ((s0 : CStore E).registerThreadSt ⟨0⟩ ⟨0⟩).unregisterThreadSt ⟨0⟩ ⟨0⟩ 1
    (s.task? ⟨0⟩).map (·.threads) = some [] ∧
    (s.inst? ⟨0⟩).map (·.threads.get? 1) = some none := ⟨rfl, rfl⟩

example : ((s0 : CStore E).setTaskState ⟨0⟩ .pendingCancel).taskPendingCancel ⟨0⟩ = true :=
  rfl

example : ({ backpressure := 1 } : InstState).hasBackpressure false = true := rfl
example : ({ exclusive := some ⟨3⟩ } : InstState).hasBackpressure false = false := rfl
example : ({ exclusive := some ⟨3⟩ } : InstState).hasBackpressure true = true := rfl

end Tests

end Silmaril.Wasm.Component.Runtime
