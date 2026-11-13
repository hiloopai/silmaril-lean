module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Task.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Task.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Flat
public import Silmaril.Raw.Wasm.Component.Runtime.Task

/-!
# Task, context and backpressure built-ins

Transcribes the task-level canon built-ins of REF `design/mvp/canonical-abi/definitions.py` at
component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>;
`CanonicalABI.md` §"Canonical Definitions") as specification programs in `P E σ`. Every built-in
returns the list of flat values core code receives (REF `return [...]`).

| Lean | REF (lines) | `may_leave` check |
| --- | --- | --- |
| `contextGet t i` | `canon_context_get` (L2275-2281) | none |
| `contextSet t i v` | `canon_context_set` (L2285-2291) | none |
| `backpressureInc` | `canon_backpressure_inc` (L2295-2300) | none |
| `backpressureDec` | `canon_backpressure_dec` (L2302-2307) | none |
| `taskReturn lim q result opts flatArgs` | `canon_task_return` (L2311-2320) | `cannotLeave` |
| `taskCancel` | `canon_task_cancel` (L2324-2329) | `cannotLeave` |

**`may_leave`.** As in REF, `context.get/set` and `backpressure.inc/dec` perform NO
`trap_if(not task.inst.may_leave)` check (like `resource.rep`); `task.return` and
`task.cancel` do (trap `cannotLeave`).

**Store updates.** Each REF mutation is one named pure function: `setContextSt` (the
`thread.storage[i] = v` of `context.set`), `incBackpressureSt`/`decBackpressureSt` (the
`inst.backpressure += 1`/`-= 1` of `backpressure.inc/dec`). `task.return`/`task.cancel`
mutate only through `Runtime.Task.return_`/`Runtime.Task.cancel` and the lifting of
`liftFlatValues`. `P.Inv` lemmas are proved for every program.

## Deviations and non-claims

* `backpressure.inc/dec`: REF first updates the counter and then traps
  (`trap_if(backpressure == 2**16)` / `trap_if(backpressure < 0)`); here the trap is evaluated
  first, with the same conditions (`AsyncRef.backpressureInc?`/`AsyncRef.backpressureDec?`, bound
  `AsyncRef.backpressureLimit = 2^16`), and the counter is only updated when no trap fires. A trap
  locks the whole store down (head semantics), so the two orders are indistinguishable. Proved
  here only at the level of the pure update: if the counter is in `[0, 2^16)` before the call
  (the REF assert, not a hypothesis of the programs) and no trap fires, it is in `[0, 2^16)`
  afterwards (`incBackpressureSt_lt`, `decBackpressureSt_lt`); no store-level invariant about
  the counter is proved. Neither built-in wakes any thread: waiters on the K1 backpressure
  gate merely become ready (REF).
* `context.get/set` (D-f): REF asserts `t ∈ {i32, i64}` (guaranteed by `AddrType`),
  `i < len(thread.storage)` (validation guarantees `i < AsyncRef.contextSlotCount = 2`) and the
  value range `v < 2^(ptr_size(t)*8)`. The index assert is handled by trapping `contextIndex`
  (unreachable for validated components); the value range is a precondition: `contextSet`
  stores the given number unchanged and `contextGet` returns `result mod 2^width` as a flat
  value of the pointer type (`ptrFlat`).
* `task.return`: the REF checks `trap_if(result_type != task.ft.result)` and
  `trap_if(not LiftOptions.equal(opts, task.opts))` both trap `taskReturnInvalid` (the two
  `trap_if`s are kept in REF order). `opts` is a `CanonOpts E` whose non-`LiftOptions` fields
  are ignored (`Runtime/Options.lean`). `Quirks.weakTaskReturnMemCheck` (wasmtime `a7b4f29`,
  `task_return` in `crates/wasmtime/src/runtime/component/concurrent.rs`) replaces
  `LiftOptions.equal` by `taskReturnOptsOk`: equal string encodings, and the memories are compared
  only when `task.return` has one. Only `Quirks.none` is the specification. The cursor returned by
  `liftFlatValues` is discarded, as REF discards its `CoreValueIter` (REF asserts nothing about
  leftover arguments).
* `Quirks.lendReleaseAtReturn` is NOT applied here: REF `task.return` releases no lends; the
  wasmtime quirk is an optional branch of the caller's `on_resolve` (`canon_lower`,
  `Canon/Lower.lean`), which `Runtime.Task.return_` reaches through the late-bound `call (.onResolve
  ..)`.
* REF `current_task()`/`current_thread()`/`current_instance()` are asserted to exist on a
  built-in's frame; a host frame is `internal` (`Canon.currentTask`/`currentThreadId`).
* Tests: a few kernel `rfl` checks of the pure store updates and of the option check. The
  built-ins are exercised end to end by the machine examples and the `run_tests.py` ports.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type}

/-! ## Pure store updates -/

theorem taskReturnOptsOk_none (opts taskOpts : CanonOpts E) :
    taskReturnOptsOk Quirks.none opts taskOpts = opts.liftEqual taskOpts := rfl

/-- The weak check accepts everything the REF check accepts. -/
theorem taskReturnOptsOk_of_liftEqual (q : Quirks) {opts taskOpts : CanonOpts E}
    (h : opts.liftEqual taskOpts = true) : taskReturnOptsOk q opts taskOpts = true := by
  rw [CanonOpts.liftEqual_iff] at h
  obtain ⟨he, hm⟩ := h
  unfold taskReturnOptsOk
  split
  · cases hmo : opts.memory with
    | none => simp [he]
    | some m => simp [he, ← hm, hmo]
  · rw [CanonOpts.liftEqual_iff]; exact ⟨he, hm⟩

/-! ## Context built-ins -/

/-! ## Backpressure built-ins -/

/-! ## Task built-ins -/

/-! ## Invariant preservation -/

namespace P.Inv

/-! The program-logic combinators are those of `Canon.P.Inv` (referred to by full name, since
their names coincide with the programs of `Canon`). -/

variable {I : CStore E → Prop}

end P.Inv

/-! ## Frame lemmas -/

/-- `context.set` touches only the thread arena. -/
theorem setContextSt_frame (t : ThreadId) (i v : Nat) (s : CStore E) :
    setContextSt t i v s = { s with threads := (setContextSt t i v s).threads } := rfl

/-- `backpressure.inc` changes no instance field other than `backpressure`. -/
theorem incBackpressureSt_frame (st : InstState) :
    (incBackpressureSt st).handles = st.handles ∧ (incBackpressureSt st).threads = st.threads ∧
      (incBackpressureSt st).mayLeave = st.mayLeave ∧
      (incBackpressureSt st).numWaitingToEnter = st.numWaitingToEnter ∧
      (incBackpressureSt st).exclusive = st.exclusive :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `backpressure.dec` changes no instance field other than `backpressure`. -/
theorem decBackpressureSt_frame (st : InstState) :
    (decBackpressureSt st).handles = st.handles ∧ (decBackpressureSt st).threads = st.threads ∧
      (decBackpressureSt st).mayLeave = st.mayLeave ∧
      (decBackpressureSt st).numWaitingToEnter = st.numWaitingToEnter ∧
      (decBackpressureSt st).exclusive = st.exclusive :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Counter range -/

/-- When the overflow check of `backpressure.inc` passes, the update is the checked value. -/
theorem incBackpressureSt_eq {st : InstState} {m : Nat}
    (h : AsyncRef.backpressureInc? st.backpressure = some m) :
    (incBackpressureSt st).backpressure = m := by
  unfold AsyncRef.backpressureInc? at h
  split at h <;> simp_all [incBackpressureSt]

/-- When the underflow check of `backpressure.dec` passes, the update is the checked value. -/
theorem decBackpressureSt_eq {st : InstState} {m : Nat}
    (h : AsyncRef.backpressureDec? st.backpressure = some m) :
    (decBackpressureSt st).backpressure = m := by
  unfold AsyncRef.backpressureDec? at h
  split at h <;> simp_all [decBackpressureSt]

/-- Range preservation of `backpressure.inc` (REF assert `0 <= backpressure < 2^16`): if the
counter is below the limit and the overflow check passes, the new counter is below the limit. -/
theorem incBackpressureSt_lt {st : InstState}
    (hlt : st.backpressure < AsyncRef.backpressureLimit)
    (hok : (AsyncRef.backpressureInc? st.backpressure).isSome) :
    (incBackpressureSt st).backpressure < AsyncRef.backpressureLimit := by
  unfold AsyncRef.backpressureInc? at hok
  split at hok
  · simp at hok
  · simp only [incBackpressureSt]; omega

/-- Range preservation of `backpressure.dec`: the new counter is below the limit whenever the
old one is (and the underflow check guarantees the old counter was positive). -/
theorem decBackpressureSt_lt {st : InstState}
    (hlt : st.backpressure < AsyncRef.backpressureLimit) :
    (decBackpressureSt st).backpressure < AsyncRef.backpressureLimit := by
  simp only [decBackpressureSt]; omega

/-! ## Checks -/

section Checks

/-- Thread 0 of task 0, with the initial context `[0, 0]`. -/
private def s0 : CStore E := { CStore.empty with threads := [{ task := ⟨0⟩ }] }

/-- `context.set 1 7` then reading slot 1 gives `7`; slot 0 is unchanged. -/
example : ((setContextSt ⟨0⟩ 1 7 (s0 : CStore E)).thread? ⟨0⟩).map (·.storage) =
    some [0, 7] := rfl

/-- An out-of-range slot leaves the storage unchanged. -/
example : ((setContextSt ⟨0⟩ 2 7 (s0 : CStore E)).thread? ⟨0⟩).map (·.storage) =
    some [0, 0] := rfl

example : (incBackpressureSt { backpressure := 3 }).backpressure = 4 := rfl
example : (decBackpressureSt { backpressure := 3 }).backpressure = 2 := rfl

/-- The overflow and underflow trap conditions. -/
example : (AsyncRef.backpressureInc? (2 ^ 16 - 1)).isNone = true := by decide
example : (AsyncRef.backpressureInc? (2 ^ 16 - 2)).isNone = false := by decide
example : (AsyncRef.backpressureDec? 0).isNone = true := by decide

/-- Without quirks, a `task.return` without memory does not match a lift with memory; with
`Quirks.wasmtime` it does. -/
example (m : E.MemAddr) :
    taskReturnOptsOk Quirks.none ({} : CanonOpts E) { memory := some m } = false := by
  simp [taskReturnOptsOk, Quirks.none, CanonOpts.liftEqual]

example (m : E.MemAddr) :
    taskReturnOptsOk Quirks.wasmtime ({} : CanonOpts E) { memory := some m } = true := by
  simp [taskReturnOptsOk, Quirks.wasmtime]

/-- Different string encodings are rejected under both checks. -/
example (q : Quirks) :
    taskReturnOptsOk q ({ encoding := .utf16 } : CanonOpts E) {} = false := by
  unfold taskReturnOptsOk
  split <;> simp [CanonOpts.liftEqual]

end Checks

end Silmaril.Wasm.Component.Canon.Builtins
