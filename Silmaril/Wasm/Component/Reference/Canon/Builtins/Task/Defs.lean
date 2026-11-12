module

public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Defs

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
  first, with the same conditions (`Async.backpressureInc?`/`Async.backpressureDec?`, bound
  `Async.backpressureLimit = 2^16`), and the counter is only updated when no trap fires. A trap
  locks the whole store down (head semantics), so the two orders are indistinguishable. Proved
  here only at the level of the pure update: if the counter is in `[0, 2^16)` before the call
  (the REF assert, not a hypothesis of the programs) and no trap fires, it is in `[0, 2^16)`
  afterwards (`incBackpressureSt_lt`, `decBackpressureSt_lt`); no store-level invariant about
  the counter is proved. Neither built-in wakes any thread: waiters on the K1 backpressure
  gate merely become ready (REF).
* `context.get/set` (D-f): REF asserts `t ∈ {i32, i64}` (guaranteed by `AddrType`),
  `i < len(thread.storage)` (validation guarantees `i < Async.contextSlotCount = 2`) and the
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

/-- The `thread.storage[i] = v` update of REF `canon_context_set` (L2290) on thread `t`
(unchanged for a dangling id or an index out of range). -/
def setContextSt (t : ThreadId) (i v : Nat) (s : CStore E) : CStore E :=
  ArenaField.threads.modify s t fun th => { th with storage := th.storage.set i v }

/-- `inst.backpressure += 1` (REF `canon_backpressure_inc`, L2298). -/
def incBackpressureSt (st : InstState) : InstState :=
  { st with backpressure := st.backpressure + 1 }

/-- `inst.backpressure -= 1` (REF `canon_backpressure_dec`, L2305); only issued when the
counter is positive. -/
def decBackpressureSt (st : InstState) : InstState :=
  { st with backpressure := st.backpressure - 1 }

/-- The option check of `task.return` (REF L2316): `LiftOptions.equal(opts, task.opts)`
(`CanonOpts.liftEqual`: same encoding, same memory, both absent counting as equal). With
`q.weakTaskReturnMemCheck` (wasmtime's `task_return`): same encoding, and the same
memory only when `opts` has a memory. -/
def taskReturnOptsOk (q : Quirks) (opts taskOpts : CanonOpts E) : Bool :=
  if q.weakTaskReturnMemCheck then
    decide (opts.encoding = taskOpts.encoding) &&
      (match opts.memory with
        | some m => decide (taskOpts.memory = some m)
        | none => true)
  else opts.liftEqual taskOpts

/-! ## Context built-ins -/

/-- REF `canon_context_get(t, i)` (L2275-2281): `[current_thread().storage[i]]` as a flat
value of type `t`. No `may_leave` check (REF). Preconditions (REF asserts, D-f): the value is
below `2^(ptr_size(t)*8)`; `i < len(storage)` is guaranteed by validation (`i < 2`), and an
index out of range traps `contextIndex` (unreachable for validated components). -/
def contextGet (t : AddrType) (i : Nat) : P E σ (List FlatValue) := do
  let th ← getThread (← currentThreadId)
  let v ← orTrap .contextIndex th.storage[i]?
  return [ptrFlat t v]

/-- REF `canon_context_set(t, i, v)` (L2285-2291): `current_thread().storage[i] = v`, as the
single store update `setContextSt`; returns `[]`. No `may_leave` check (REF). Preconditions
(REF asserts, D-f): `v < 2^(ptr_size(t)*8)` (the pointer type `t` is otherwise unused);
`i < len(storage)` is guaranteed by validation, and an index out of range traps
`contextIndex`. -/
def contextSet (_t : AddrType) (i v : Nat) : P E σ (List FlatValue) := do
  let t ← currentThreadId
  let th ← getThread t
  trapIf (decide (th.storage.length ≤ i)) .contextIndex
  modifyStore (setContextSt t i v)
  return []

/-! ## Backpressure built-ins -/

/-- REF `canon_backpressure_inc()` (L2295-2300): trap `backpressureOverflow` when the counter
would reach `Async.backpressureLimit = 2^16`, else `inst.backpressure += 1`
(`incBackpressureSt`); returns `[]`. No `may_leave` check and no wakeup (REF). The trap is
evaluated before the update (see the module docstring). Precondition (REF assert):
`0 <= backpressure < 2^16`. -/
def backpressureInc : P E σ (List FlatValue) := do
  let inst ← currentInst
  let st ← getInst inst
  trapIf (Async.backpressureInc? st.backpressure).isNone .backpressureOverflow
  modifyInst inst incBackpressureSt
  return []

/-- REF `canon_backpressure_dec()` (L2302-2307): trap `backpressureUnderflow` when the counter
is `0` (REF `trap_if(backpressure < 0)` after the decrement), else `inst.backpressure -= 1`
(`decBackpressureSt`); returns `[]`. No `may_leave` check and no wakeup (REF). Precondition
(REF assert): `0 <= backpressure < 2^16`. -/
def backpressureDec : P E σ (List FlatValue) := do
  let inst ← currentInst
  let st ← getInst inst
  trapIf (Async.backpressureDec? st.backpressure).isNone .backpressureUnderflow
  modifyInst inst decBackpressureSt
  return []

/-! ## Task built-ins -/

/-- REF `canon_task_return(result_type, opts, flat_args)` (L2311-2320):
`task = current_task()`; trap `cannotLeave` unless `task.inst.may_leave`; trap `taskNotAsync`
unless `task.opts.async_`; trap `taskReturnInvalid` if `result_type != task.ft.result`, then
if not `LiftOptions.equal(opts, task.opts)` (`taskReturnOptsOk q`, with the
`Quirks.weakTaskReturnMemCheck` branch); lift the result with
`lift_flat_values(cx, MAX_FLAT_PARAMS, CoreValueIter(flat_args), task.ft.result_type())`
where `cx = LiftLowerContext(opts, task.inst, task)` (L2317: borrows are scoped to the task);
`task.return_(result)`; return `[]`. -/
def taskReturn (lim : Limits) (q : Quirks) (result : Option (WIT.ClosedType RtId))
    (opts : CanonOpts E) (flatArgs : List FlatValue) : P E σ (List FlatValue) := do
  let task ← currentTask
  let tk ← getTask task
  let st ← getInst tk.inst
  trapIf (!st.mayLeave) .cannotLeave
  trapIf (!tk.opts.async_) .taskNotAsync
  trapIf (decide (result ≠ tk.ft.result)) .taskReturnInvalid
  trapIf (!taskReturnOptsOk q opts tk.opts) .taskReturnInvalid
  let cx : LiftLowerContext E := { opts := opts, inst := tk.inst, scope := .task task }
  let (vs, _) ← liftFlatValues lim q cx ABI.maxFlatParams (.ofList flatArgs)
    tk.ft.result.toList
  Runtime.Task.return_ task vs
  return []

/-- REF `canon_task_cancel()` (L2324-2329): `task = current_task()`; trap `cannotLeave` unless
`task.inst.may_leave`; trap `taskNotAsync` unless `task.opts.async_`; `task.cancel()` (it
traps `taskCancelNotCancelled` unless the cancel was delivered, `borrowsRemain` if borrows
remain; `on_resolve(None)`); return `[]`. -/
def taskCancel : P E σ (List FlatValue) := do
  let task ← currentTask
  let tk ← getTask task
  let st ← getInst tk.inst
  trapIf (!st.mayLeave) .cannotLeave
  trapIf (!tk.opts.async_) .taskNotAsync
  Runtime.Task.cancel task
  return []

/-! ## Invariant preservation -/

namespace P.Inv

/-! The program-logic combinators are those of `Canon.P.Inv` (referred to by full name, since
their names coincide with the programs of `Canon`). -/

variable {I : CStore E → Prop}

end P.Inv

/-! ## Frame lemmas -/

/-! ## Counter range -/

/-! ## Checks -/

section Checks

end Checks

end Silmaril.Wasm.Component.Canon.Builtins
