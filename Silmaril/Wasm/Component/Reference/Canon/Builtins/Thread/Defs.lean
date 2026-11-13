module

public import Silmaril.Wasm.Component.Reference.Runtime.Task.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs

/-!
# The `thread.*` built-ins

Transcribes the 🧵 built-ins of REF `design/mvp/canonical-abi/definitions.py` at
component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
as specification programs in `P E σ` over the thread methods of `Runtime/Thread.lean` and
the task methods of `Runtime/Task.lean` (`CanonicalABI.md` §"Canonical Definitions"):

| Lean | REF (line) |
| --- | --- |
| `threadIndex` | `canon_thread_index` (L2565-2569) |
| `threadNewIndirect tbl ft fi c` | `canon_thread_new_indirect` (L2578-2591) |
| `threadResumeLater i` | `canon_thread_resume_later` (L2594-2601) |
| `threadSuspend` | `canon_thread_suspend` (L2605-2609) |
| `threadYield` | `canon_thread_yield` (L2613-2617) |
| `threadSuspendThenResume i` | `canon_thread_suspend_then_resume` (L2621-2628) |
| `threadYieldThenResume i` | `canon_thread_yield_then_resume` (L2632-2639) |
| `threadSuspendThenPromote hr q i` | `canon_thread_suspend_then_promote` (L2643-2649) |
| `threadYieldThenPromote hr q i` | `canon_thread_yield_then_promote` (L2653-2659) |

Every built-in begins with `trap_if(not ... may_leave)` (`cannotLeave`), including
`thread.index` (L2567) and `thread.resume-later` (L2595); `thread.index` therefore traps
inside a `realloc` (which runs with `may_leave = False`). Each returns the flat core results
(`List FlatValue`) the dispatcher hands back to core code; `i`, `fi` are the unsigned
values of the flat arguments. `thread.suspend`, `thread.yield` and the four `*-then-*`
built-ins return `[0]` once the current thread is resumed (the `block` effect returns then).

Trap reasons: an index unknown to `inst.threads` traps `unknownHandle i` (REF `Table.get`);
`trap_if(not other_thread.suspended())` and `trap_if(i == thread.index)` trap
`cannotResumeThread` (the `.wast` message, see `TrapReason.cannotResumeThread`).

## Deviations and non-claims

* D-e: `thread.new-indirect` reads a real core funcref table with 0-based indices
  (`E.tableFunc?` on the core store): an out-of-bounds index or a null entry traps
  `threadNewIndirectNull`, a function whose type is not `E.ofFlatType ft` traps
  `threadNewIndirectType`. This intentionally does NOT match REF's 1-based Python `Table`
  (index 0 reserved) for `CoreFuncRef` tables. A dangling function address (no type in the
  core store) is a type mismatch.
* D-f: REF asserts are preconditions, not checked: `ft` is `(func (param i32))` or
  `(func (param i64))` (validation), `new_thread.suspended()` (the `newThread` effect creates a
  suspended thread), `current_thread() is not other_thread` in `resume-later` and
  `*-then-resume` (a running thread is not suspended, so the preceding trap excludes it under
  the machine invariant), and `thread.index is not None` in `thread.index` (a running guest
  thread is registered; a missing index is an `internal` trap here).
* The `thread_func` of `thread.new-indirect` (`call_and_trap_on_throw(f.callee, [c])` then
  `task.unregister_thread(new_thread)`) is the defunctionalized `ThreadBody.newIndirect task f c`,
  run by the dispatcher when the thread is first resumed.
* `hr : HostReady σ` (host readiness) and `q : Quirks` (the `Quirks.promoteYieldOnly` branch)
  are passed through to `Thread.suspendThenPromote`/`Thread.yieldThenPromote`.
* Not modelled here: the dispatch of the core call and any test (the built-ins are
  tested end to end in `Examples/Threads.lean` and `Tests/Threads.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon.Builtins

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-- The current thread with its record and task record, after REF
`trap_if(not thread.task.inst.may_leave)`. -/
def enterThreadBuiltin : P E σ (ThreadId × Runtime.Thread × Task E) := do
  let t ← currentThreadId
  let th ← getThread t
  let tk ← getTask th.task
  trapIf (!(← getInst tk.inst).mayLeave) .cannotLeave
  return (t, th, tk)

/-- REF `trap_if(not other_thread.suspended())`, reason `cannotResumeThread`. -/
def trapUnlessSuspended (o : ThreadId) : P E σ Unit := do
  trapIf (!(← getStore).threadIs Runtime.Thread.suspended o) .cannotResumeThread

/-- REF `canon_thread_index()` (L2565-2569): `trap_if(not thread.task.inst.may_leave)`; return
`[thread.index]`. Precondition (REF assert): the current thread is registered. -/
def threadIndex : P E σ (List FlatValue) := do
  let (_, th, _) ← enterThreadBuiltin
  let i ← orTrap (.internal "thread.index: current thread has no index") th.index
  return [i32Flat i]

/-- REF `canon_thread_new_indirect(ft, ftbl, fi, c)` (L2578-2591): `task = current_task()`;
`trap_if(not task.inst.may_leave)`; `f = ftbl.get(fi)` on the core table `tbl` (D-e: out of
bounds or null traps `threadNewIndirectNull`); `trap_if(f.t != ft)` (`threadNewIndirectType`);
create the suspended thread running `ThreadBody.newIndirect task f c`; `register_thread` in
`task` (may trap `tableFull`); return `[new_thread.index]`.
Precondition (REF assert): `ft` is `(func (param i32))` or `(func (param i64))`. -/
def threadNewIndirect (tbl : E.TableAddr) (ft : V1.FuncType) (fi : Nat) (c : FlatValue) :
    P E σ (List FlatValue) := do
  let task ← currentTask
  let tk ← getTask task
  trapIf (!(← getInst tk.inst).mayLeave) .cannotLeave
  let s ← getStore
  let f ← orTrap .threadNewIndirectNull ((E.tableFunc? s.core tbl fi).join)
  trapIf (E.funcType? s.core f != some (E.ofFlatType ft)) .threadNewIndirectType
  let nt ← newThread (.newIndirect task f c)
  let i ← Runtime.Task.registerThread task nt
  return [i32Flat i]

/-- REF `canon_thread_resume_later(i)` (L2594-2601): `inst = current_instance()`;
`trap_if(not inst.may_leave)`; `other_thread = inst.threads.get(i)`;
`trap_if(not other_thread.suspended())`; `other_thread.resume_later()`; return `[]`.
Precondition (REF assert): `other_thread` is not the current thread. -/
def threadResumeLater (i : Nat) : P E σ (List FlatValue) := do
  let inst ← currentInst
  trapIf (!(← getInst inst).mayLeave) .cannotLeave
  let o ← threadsGet inst i
  trapUnlessSuspended o
  Runtime.Thread.resumeLater o
  return []

/-- REF `canon_thread_suspend()` (L2605-2609): `trap_if(not thread.task.inst.may_leave)`;
`thread.suspend()`; return `[0]`. -/
def threadSuspend : P E σ (List FlatValue) := do
  let _ ← enterThreadBuiltin
  Runtime.Thread.suspend
  return [i32Flat 0]

/-- REF `canon_thread_yield()` (L2613-2617): `trap_if(not thread.task.inst.may_leave)`;
`thread.yield_()` (C1 at site K9); return `[0]`. -/
def threadYield : P E σ (List FlatValue) := do
  let _ ← enterThreadBuiltin
  Runtime.Thread.yield_
  return [i32Flat 0]

/-- REF `canon_thread_suspend_then_resume(i)` (L2621-2628):
`trap_if(not thread.task.inst.may_leave)`; `other_thread = thread.task.inst.threads.get(i)`;
`trap_if(not other_thread.suspended())`; `thread.suspend_then_resume(other_thread)`; return
`[0]`. Precondition (REF assert): `other_thread` is not the current thread. -/
def threadSuspendThenResume (i : Nat) : P E σ (List FlatValue) := do
  let (_, _, tk) ← enterThreadBuiltin
  let o ← threadsGet tk.inst i
  trapUnlessSuspended o
  Runtime.Thread.suspendThenResume o
  return [i32Flat 0]

/-- REF `canon_thread_yield_then_resume(i)` (L2632-2639): as `threadSuspendThenResume` with
`thread.yield_then_resume(other_thread)`. -/
def threadYieldThenResume (i : Nat) : P E σ (List FlatValue) := do
  let (_, _, tk) ← enterThreadBuiltin
  let o ← threadsGet tk.inst i
  trapUnlessSuspended o
  Runtime.Thread.yieldThenResume o
  return [i32Flat 0]

/-- REF `canon_thread_suspend_then_promote(i)` (L2643-2649):
`trap_if(not thread.task.inst.may_leave)`; `trap_if(i == thread.index)` (`cannotResumeThread`);
`other_thread = thread.task.inst.threads.get(i)`; `thread.suspend_then_promote(other_thread)`;
return `[0]`. `q.promoteYieldOnly` selects the wasmtime promotability test. -/
def threadSuspendThenPromote (hr : HostReady σ) (q : Quirks) (i : Nat) :
    P E σ (List FlatValue) := do
  let (_, th, tk) ← enterThreadBuiltin
  trapIf (th.index == some i) .cannotResumeThread
  let o ← threadsGet tk.inst i
  Runtime.Thread.suspendThenPromote hr q o
  return [i32Flat 0]

/-- REF `canon_thread_yield_then_promote(i)` (L2653-2659): as `threadSuspendThenPromote` with
`thread.yield_then_promote(other_thread)`. -/
def threadYieldThenPromote (hr : HostReady σ) (q : Quirks) (i : Nat) :
    P E σ (List FlatValue) := do
  let (_, th, tk) ← enterThreadBuiltin
  trapIf (th.index == some i) .cannotResumeThread
  let o ← threadsGet tk.inst i
  Runtime.Thread.yieldThenPromote hr q o
  return [i32Flat 0]

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon.Builtins
