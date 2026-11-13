module

public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Thread.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Task
public import Silmaril.Raw.Wasm.Component.Canon.Flat

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

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

/-! ## Examples -/

section Examples

/-- A small program: spawn a thread from table slot 0 with context `c`, then switch to it,
leaving the current thread suspended (REF Concurrency.md "Thread Built-ins"). -/
example (tbl : E.TableAddr) (c : FlatValue) : P E σ Unit := do
  match ← threadNewIndirect (σ := σ) tbl ⟨[.int .i32], []⟩ 0 c with
  | [v] => discard <| threadSuspendThenResume (E := E) (σ := σ) (flatNat v)
  | _ => pure ()

/-- `thread.suspend` returns `[0]` once resumed. -/
example : i32Flat 0 = .int .i32 0 := rfl

end Examples

end Silmaril.Wasm.Component.Canon.Builtins
