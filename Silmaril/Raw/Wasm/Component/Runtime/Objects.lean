module

public import Silmaril.Wasm.Component.Reference.Runtime.Objects.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Builtin
public import Silmaril.Raw.Wasm.Component.Runtime.Table
public import Silmaril.Raw.Wasm.Component.Value.Basic
public import Silmaril.Raw.Wasm.Component.Async.Codes

/-!
# Runtime objects of the component store

Every REF runtime class of `design/mvp/canonical-abi/definitions.py` at component-model
`a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
transcribed as PLAIN DATA: no functions, no programs. Object
references are arena ids (`Runtime/Ids.lean`); the objects live in the arenas of
`Runtime.CStore` (`Runtime/Store.lean`). Python closures stored in objects are
defunctionalized into data:

| Lean | REF (line) | defunctionalized closures |
| --- | --- | --- |
| `ResourceType` | `ResourceType` (L703) | `dtor` is a core function address |
| `ResourceHandle` | `ResourceHandle` (L689) | |
| `PendingEvent` | `Waitable.pending_event` (L724) | `subtask_event`, `*_event` of `notify` |
| `WaitableCommon`, `Waitable` | `Waitable` (L724) | |
| `WaitableSet` | `WaitableSet` (L766) | |
| `Subtask` | `Subtask` (L816) | `on_cancel` is a `CancelRef` |
| `Task` | `Task` (L392) | `on_start`/`on_resolve` are a `Caller` record (by id) |
| `Thread`, `ThreadStatus` | `Thread` (L279) | `ready_func` is a `ReadyCond`; no `cont` |
| `End`, `BufferDesc` | `End` (L931), `GuestBuffer` (L887), host buffers of `run_tests.py` | |
| `ErrorContext` | `ErrorContext` (L2664) | |
| `HandleEntry` | elements of `ComponentInstance.handles` (L190) | |
| `InstState` | `ComponentInstance` (L190) | `store` is implicit |
| `CFuncInst` | `FuncInst` (L385-389) produced by `Store.lift` or supplied by the host | |
| `Caller`, `SubKind` | `(on_start, on_resolve)` pairs (see `Caller`) | |
| `CancelRef` | `OnCancel` (L385-389) | |
| `WaitSite` | the `block()` sites K1-K13 (listed at `WaitSite`) | |

The Async/Codes enumerations `SubtaskState`, `TaskState`, `EndState`, `EndKind` are reused.

Not modelled or claimed here: any behaviour (methods are canon programs in `Runtime/` and
`Canon/`), the evaluation of `ReadyCond` (`Runtime/Thread.lean`), invariants relating objects, and
REF's `Thread.cont` (the machine keeps continuations). -/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine AsyncRef

/-! ## Resources -/

/-! ## Waitables -/

/-! ## Threads and readiness -/

theorem WaitSite.mem_all (k : WaitSite) : k ∈ WaitSite.all := by cases k <;> decide

theorem WaitSite.all_toNat : WaitSite.all.map WaitSite.toNat = List.range' 1 13 := by decide

/-! ## Streams and futures -/

namespace BufferDesc

variable {E : CoreEngine}

end BufferDesc

/-! ## Tasks, callers and instances -/

example : ({ task := ⟨0⟩ } : Thread).storage = [0, 0] := rfl
example : ({ task := ⟨0⟩ } : Thread).status = .blocked ∧
    ({ task := ⟨0⟩ } : Thread).readyCond = none := ⟨rfl, rfl⟩
example : ({} : InstState).mayLeave = true := rfl

end Silmaril.Wasm.Component.Runtime
