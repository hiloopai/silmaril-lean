module

/-!
# Runtime object identities

Arena identities for the component-model runtime store (`Runtime.CStore`) and
the machine. The Python reference (`design/mvp/canonical-abi/definitions.py` at
component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
refers to runtime objects by Python object identity; here every such object
lives in an append-only arena (`Runtime.Arena`) and is named by its index,
wrapped in a distinct structure per object kind so that ids of different kinds
cannot be confused:
`InstId`, `RtId`, `FuncId`, `TaskId`, `ThreadId`, `SubtaskId`, `HandleObjId`, `EndId`,
`WsetId`, `ErrCtxId`, `CallerId`, `CancelId`, `HostFuncId`, `HostBufId`, `CallId`.

These are *not* the per-instance handle-table indices that core wasm code sees
(those are `Nat` indices of `Runtime.Table`); a table slot stores one of these
ids. Nothing here is a specification of allocation: which fresh id an arena
returns is fixed by `Runtime.Arena.alloc` (its length).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

/-- A component instance (REF `ComponentInstance`). -/
structure InstId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A resource type (REF `ResourceType`). -/
structure RtId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A component-level function value (lifted function or host function). -/
structure FuncId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A task (REF `Task`). -/
structure TaskId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A thread (REF `Thread`); distinct from the per-instance thread table index. -/
structure ThreadId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A subtask (REF `Subtask`). -/
structure SubtaskId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A resource handle object (REF `ResourceHandle`). -/
structure HandleObjId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A stream or future end (REF `ReadableStreamEnd`/`WritableStreamEnd`/future ends). -/
structure EndId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A waitable set (REF `WaitableSet`). -/
structure WsetId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- An error context (REF `ErrorContext`). -/
structure ErrCtxId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A caller identity used for borrow scoping and reentrance checks. -/
structure CallerId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A host-side cancellation token (REF `on_cancel` / `OnResolve` callbacks). -/
structure CancelId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A host function of the embedding (choice point E1). -/
structure HostFuncId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A host-owned stream/future buffer (REF host `Buffer`s, choice point E1). -/
structure HostBufId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

/-- A pending late-bound call (resolved by `Canon.dispatch`). -/
structure CallId where
  /-- The underlying arena index. -/
  idx : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

end Silmaril.Wasm.Component.Runtime
