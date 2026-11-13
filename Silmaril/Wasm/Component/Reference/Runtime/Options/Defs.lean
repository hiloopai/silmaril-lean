module

public import Silmaril.Wasm.Component.Engine.Interface
public import Silmaril.Wasm.Component.Reference.Runtime.Ids.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Calling.Defs
public import Silmaril.Wasm.Component.Reference.ABI.String.Defs

/-!
# Canonical options and lift/lower contexts

Plain-data transcription of the REF option records and of `LiftLowerContext`
(`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>):

* `CanonOpts E` is REF `CanonicalOptions` (L608), which extends `LiftLowerOptions` (+`realloc`)
  and `LiftOptions` (L595: `string_encoding`, `memory`). Core entities are engine addresses:
  `memory : Option E.MemAddr`, `realloc`/`postReturn`/`callback : Option E.FuncAddr`. The REF
  subclass chain is not reproduced: every runtime record stores the full `CanonOpts`, and the
  fields a smaller REF class lacks are simply unused (`task.return`'s `LiftOptions` are a
  `CanonOpts` whose extra fields are defaults).
* `CanonOpts.liftEqual` is REF `LiftOptions.equal` (L599-601): equal string encodings and the
  same memory *instance* (Python `is`), i.e. equal memory addresses, including both absent.
* `BorrowScope` is the REF `borrow_scope : Optional[Task|Subtask]` field of `LiftLowerContext`
  (L615-623), as an id.
* `LiftLowerContext E` is REF `LiftLowerContext` without its methods (`reallocate`/`allocate`,
  L625-646, are canon programs in `Canon/Context.lean` and `Canon/Lift.lean`; their pending
  on_start/on_resolve closures are `Runtime.Caller.sub (.realloc ..)` records, see
  `Runtime/Objects.lean`).
* `CanonOpts.ptrType` is the pointer width `cx.opts.memory.ptr_type()` given the address type of
  each memory (an argument, since the address type lives in the core store). Deviation D-g:
  without a `memory` option the width defaults to `.i32` (REF would raise; validation makes this
  unreachable wherever a pointer is used).

Not modelled here: option validation (Validation items), and any behaviour.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine

/-- REF `CanonicalOptions` (L608-613) with its superclasses `LiftLowerOptions` and
`LiftOptions` (L595-606) flattened into one record. -/
structure CanonOpts (E : CoreEngine) where
  /-- REF `string_encoding` (default `'utf8'`). -/
  encoding : ABI.StringEncoding := .utf8
  /-- REF `memory` (an engine memory address). -/
  memory : Option E.MemAddr := none
  /-- REF `realloc`. -/
  realloc : Option E.FuncAddr := none
  /-- REF `post_return`. -/
  postReturn : Option E.FuncAddr := none
  /-- REF `async_`. -/
  async_ : Bool := false
  /-- REF `callback`. -/
  callback : Option E.FuncAddr := none
  deriving DecidableEq

namespace CanonOpts

variable {E : CoreEngine}

/-- The default options (`CanonicalOptions()`): utf8 and nothing else. -/
def default : CanonOpts E := {}

instance : Inhabited (CanonOpts E) := ⟨default⟩

/-- REF `LiftOptions.equal` (L599-601): same string encoding and the same memory address
(both absent counts as equal). -/
def liftEqual (a b : CanonOpts E) : Bool :=
  decide (a.encoding = b.encoding) && decide (a.memory = b.memory)

/-- The pointer width `opts.memory.ptr_type()`, given the address type of every memory.
Deviation D-g: `.i32` when no memory is present. -/
def ptrType (memAddr : E.MemAddr → AddrType) (o : CanonOpts E) : AddrType :=
  match o.memory with
  | some m => memAddr m
  | none => .i32

/-- The static flattening options (`ABI.Options`) selected by these canonical options. -/
def abiOptions (memAddr : E.MemAddr → AddrType) (o : CanonOpts E) : ABI.Options :=
  { memory := o.ptrType memAddr, async_ := o.async_, callback := o.callback.isSome }

end CanonOpts

/-- REF `LiftLowerContext.borrow_scope : Optional[Task|Subtask]` (L618): the task (lift side)
or subtask (lower side) that borrows are scoped to, or none (e.g. stream/future buffers). -/
inductive BorrowScope where
  | task (t : TaskId)
  | subtask (s : SubtaskId)
  | none
  deriving DecidableEq, Repr, Inhabited

/-- REF `LiftLowerContext` (L615-623) as plain data: the options, the component instance and
the borrow scope. -/
structure LiftLowerContext (E : CoreEngine) where
  /-- REF `opts`. -/
  opts : CanonOpts E
  /-- REF `inst`. -/
  inst : InstId
  /-- REF `borrow_scope` (default none). -/
  scope : BorrowScope := .none
  deriving DecidableEq

end Silmaril.Wasm.Component.Runtime
