module

public import Silmaril.Wasm.Component.Reference.Runtime.Options.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Options.Defs

public import Silmaril.Wasm.Component.Engine.Interface
public import Silmaril.Raw.Wasm.Component.Runtime.Ids
public import Silmaril.Raw.Wasm.Component.ABI.Calling
public import Silmaril.Raw.Wasm.Component.ABI.String

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

namespace CanonOpts

variable {E : CoreEngine}

theorem liftEqual_iff (a b : CanonOpts E) :
    a.liftEqual b = true ↔ a.encoding = b.encoding ∧ a.memory = b.memory := by
  simp [liftEqual]

theorem liftEqual_refl (a : CanonOpts E) : a.liftEqual a = true := by simp [liftEqual]

theorem liftEqual_comm (a b : CanonOpts E) : a.liftEqual b = b.liftEqual a := by
  simp only [liftEqual, eq_comm]

end CanonOpts

end Silmaril.Wasm.Component.Runtime
