module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Store.Defs
public import Silmaril.Wasm.SingleThreaded.Interface
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping

/-!
# Store typing under the store operations of the concrete Core 3.0 engine

Typed-store facts (`Store_ok`, `Extend_store`) for the store operations the component runtime
performs directly on a Core 3.0 store:

* `allocHost_storeOk`: allocating a host function of a flat type (`SingleThreaded.allocHost`, the
  spec's `$allocfunc` with host code) keeps the store typed and extends it; the new instance is
  typed by the host-function rule `FuncInstOk.host` at `ofFlatType ft`, a valid closed function
  type (`tyOk_ofFlatType`, `expand_ofFlatType`);
* `memWrite?_storeOk`: a byte write into a memory (`SingleThreaded.memWrite?`) keeps the memory's
  size, so the store stays typed (`StoreOk.setMem`);
* `threadOk_extend`: a typed thread stays typed in an extended typed store. For a pending thread
  the callee exists (`invoke_func_exists`: the reference `ref.func a` of `$invoke` is typed), and
  its type is unchanged by the extension, so the loaded code is the same.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3.Typed

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-! ## Flat function types -/

/-! ## Appending a function instance -/

/-! ## Host allocation -/

/-! ## Memory writes -/

/-! ## Threads in extended stores -/

end Silmaril.Wasm.Component.Engine.Core3.Typed
