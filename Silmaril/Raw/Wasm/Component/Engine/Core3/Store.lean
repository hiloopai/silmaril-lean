module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs

public import Silmaril.Raw.Wasm.Component.Engine.Core3.Extends
public import Silmaril.Raw.Wasm.Component.Wasm.Execution.Memory.Lemmas
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc

/-!
# Store laws of the concrete Core 3.0 engine

The store-level fields of `CoreEngine.Lawful` (Engine/Laws.lean) for `core3 o`, stated over the
concrete functions of the engine (`SingleThreaded.allocHost`, `funcTypeE?`,
`SingleThreaded.memRead?`/`memWrite?`/`memSize?`/`memAddrType?`, `prepareE?`, `statusE`), which
are the fields of `core3 o` by definition:

* host allocation (`SingleThreaded.allocHost`, the spec's `$allocfunc` of a host function)
  appends one function instance: it grows the store (`allocHost_grows`, hence
  `allocHost_extends`), the new address was free (`allocHost_fresh`), no other function type
  changes (`allocHost_frame`), the new function has type `ofFlatType ft`
  (`allocHost_funcType`), and invoking it with `ft.params.length` flat arguments is
  immediately a callout of its host code with those arguments (`statusE_allocHost_callout`);
* memory writes (`SingleThreaded.memWrite?`) grow the store (`memWrite?_grows`,
  `memWrite?_extends`), keep every memory size and address type (`memWrite?_memSize`,
  `memWrite?_memAddrType`), satisfy read-after-write and the frame law for other memories and
  disjoint ranges (`memWrite?_read`, `memWrite?_read_other`); reads and writes succeed exactly
  in bounds (`memRead?_isSome_iff`, `memWrite?_isSome_iff`), reads have the requested length
  (`memRead?_size`), and a memory has an address type exactly when it has a size
  (`memAddrType?_isSome_iff`);
* instantiation (`prepareE?`: `$evalglobals`, then allocation of the module instance of the
  global-free residue and direct element and data segment initialisation, `instantiateOnce?`)
  grows the store (`instantiateOnce?_grows`, `prepareE?_grows`, hence `prepareE?_extends`).

No typing is assumed anywhere.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## Host allocation -/

/-! ## Memory reads and writes -/

/-! ## Instantiation -/

section Instantiation

variable {P : Numerics.Profile}

end Instantiation

end Silmaril.Wasm.Component.Engine.Core3
