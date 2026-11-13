module

public import Silmaril.Wasm.Component.Reference.Wasm.Semantics.Memory.Defs

public import Silmaril.Raw.Wasm.Component.Wasm.Execution.Memory.Lemmas
public import Silmaril.Wasm.Types

/-!
# The memory view of a Wasm semantics

Every WebAssembly semantics in this development (V1, Lime1, 2.0, Core 3.0, the mock engine)
stores its linear memories the same way: the store holds a list of memory instances, each of
which wraps a `Silmaril.Wasm.Execution.Memory.Bytes` buffer together with bookkeeping (a
maximum, an address type). The byte-level accessors the component runtime needs
(`memAddrType?`, `memSize?`, `memRead?`, `memWrite?`) are then the *same four expressions* in
every engine, and so are their laws -- which are currently proved four times over
(`Engine/Lime1/Properties.lean`, `Engine/V2/Properties.lean`, `Engine/Core3/Store.lean`,
`Engine/Mock.lean`).

A `MemoryView Store` factors that repetition. It is the minimal data a semantics must supply:

* a memory address type and a memory-instance type;
* a partial lookup `inst?` of an instance in a store, and an update `setInst`;
* the byte buffer `data` of an instance, a functional update `withData`, and the instance's
  address type.

The four accessors are *derived* (`addrType?`, `size?`, `read?`, `write?`), and
`MemoryView.Lawful` asks only for four pointwise coherence facts -- read-back and frame for
`setInst`, and read-back and address-type preservation for `withData`. From those,
`Silmaril/Wasm/Semantics/Defs.lean` derives eight of the twenty-three
`Component.Engine.CoreEngine.Lawful` fields.

Deliberately not here: store extension, which mentions function types and thread status and so
cannot be stated at this level (see `WasmSemantics.Lawful.memWrite_frame`), and memory growth,
which the component runtime never performs.
-/

@[expose] public section

namespace Silmaril.Wasm.Semantics

open Silmaril.Wasm.Execution

namespace MemoryView

variable {Store : Type → Type} (V : MemoryView Store)

variable {V}

section Lawful

variable [L : V.Lawful]

end Lawful

end MemoryView

end Silmaril.Wasm.Semantics
