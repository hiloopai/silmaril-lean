module

public import Silmaril.Wasm.Component.Reference.Wasm.Semantics.Defs

public import Silmaril.Raw.Wasm.Component.Wasm.Semantics.Memory
public import Silmaril.Wasm.Component.Engine.Laws

/-!
# `WasmSemantics`: the core-level interface, with `CoreEngine` as a derived view

This is the interface of issue #846 (`WasmInterp`), in the shape issue #878 needs: one
core-level description of a WebAssembly semantics from which the component model's
`Component.Engine.CoreEngine` is **derived by a single adapter**, rather than a second,
parallel interface.

## Why not #846's five-field sketch

#846 proposes

```
structure WasmInterp where
  Module : Type ; Valid : Module → Prop ; Input : Type ; Behaviour : Type
  sem : Module → Input → Behaviour → Prop
```

That is a *behavioural* view: it says what a whole run of a whole module looks like. The
component model needs strictly more, because a component instance is not a closed program: the
canonical ABI reads and writes the instance's linear memory between calls, resolves funcrefs
out of its tables, allocates one host function per lowering site, and suspends an activation at
a host callout to let the component scheduler interleave it with others. None of that is
expressible as a predicate on `Module × Input × Behaviour`.

`WasmSemantics` is therefore the *configuration-level* interface -- modules and validity, a
host-indexed store, addresses, instantiation, invocation, a host-free step relation and an
observable status -- and #846's behavioural view is recovered from it as a definition
(`Silmaril/Wasm/Semantics/Interp.lean`), not assumed as a second primitive.

## Structure, not class

`WasmSemantics` is a `structure`, following `CoreEngine`. A semantics is a *value*, not a
canonical choice per type: `v2 o` and `v2Det o` are two semantics over the very same carriers,
as are `core3 o` and `core3Spec o`, so typeclass resolution has nothing to dispatch on. The
laws, by contrast, are a `class` on that value (`WasmSemantics.Lawful`, in
`Silmaril/Wasm/Semantics/Laws.lean`), exactly as `CoreEngine.Lawful` is.

## What is factored out

The one genuine sublanguage shared by every engine is linear memory: `MemoryView`
(`Silmaril/Wasm/Semantics/Memory.lean`) replaces the four byte-level accessors by a lookup/update
pair, and discharges eight of `CoreEngine.Lawful`'s twenty-three fields from four pointwise
coherence facts. Everything else `CoreEngine` asks for is genuinely semantics-level and is kept
here.

Not here: store extension and the laws (`Semantics/Laws.lean`), the behavioural view
(`Semantics/Interp.lean`), and any particular semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.Semantics

open Silmaril.Wasm.Component.Engine

namespace WasmSemantics

variable (S : WasmSemantics)

end WasmSemantics

end Silmaril.Wasm.Semantics
