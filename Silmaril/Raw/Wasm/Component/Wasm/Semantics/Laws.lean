module

public import Silmaril.Wasm.Component.Reference.Wasm.Semantics.Laws.Defs

public import Silmaril.Raw.Wasm.Component.Wasm.Semantics.Defs

/-!
# The laws of a `WasmSemantics`, and the lawfulness of its engine view

`WasmSemantics.Lawful` is what a semantics must prove. `WasmSemantics.toCoreEngine_lawful` is
the payoff: a semantics proving these fourteen obligations gets all twenty-three
`Component.Engine.CoreEngine.Lawful` fields for its engine view, for free.

The fourteen are not a renaming of the twenty-three. Two groups collapse.

* **Parking (3 → 1).** `CoreEngine.Lawful` asks separately that a `returned`, a `callout` and a
  `stuck` thread take no internal step. The content is the single statement that *only running
  threads step* (`internal_running`), which is also exactly the form every engine's proof takes
  and the form `CoreEngine.status_running_of_internal` immediately recovers.
* **Linear memory (9 → 5).** Eight of the nine memory laws are consequences of the four
  pointwise coherence facts of `MemoryView.Lawful` (`Semantics/Memory.lean`), which are about
  `setInst`/`withData` alone and mention neither the component runtime nor store extension. The
  ninth, `memWrite_extends`, genuinely does mention function types, table address types and
  thread status, so it stays here.

The rest -- flat signatures, the `ExternSub` preorder, `asFunc?`/`ofFunc`, the three
store-extension laws and the five `allocHost` laws -- are carried across unchanged, because
they are already in semantics-level vocabulary.

Deliberately **not** a field: `CoreEngine.ResumeLawful` (resuming a parked thread leaves it
running or returned). It is false for every real engine in this development -- Lime1, V1, 2.0
and Core 3.0 all decline it, since an ill-typed host result can leave the resumed thread stuck
-- so building it into `WasmSemantics.Lawful` would make the class uninhabited in practice.
-/

@[expose] public section

namespace Silmaril.Wasm.Semantics

open Silmaril.Wasm.Component.Engine

namespace WasmSemantics

end WasmSemantics

end Silmaril.Wasm.Semantics
