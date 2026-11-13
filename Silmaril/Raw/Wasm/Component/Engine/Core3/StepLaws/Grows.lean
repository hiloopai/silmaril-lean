module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Grows.Defs

public import Silmaril.Wasm.Component.Engine.Core3.Defs
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Grows

/-!
# Interpreter steps grow the store

Without any typing hypothesis, every step of the computable interpreter grows the store
(`Grows`, Engine/Core3/Grows.lean):

* `interpHead_grows`: the head step `SingleThreaded.Exec.interpHead o`. For the families whose
  head-step soundness lemmas need no `StoreOk`, through those lemmas and `Det.Head.grows`;
  directly for the reference family (which keeps the store) and the control family (which
  changes it only by allocating an exception at `throw`, `Store.addExn`, `Grows.addExn`);
* `stepI_grows`: the interpreter step `stepI o = step? (interpHead o)`, by well-founded
  induction on the driver (`step?_cons`, `Drv.layer`): the trap and `throw_ref` bubbling
  branches keep the store, the head branch is `interpHead_grows`, and the `label`, `handler`
  and `frame` branches are the induction hypothesis;
* `internal_grows`: an internal step of the concrete engine, `internalC (stepI o)`.

With `Grows.extends` this is the `internal_extends` law of `CoreEngine.Lawful`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core

variable {H : Type}

namespace StepLaws

/-! ## The reference and control families -/

end StepLaws

namespace StepLaws

/-! ## The driver -/

end StepLaws

end Silmaril.Wasm.Component.Engine.Core3
