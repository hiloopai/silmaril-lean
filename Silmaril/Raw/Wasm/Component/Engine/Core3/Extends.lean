module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Extends.Defs

public import Silmaril.Wasm.Component.Engine.Core3.Defs
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Grows

/-!
# The flat status view and store extension of the concrete Core 3.0 engine

* `flatStatus` is the flat view of a single-threaded status: values are converted to flat
  values (`SingleThreaded.toFlat?`), and a result or a callout whose values are not all numeric
  is `stuck`. The status of `core3 o` is the flat view of the computable status
  `statusC (stepI o)` (`statusE_eq_flatStatus`).
* `flatStatus_running_iff`, `flatStatus_eq_callout`: only `running` is `running`, and a flat
  callout comes from a callout.
* `Grows.extends`: untyped store growth (`Grows`, Engine/Core3/Grows.lean) is store extension
  of the concrete engine (`CoreEngine.Extends`, Engine/Laws.lean).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## The flat status view -/

/-! ## Growth is store extension -/

end Silmaril.Wasm.Component.Engine.Core3
