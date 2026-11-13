module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Defs

public import Silmaril.Raw.Wasm.Component.Engine.Core3.Extends
public import Silmaril.Raw.Wasm.Component.Engine.Core3.StepLaws.Terminal
public import Silmaril.Raw.Wasm.Component.Engine.Core3.StepLaws.Callout
public import Silmaril.Raw.Wasm.Component.Engine.Core3.StepLaws.Grows

/-!
# Parked threads of the concrete Core 3.0 engine take no step

The status of `core3 o` is the flat view of `SingleThreaded.statusC (stepI o)`
(`statusE_eq_flatStatus`). Every status other than `running` means that the interpreter has
no step at the thread's configuration (`stepI_none_of_statusC_ne_running`), without any typing:
`returned` codes are values, a lone `trap` or an uncaught exception
(StepLaws/Terminal.lean), a `callout` is a host-call redex (StepLaws/Callout.lean), and
`stuck` means `stepI` is `none` by definition. Hence the internal step of `core3 o` is `none`
on every non-`running` thread (`statusE_not_running_no_step`), which gives the
`returned_no_step`, `callout_no_step` and `stuck_no_step` laws of `CoreEngine.Lawful`
(`statusE_returned_no_step`, `statusE_callout_no_step`, `statusE_stuck_no_step`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core

variable {H : Type}

end Silmaril.Wasm.Component.Engine.Core3
