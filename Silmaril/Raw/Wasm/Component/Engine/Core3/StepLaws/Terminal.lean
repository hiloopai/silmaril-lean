module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Terminal.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs

/-!
# Terminal codes take no interpreter step

The interpreter step `SingleThreaded.Exec.stepI o` is `none` on the codes that
`SingleThreaded.statusC` reports as `returned`, without any typing hypothesis:

* a value sequence (`stepI_of_splitVals_isEmpty`, `stepI_vals`): the driver `step?` has no
  instruction to reduce (`step?_nil`);
* a lone `trap` (`stepI_trap`): the driver's trap branch (`Drv.layer`) only bubbles a `trap`
  that has values or instructions around it;
* an uncaught exception `throwing a` (`stepI_throwing`): the driver's `throw_ref` branch only
  bubbles a thrown exception that has values or instructions around it.

These are the untyped analogues of `returned_no_internal` (SingleThreaded/Agreement.lean).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem stepI_vals {o : SingleThreaded.GrowOracle} {c : Config H} {vs : List Val}
    (h : c.code = vals vs) : SingleThreaded.Exec.stepI o c = none := by
  apply stepI_of_splitVals_isEmpty
  rw [h, SingleThreaded.splitVals_vals]
  rfl

end Silmaril.Wasm.Component.Engine.Core3
