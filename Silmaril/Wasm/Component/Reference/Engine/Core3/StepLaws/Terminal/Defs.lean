module

public import Silmaril.Wasm.Component.Engine.Core3.Defs

/-!
# `Engine.Core3.StepLaws.Terminal`: the laws that definitions cite

The theorems of the component reference copy `Engine.Core3.StepLaws.Terminal` that definition parts
cite (engine records bundle such laws as fields). The other theorems stay in
`Silmaril.Raw.Wasm.Component.Engine.Core3.StepLaws.Terminal`, which imports this module.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core
variable {H : Type}

/-- No step when the code is all values. -/
theorem stepI_of_splitVals_isEmpty {o : SingleThreaded.GrowOracle} {c : Config H}
    (h : (SingleThreaded.splitVals c.code).2.isEmpty = true) :
    SingleThreaded.Exec.stepI o c = none :=
  SingleThreaded.Exec.step?_nil (vs := (SingleThreaded.splitVals c.code).1)
    (Prod.ext rfl (List.isEmpty_iff.mp h))

/-- No step on a lone `trap`. -/
theorem stepI_trap {o : SingleThreaded.GrowOracle} {c : Config H} (h : c.code = [.trap]) :
    SingleThreaded.Exec.stepI o c = none := by
  have hs : SingleThreaded.splitVals c.code = ([], [.trap]) := by rw [h]; rfl
  rw [SingleThreaded.Exec.stepI, SingleThreaded.Exec.step?_cons hs]
  rfl

/-- No step on an uncaught exception at the top of the code. -/
theorem stepI_throwing {o : SingleThreaded.GrowOracle} {c : Config H} {a : Nat}
    (h : c.code = throwing a) : SingleThreaded.Exec.stepI o c = none := by
  have hs : SingleThreaded.splitVals c.code = ([.ref (.exn a)], [.plain .throwRef]) := by
    rw [h]; rfl
  rw [SingleThreaded.Exec.stepI, SingleThreaded.Exec.step?_cons hs]
  rfl

end Silmaril.Wasm.Component.Engine.Core3
