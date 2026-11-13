module

public import Silmaril.Wasm.Component.Async.CabiOracle4.Defs
meta import Silmaril.Wasm.Component.Async.CabiOracle4.Defs

@[expose] public section

/-!
# `test_cancel_subtask` and `test_sync_threads` pass, in the kernel

The scripts of `Silmaril.Wasm.Component.Async.CabiOracle4` (component-model `d095e2f`) run to the
end with every assertion of the Python test holding, checked by kernel evaluation
(`decide +kernel`) and by the compiled evaluator (`#guard`).
-/

namespace Silmaril.Wasm.Component.Async.Cabi.Oracle

/-- `test_cancel_subtask`. -/
theorem cancelSubtask_passes : runScript 2 cancelSubtask = none := by decide +kernel

/-- `test_sync_threads`. -/
theorem syncThreads_passes : runScript 1 syncThreads = none := by decide +kernel

#guard all4.all fun (_, n, cs) => runScript n cs == none

end Silmaril.Wasm.Component.Async.Cabi.Oracle
