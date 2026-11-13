module

public import Silmaril.Wasm.Component.Async.CabiOracle3.Defs
meta import Silmaril.Wasm.Component.Async.CabiOracle3.Defs

@[expose] public section

/-!
# The `run_tests.py` stream scripts with host pumps pass, in the kernel

Each test of `Silmaril.Wasm.Component.Async.CabiOracle3` (component-model `d095e2f`) runs to the
end with every assertion of the Python test holding, checked by kernel evaluation (`decide`)
and by the compiled evaluator (`#guard`).
-/

namespace Silmaril.Wasm.Component.Async.Cabi.Oracle

/-- `test_transfer_readable_end`. -/
theorem transferReadableEnd_passes : runScript 1 transferReadableEnd = none := by decide

/-- `test_eager_stream_completion`. -/
theorem eagerStreamCompletion_passes : runScript 1 eagerStreamCompletion = none := by decide

/-- `test_async_stream_ops`. -/
theorem asyncStreamOps_passes : runScript 1 asyncStreamOps = none := by decide +kernel

#guard all3.all fun (_, n, cs) => runScript n cs == none

end Silmaril.Wasm.Component.Async.Cabi.Oracle
