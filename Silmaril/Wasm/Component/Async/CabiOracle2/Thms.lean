module

public import Silmaril.Wasm.Component.Async.CabiOracle2.Defs
meta import Silmaril.Wasm.Component.Async.CabiOracle2.Defs

@[expose] public section

/-!
# More `run_tests.py` scripts pass, in the kernel

Each test of `Silmaril.Wasm.Component.Async.CabiOracle2` (component-model `d095e2f`) runs to the
end with every assertion of the Python test holding, checked by kernel evaluation (`decide`)
and by the compiled evaluator (`#guard`).
-/

namespace Silmaril.Wasm.Component.Async.Cabi.Oracle

/-- `test_async_to_async`. -/
theorem asyncToAsync_passes : runScript 2 asyncToAsync = none := by decide

/-- `test_sync_using_wait`. -/
theorem syncUsingWait_passes : runScript 2 syncUsingWait = none := by decide

/-- `test_async_to_sync`. -/
theorem asyncToSync_passes : runScript 2 asyncToSync = none := by decide

/-- `test_callback_interleaving`. -/
theorem callbackInterleaving_passes : runScript 2 callbackInterleaving = none := by
  decide +kernel

/-- `test_sync_ignores_backpressure`. -/
theorem syncIgnoresBackpressure_passes : runScript 2 syncIgnoresBackpressure = none := by decide

/-- `test_forward`. -/
theorem forward_passes : runScript 1 forward = none := by decide

/-- `test_receive_own_stream`. -/
theorem receiveOwnStream_passes : runScript 1 receiveOwnStream = none := by decide

/-- `test_self_copy(None)`, `test_self_copy(U8Type())`, `test_self_copy(F64Type())`. -/
theorem selfCopy_passes :
    runScript 1 (selfCopy tnone) = none ∧ runScript 1 (selfCopy u8) = none ∧
      runScript 1 (selfCopy f64) = none := by decide

/-- `test_wasm_to_wasm_stream`. -/
theorem wasmToWasmStream_passes : runScript 2 wasmToWasmStream = none := by decide

/-- `test_wasm_to_wasm_stream_empty`. -/
theorem wasmToWasmStreamEmpty_passes : runScript 2 wasmToWasmStreamEmpty = none := by decide

/-- `test_async_flat_params`. -/
theorem asyncFlatParams_passes : runScript 1 asyncFlatParams = none := by decide

/-- `test_threads`. -/
theorem threads_passes : runScript 1 threads = none := by decide

#guard all2.all fun (_, n, cs) => runScript n cs == none

end Silmaril.Wasm.Component.Async.Cabi.Oracle
