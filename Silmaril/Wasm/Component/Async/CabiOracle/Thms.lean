module

public import Silmaril.Wasm.Component.Async.CabiOracle.Defs
meta import Silmaril.Wasm.Component.Async.CabiOracle.Defs

@[expose] public section

/-!
# The `run_tests.py` scripts pass, in the kernel

Each transcribed test of `run_tests.py` (component-model `d095e2f`) runs to the end with every
assertion of the Python test holding, checked by kernel evaluation (`decide`) and by the
compiled evaluator (`#guard`).
-/

namespace Silmaril.Wasm.Component.Async.Cabi.Oracle

/-- `test_stream_drop_both_ends_while_idle`. -/
theorem dropBothEndsWhileIdle_passes : runScript 1 dropBothEndsWhileIdle = none := by decide

/-- `test_future_drop_readable_with_pending_write`. -/
theorem futureDropReadableWithPendingWrite_passes :
    runScript 1 futureDropReadableWithPendingWrite = none := by decide

/-- `test_futures`. -/
theorem futures_passes : runScript 1 futures = none := by decide

/-- `test_host_partial_reads_writes`. -/
theorem hostPartialReadsWrites_passes : runScript 1 hostPartialReadsWrites = none := by decide

/-- `test_cancel_copy`. -/
theorem cancelCopy_passes : runScript 1 cancelCopy = none := by decide

/-- `test_async_callback`. -/
theorem asyncCallback_passes : runScript 2 asyncCallback = none := by decide

/-- `test_async_backpressure`. -/
theorem asyncBackpressure_passes : runScript 2 asyncBackpressure = none := by decide

#guard all.all fun (_, n, cs) => runScript n cs == none

end Silmaril.Wasm.Component.Async.Cabi.Oracle
