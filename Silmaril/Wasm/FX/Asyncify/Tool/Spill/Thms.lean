module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Spill.Bytes

/-!
# Operands live across calls: theorems

Proofs in `Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Spill.*` (Isar style); no `sorry`, no axiom beyond
Lean's.

* `spill_beh`: **the spill is correct**. For segmented functions passing their checks
  (`SegOk`: `chainOk` depths, temporaries below `2 ^ 32`), a call of a defined function of the
  segmented program `segEnv imps gs` and the same call of the spilled program `spEnv imps gs`
  have the same behaviours (results with the final host state, traps, divergence) for every
  deterministic host. Proved by a simulation on the frame machine (`isSimS`): the spilled program
  takes extra steps at every call site (store the operands, reload the arguments; after the call,
  store the results, reload the live operands and the results), never fewer.
* `segmentEnv_sound`: the reader of the segmented form returns segmented functions that flatten
  to the program and pass the checks.
* `asyncifyS_beh`: the pass on the segmented form (spill, then the statement-form pass with
  elided checks) has the behaviours of the module's machine program, for the spilled program `P`
  (its `DepthBound` is about `P`'s runs; their frames are the source's, not proved here).
* `asyncifyBytesW_correct`: **the tool on the wider fragment, on bytes** (`asyncifyBytesW`, the
  default of `wasm-asyncify`): statement form when the module is in it, else spilled; decoding
  and encoding sound for the binary grammar, the output read back as the asyncified program, and
  equal behaviours of every call.
-/
