module

public import Silmaril.Proofs.Wasm.FX.Logic.Generator.Run

/-!
# A one-shot generator in WasmFX: its result, by the WasmFX calculus

* `gen_main`: the consumer `mainBody` (`Silmaril.Wasm.FX.Logic.Generator.Defs`) can run to the
  result `[3]`: the generator yields `1`, the handler catches the yield, the rest of the
  generator is resumed and returns `2`, and the consumer adds them;
* **`gen_behaviour`**: `3` is a behaviour of `mainBody` under `StepFX'`, for every profile and
  every host relation.

The proof (`Silmaril.Proofs.Wasm.FX.Logic.Generator.Run`) uses only the rules of
`Silmaril.Wasm.FX.Logic.Thms` and its tactics (`fx_block`, `fx_resume`, `fx_call`, `fx_catch`,
`fx_exec`), not the reduction rules. It shows that the result is *a* behaviour (the calculus is
existential); that it is the *only* one is not proved here.

New statements.
-/
