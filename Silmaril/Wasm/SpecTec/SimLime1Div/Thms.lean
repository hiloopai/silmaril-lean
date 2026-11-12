module

public import Silmaril.Proofs.Wasm.SpecTec.SimLime1Div.Diverge

/-!
# Lime1 divergence against the wasm-3.0 script

`Silmaril.Wasm.SpecTec.SimLime1` relates Lime1 steps and finite Lime1 runs to the wasm-3.0 script
(`compositeL1T`, `compositeL1_steps`). This topic adds divergence. In
`Silmaril.Proofs.Wasm.SpecTec.SimLime1Div`:

* **`divergeL1T`**: a diverging Lime1 configuration (`Lime1.Execution.Diverges`), simulated by a
  Core configuration `c` that only reaches good configurations (`Sim20.RunGood`), gives an
  infinite run (`InfiniteTrace`) of wasm-3.0 backend steps at Round 6's builtins `BI` from
  `configV hn c`. No hypothesis on the Lime1 side;
* `coreDiv_script`: the same from a diverging Core 3.0 configuration;
* `step_inv`: the invariant of the coinduction (`Inv`: `RunGood`, divergence and Round 6's
  `SimRel`) is kept by one Core step, with a non-empty backend run.

So all three Lime1 behaviours (values, traps and divergence) reach the 3.0 script through
Core 3.0, the first two by `compositeL1_steps` and `Lime1.Execution.Sim.result`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Proofs.Wasm.SpecTec.SimLime1Div.divergeL1T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.SpecTec.SimLime1Div.divergeL1T

/-- info: 'Silmaril.Proofs.Wasm.SpecTec.SimLime1Div.coreDiv_script' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.SpecTec.SimLime1Div.coreDiv_script
