module

public import Silmaril.Proofs.Wasm.SpecTec.SimLime1Div20.Diverge

/-!
# Lime1 divergence against the wasm-2.0 script, and 1.0 divergence against both

`Silmaril.Wasm.SpecTec.SimLime1Div` takes Lime1 divergence to the wasm-3.0 script, with no
hypothesis. This topic adds, in `Silmaril.Proofs.Wasm.SpecTec.SimLime1Div20`:

* **`divergeL1_20`**: a diverging Lime1 configuration, simulated by a 2.0 configuration that only
  reaches good configurations (`Sim10.RunGood20`), gives an infinite run of the corrected
  wasm-2.0 script's backend steps (`SStepB (Sim20.StepFix.simEnv20S B)`), **conditional on the
  2.0 forward obligation `Sim10.Fwd20`**, the same hypothesis as `SimLime1.compositeL1`;
* **`divergeV1T`**: a diverging 1.0 configuration whose Lime1 image is simulated by a Core
  configuration that only reaches good configurations gives an infinite run of wasm-3.0 backend
  steps. No hypothesis on the 1.0 side: the copied lock-step `V1.Execution.Diverges.toLime`,
  then `SimLime1Div.divergeL1T`;
* `divergeV1_20`: the same into the 2.0 script, conditional on `Sim10.Fwd20`;
* `infinite_of_transGen`: the generic coinduction (non-empty runs between images give an
  infinite run).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Proofs.Wasm.SpecTec.SimLime1Div20.divergeL1_20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.SpecTec.SimLime1Div20.divergeL1_20

/-- info: 'Silmaril.Proofs.Wasm.SpecTec.SimLime1Div20.divergeV1T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.SpecTec.SimLime1Div20.divergeV1T

/-- info: 'Silmaril.Proofs.Wasm.SpecTec.SimLime1Div20.divergeV1_20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.SpecTec.SimLime1Div20.divergeV1_20
