module

public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.Equiv
public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.HeightCompose

/-!
# A big-step semantics for WebAssembly 1.0: theorems

The big-step semantics `BigStep` of Watt et al. (ECOOP 2019, Appendix A) and its
height-indexed form `BigStepN` (`Silmaril.Wasm.Logic.V1.BigStep.Defs`), against
silmaril-lean's V1 small-step semantics `Silmaril.Wasm.V1.Execution.Steps`:

* Theorem 1 of the paper, for terminating runs: `bigStep_normal_iff_steps` and
  `bigStep_trap_iff_steps` (proofs `BigStep.toSteps`, `BigStep.ofSteps_normal`,
  `BigStep.ofSteps_trap`);
* heights: `bigStep_iff_exists_height`, `BigStepN.mono`, `BigStep.toHeight`;
* the structural laws behind Wasm Logic's `[seq]` and `[extension]` rules:
  `BigStep.append`, `BigStep.append_inv`, `BigStep.weaken`, and their
  height-indexed forms `BigStepN.append`, `BigStepN.append_inv`, `BigStepN.weaken`.
-/