module

public import Silmaril.Proofs.Wasm.Logic.OpenExamples.Link

/-!
# Worked example for open modules

Checked in every profile (proofs in `Silmaril/Proofs/Wasm/Logic/OpenExamples`):

* `incMod_sat`: the provider (`local.get 0; i32.const 1; i32.add`) meets
  `incSpec` ("returns `m + 1`, store unchanged") with no imports;
* `clientMod_sat`: the client (`local.get 0; call x`, where `x` is an import
  stub standing for the provider's address) meets `clientSpec` under the import
  specification `incSpec`, without any assumption on the import's code;
* `link_example`: the composition of their strategies refines
  `agStrat (ctxSpec ∅) (ctxSpec clientSpec)`.

Partial correctness. Each theorem is stated for any function instances, types and
bindings for which the indices resolve as assumed (the hypotheses); building
concrete modules and instantiating them is not done here.
-/
