module

public import Silmaril.Proofs.Wasm.Logic.Strategy.Comp

/-!
# Specifications as strategies: composition

* `agStrat_comp` (`Silmaril.Proofs.Wasm.Logic.Strategy.Comp`): the composition of the
  assume/guarantee strategies for `I ↠ M` and `M ↠ S` refines the one for `I ↠ S`;
* `comp_refines`: components that refine their specification strategies compose
  (with `Silmaril.Games.Strategy.comp_mono`) to one that refines the composed
  specification strategy.

The instance for Wasm modules (the strategy of an open module, the proof that it
refines the assume/guarantee strategy of its import and export specifications,
and linking) is `Silmaril.Wasm.Logic.Open`.

A Silmaril addition.
-/
