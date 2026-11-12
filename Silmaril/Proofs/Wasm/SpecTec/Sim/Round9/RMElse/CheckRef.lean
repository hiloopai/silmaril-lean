module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.Defs

/-!
# Round 9, rm: the kernel checks on `Ref_ok` and the pairs left

* `refOkOk_fixed`: `Ref_ok` has no parameters and every rule is `refOkRule`;
* `sfPairsOk_fixed`: at the 4 pairs of `leftPairsC` the `otherwise` rule reads the state as
  `(s; f)` with `s` a store quantifier (`lhsSF`) and the earlier rule is `sfRule`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

set_option maxRecDepth 100000 in
theorem refOkOk_fixed :
    refOkOk (Silmaril.SpecTec.Sem.relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sfPairsOk_fixed : sfPairsOk (Round8.FiresC.rulesOf "Step_read") leftPairsC = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
