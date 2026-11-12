module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs

/-!
# Round 9, `otherwise` rules: the kernel check of the pairs with `throw_ref-instrs`

`adjPairs_fixed` (`decide +kernel`): in the fixed wasm-3.0 script, the pairs of `elsePairs` whose
rules satisfy `adjDiffer` are `adjPairs`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The pairs with `throw_ref-instrs` in the fixed script.** -/
theorem adjPairs_fixed : adjPairsIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed)
    adjPairs = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
