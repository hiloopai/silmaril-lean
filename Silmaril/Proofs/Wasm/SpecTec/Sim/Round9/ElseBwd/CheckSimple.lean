module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs

/-!
# Round 9, `otherwise` rules: the kernel check of the simple pairs

`simplePairs_fixed` (`decide +kernel`): in the fixed wasm-3.0 script, the pairs of `elsePairs`
whose `otherwise` rule has a left-hand side `z; L` and whose earlier rule is simple are
`simplePairs`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The simple pairs of the fixed script.** -/
theorem simplePairs_fixed : simplePairsIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed)
    simplePairs = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
