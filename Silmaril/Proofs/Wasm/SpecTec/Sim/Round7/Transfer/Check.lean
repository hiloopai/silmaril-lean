module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Transfer.Defs

/-!
# Round 7: the rules `Step` reaches are harmless, conclusion alternatives included

One kernel computation (`decide +kernel`, kernel reduction, no native code) over the fixed wasm-3.0 script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Transfer

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **Every relation `Step` reaches has no parameters and harmless rules.** -/
theorem relRulesOk_fixed : relRulesOk (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.Transfer
