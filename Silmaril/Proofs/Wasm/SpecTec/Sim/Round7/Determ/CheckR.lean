module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Defs

/-!
# Round 7, determination: the mode check on the script

One kernel computation (`decide +kernel`, kernel reduction, no native code): every rule of every relation that
SpecTec's `Step` reaches passes `Round7.Determ.ruleDetOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **Every rule `Step` reaches is determined.** -/
theorem detRelsOk_fixed :
    detRelsOk (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
