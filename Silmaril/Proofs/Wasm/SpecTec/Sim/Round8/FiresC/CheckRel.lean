module

public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Defs

/-!
# Round 8, firing across code erasure: the relations `relG`

One kernel computation (`decide +kernel`, kernel reduction, no native code): the relations `relG` (`Ref_ok`,
`Expand` and the validation relations they reach) are relations `Step` reaches other than `Step`,
have no parameters, and their rules pass round 8's check, have no `otherwise` premise and consult
only `relG`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **`relG` is closed under relation premises**, without parameters or `otherwise`. -/
theorem relGOk_fixed : relGOk (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
