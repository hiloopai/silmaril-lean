module

public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Defs

/-!
# Round 7: the quantifiers of the rules `Step` reaches are over `tyB`

One kernel computation (`decide +kernel`, kernel reduction, no native code) over the fixed
wasm-3.0 script: every rule of a relation that `Step` reaches quantifies only over types
over `tyB`, in the sense of `Round7.TypAgree.relQuantsOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **Every rule of a relation `Step` reaches quantifies over `tyB`.** -/
theorem relQuantsOk_B :
    relQuantsOk tyA tyB (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree
