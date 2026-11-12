module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Defs

/-!
# Round 7, moving derivations across erasure: the closure check on the script

One kernel computation (`decide +kernel`, kernel reduction, no native code): every rule of every relation that
SpecTec's `Step` reaches is closed over its quantifiers (`Round7.EraseDer.ruleClosed`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **Every rule `Step` reaches is closed over its quantifiers.** -/
theorem closedRels_fixed :
    closedRels (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
