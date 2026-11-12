module

public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Defs

/-!
# Round 8, typing across code erasure: the check on quantifier types, part 0

One kernel computation (`decide +kernel`, kernel reduction, no native code): the first 50 relations of the
fixed script pass `xRelQuants tyC`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- The quantifier types of the first 50 relations are checked. -/
theorem xRelQuants_fixed0 :
    xRelQuants tyC ((relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).take 50) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
