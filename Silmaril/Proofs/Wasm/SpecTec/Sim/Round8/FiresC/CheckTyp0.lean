module

public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Defs

/-!
# Round 8, typing across code erasure: the check on types, part 0

One kernel computation (`decide +kernel`, kernel reduction, no native code): the first 200 types of the fixed
script pass `xTypMap tyC`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- The first 200 types of the script are checked. -/
theorem xTypMap_fixed0 :
    ((typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).take 200).all
      (fun p => !tyC.contains p.1 || xInsts tyC p.2.2) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
