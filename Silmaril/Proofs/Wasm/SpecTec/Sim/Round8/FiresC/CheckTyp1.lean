module

public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Defs

/-!
# Round 8, typing across code erasure: the check on types, part 1

Kernel computations (`decide +kernel`, kernel reduction, no native code): the types of the fixed script after
the first 200 pass `xTypMap tyC`, and `funccode` is a variant of `FUNC` and `_HOSTFUNC text`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- The types of the script after the first 200 are checked. -/
theorem xTypMap_fixed1 :
    ((typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).drop 200).all
      (fun p => !tyC.contains p.1 || xInsts tyC p.2.2) = true := by
  decide +kernel

/-- **`funccode` has the shape `funccodeOk`.** -/
theorem funccodeMap_fixed :
    funccodeMap (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
