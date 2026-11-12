module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Defs

/-!
# Round 7, moving derivations across erasure: the check on types

One kernel computation (`decide +kernel`, kernel reduction, no native code): every type over `tyB` passes the
check `xTy`: its expressions pass the evaluator-level check, its type arguments are closed, and
the `EXPORTS` field of `moduleinst` has type `exportinst*` and no premises.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **Every type over `tyB` is checked.** -/
theorem xTypMap_fixed :
    xTypMap TypAgree.tyB (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
