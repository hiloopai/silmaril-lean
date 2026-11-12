module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Defs

/-!
# Round 7, moving derivations across erasure: the check on quantifier types

One kernel computation (`decide +kernel`, kernel reduction, no native code): every quantifier of every rule
`Step` reaches has a type that passes `xTy` at `tyB`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **Every quantifier type of a rule `Step` reaches is checked.** -/
theorem xRelQuants_fixed :
    xRelQuants TypAgree.tyB (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
