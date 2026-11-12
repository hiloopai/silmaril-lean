module

public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Defs

/-!
# Round 7: the type facts over `tyA` (no `EXPORTS` exemption)

One kernel computation (`decide +kernel`, kernel reduction, no native code): every type of the fixed
wasm-3.0 script named in the list is over the list, in the sense of `Round7.TypAgree.typMapOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **The types named in the list are over the list.** -/
theorem typMapOk_A :
    typMapOk tyA tyA false (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree
