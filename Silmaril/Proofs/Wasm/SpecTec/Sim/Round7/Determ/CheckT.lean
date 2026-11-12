module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Defs

/-!
# Round 7, determination: no type over `tyA` declares an `EXPORTS` field

One kernel computation (`decide +kernel`, kernel reduction, no native code).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA)

set_option maxRecDepth 100000

/-- **No type named in `tyA` declares a record field `EXPORTS`.** -/
theorem typMapNoExp_A :
    typMapNoExp tyA (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
