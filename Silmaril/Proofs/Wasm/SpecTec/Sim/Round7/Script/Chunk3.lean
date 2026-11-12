module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs

/-!
# Round 7: the `Step` closure facts on definitions 300–399 of the fixed wasm-3.0 script

One kernel computation (`decide +kernel`, kernel reduction, no native code): every top-level definition at
positions 300 to 399 of `Scripts.Wasm30.fixed` that is named in `stepReach` refers only to
names in `stepReach` and has only `evOk` events. `Round7/Script/Assemble.lean` puts the ten
chunks together; the script is split so that each module stays well under the 20 s budget.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Script

set_option maxRecDepth 100000

/-- `scriptOk` on definitions 300–399 of the fixed wasm-3.0 script. -/
theorem scriptOk_chunk3 :
    scriptOk stepReach ((Scripts.Wasm30.fixed.drop 300).take 100) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.Script
