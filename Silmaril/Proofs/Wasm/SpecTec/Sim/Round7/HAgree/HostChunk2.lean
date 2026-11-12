module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.Defs

/-!
# Round 7, `BD`: `$hostcall` on definitions 500–749 of the fixed wasm-3.0 script

One kernel computation (`decide +kernel`, kernel reduction, no native code). The script is split into four
chunks so that each module stays under the 20 s budget.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

set_option maxRecDepth 100000

/-- `hostcallOnlyStep` on definitions 500–749 of the fixed wasm-3.0 script. -/
theorem hostcallOnlyStep_chunk2 :
    hostcallOnlyStep ((Scripts.Wasm30.fixed.drop 500).take 250) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
