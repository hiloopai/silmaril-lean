module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.Defs

/-!
# Round 7, memory SIMD: `Step` and `Step_read` references on definitions 0–249

One kernel computation (`decide +kernel`, kernel reduction, no native code) of `stepRelOnly` on a quarter of
the fixed wasm-3.0 script, split so that each module stays under the 20 s budget.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

set_option maxRecDepth 100000

/-- `stepRelOnly` on definitions 0–249 of the fixed wasm-3.0 script. -/
theorem stepRelOnly_chunk0 :
    stepRelOnly ((Scripts.Wasm30.fixed.drop 0).take 250) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
