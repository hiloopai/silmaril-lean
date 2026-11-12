module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VAgree.Defs

/-!
# Round 7, memory SIMD: `Step` and `Step_read` references on definitions 625–749

One kernel computation (`decide +kernel`, kernel reduction, no native code) of `stepRelOnly` on half of a
chunk of the fixed wasm-3.0 script. Round 4 split the chunk so that each module stays under the
time budget under parallel load; `Chunk2` puts the halves together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

set_option maxRecDepth 100000

/-- `stepRelOnly` on definitions 625–749 of the fixed wasm-3.0 script. -/
theorem stepRelOnly_chunk2b :
    stepRelOnly ((Scripts.Wasm30.fixed.drop 625).take 125) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
