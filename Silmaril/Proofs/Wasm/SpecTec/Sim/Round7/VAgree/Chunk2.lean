module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Split
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Chunk2a
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Chunk2b

/-!
# Round 7, memory SIMD: `Step` and `Step_read` references on definitions 500–749

`stepRelOnly` on a quarter of the fixed wasm-3.0 script, from the two kernel computations
(`decide +kernel`, kernel reduction, no native code) of `Chunk2a` and `Chunk2b`. Round 4 split the
computation so that each module stays under the 20 s budget under parallel load.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

/-- `stepRelOnly` on definitions 500–749 of the fixed wasm-3.0 script. -/
theorem stepRelOnly_chunk2 :
    stepRelOnly ((Scripts.Wasm30.fixed.drop 500).take 250) = true :=
  stepRelOnly_halves _ 500 125 stepRelOnly_chunk2a stepRelOnly_chunk2b

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
