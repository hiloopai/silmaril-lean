module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Split
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Chunk3a
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Chunk3b

/-!
# Round 7, memory SIMD: `Step` and `Step_read` references on definitions 750–975

`stepRelOnly` on a quarter of the fixed wasm-3.0 script, from the two kernel computations
(`decide +kernel`, kernel reduction, no native code) of `Chunk3a` and `Chunk3b`. Round 4 split the
computation so that each module stays under the 20 s budget under parallel load.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

/-- `stepRelOnly` on definitions 750–975 of the fixed wasm-3.0 script. -/
theorem stepRelOnly_chunk3 :
    stepRelOnly ((Scripts.Wasm30.fixed.drop 750).take 250) = true :=
  stepRelOnly_halves _ 750 125 stepRelOnly_chunk3a stepRelOnly_chunk3b

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
