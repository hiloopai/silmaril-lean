module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Split
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Chunk1a
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VAgree.Chunk1b

/-!
# Round 7, memory SIMD: `Step` and `Step_read` references on definitions 250–499

`stepRelOnly` on a quarter of the fixed wasm-3.0 script, from the two kernel computations
(`decide +kernel`, kernel reduction, no native code) of `Chunk1a` and `Chunk1b`. Round 4 split the
computation so that each module stays under the 20 s budget under parallel load.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VAgree

/-- `stepRelOnly` on definitions 250–499 of the fixed wasm-3.0 script. -/
theorem stepRelOnly_chunk1 :
    stepRelOnly ((Scripts.Wasm30.fixed.drop 250).take 250) = true :=
  stepRelOnly_halves _ 250 125 stepRelOnly_chunk1a stepRelOnly_chunk1b

end Silmaril.Wasm.SpecTec.Sim.Round7.VAgree
