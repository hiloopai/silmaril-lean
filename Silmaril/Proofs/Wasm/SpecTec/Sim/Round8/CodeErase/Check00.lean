module

public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Defs

/-!
# Round 8, function code erasure: checked definitions, chunk 0 of the wasm-3.0 script

One kernel computation (`decide +kernel`, kernel reduction, no native code) on the top-level definitions
0–24 of the fixed script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll

set_option maxRecDepth 100000

/-- Chunk 0 of the check of the wasm-3.0 script. -/
theorem xScriptOk_chunk00 :
    ((Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.drop 0).take 25).all (xDefOk grC gdC) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll
