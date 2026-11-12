module

public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Defs

/-!
# Round 8, function code erasure: checked definitions, chunk 24 of the wasm-3.0 script

One kernel computation (`decide +kernel`, kernel reduction, no native code) on the top-level definitions
600–624 of the fixed script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll

set_option maxRecDepth 100000

/-- Chunk 24 of the check of the wasm-3.0 script. -/
theorem xScriptOk_chunk24 :
    ((Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.drop 600).take 25).all (xDefOk grC gdC) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll
