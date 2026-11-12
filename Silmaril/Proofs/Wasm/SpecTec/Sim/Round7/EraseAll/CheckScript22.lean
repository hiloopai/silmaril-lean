module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckBase

/-!
# Round 7, the whole-evaluator erasure: checked definitions, chunk 22 of the wasm-3.0 script

One kernel computation (`decide +kernel`, kernel reduction, no native code) on the top-level definitions
550–574 of the fixed script; `Round7/EraseAll/Script.lean` puts the chunks together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

set_option maxRecDepth 100000

/-- Chunk 22 of `xDefsOk_fixed`, `xRelsOk_fixed` and `xAltsOk_fixed`. -/
theorem xScriptOk_chunk22 :
    ((Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.drop 550).take 25).all (xDefOk grE gdE) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
