module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckBase

/-!
# Round 7, the whole-evaluator erasure: checked definitions, chunk 25a of the wasm-3.0 script

One kernel computation (`decide +kernel`, kernel reduction, no native code) on the top-level definitions
625–637 of the fixed script; `CheckScript25` puts the two halves together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

set_option maxRecDepth 100000

/-- Chunk 25a of `xDefsOk_fixed`, `xRelsOk_fixed` and `xAltsOk_fixed`. -/
theorem xScriptOk_chunk25a :
    ((Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.drop 625).take 13).all (xDefOk grE gdE) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
