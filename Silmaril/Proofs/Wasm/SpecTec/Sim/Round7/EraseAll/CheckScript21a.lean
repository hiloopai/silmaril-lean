module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckBase

/-!
# Round 7, the whole-evaluator erasure: checked definitions, chunk 21a of the wasm-3.0 script

One kernel computation (`decide +kernel`, kernel reduction, no native code) on the top-level definitions
525–537 of the fixed script; `CheckScript21` puts the two halves together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

set_option maxRecDepth 100000

/-- Chunk 21a of `xDefsOk_fixed`, `xRelsOk_fixed` and `xAltsOk_fixed`. -/
theorem xScriptOk_chunk21a :
    ((Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.drop 525).take 13).all (xDefOk grE gdE) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
