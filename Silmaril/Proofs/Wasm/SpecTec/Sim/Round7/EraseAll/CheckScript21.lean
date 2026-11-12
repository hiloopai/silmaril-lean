module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript21a
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript21b

/-!
# Round 7, the whole-evaluator erasure: checked definitions, chunk 21 of the wasm-3.0 script

Top-level definitions 525–549 of the fixed script, from the two kernel-checked halves
`CheckScript21a` and `CheckScript21b` (this chunk is one of the heaviest);
`Round7/EraseAll/Script.lean` puts the chunks together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

/-- Chunk 21 of `xDefsOk_fixed`, `xRelsOk_fixed` and `xAltsOk_fixed`. -/
theorem xScriptOk_chunk21 :
    ((Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.drop 525).take 25).all (xDefOk grE gdE) = true :=
  all_drop_take_add _ _ 525 13 12 xScriptOk_chunk21a xScriptOk_chunk21b

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
