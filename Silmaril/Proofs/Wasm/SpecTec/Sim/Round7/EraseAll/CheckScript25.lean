module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript25a
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript25b

/-!
# Round 7, the whole-evaluator erasure: checked definitions, chunk 25 of the wasm-3.0 script

Top-level definitions 625–649 of the fixed script, from the two kernel-checked halves
`CheckScript25a` and `CheckScript25b` (this chunk is one of the heaviest);
`Round7/EraseAll/Script.lean` puts the chunks together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

/-- Chunk 25 of `xDefsOk_fixed`, `xRelsOk_fixed` and `xAltsOk_fixed`. -/
theorem xScriptOk_chunk25 :
    ((Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.drop 625).take 25).all (xDefOk grE gdE) = true :=
  all_drop_take_add _ _ 625 13 12 xScriptOk_chunk25a xScriptOk_chunk25b

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
