module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript13a
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript13b

/-!
# Round 7, the whole-evaluator erasure: checked definitions, chunk 13 of the wasm-3.0 script

Top-level definitions 325–349 of the fixed script, from the two kernel-checked halves
`CheckScript13a` and `CheckScript13b` (this chunk is one of the heaviest);
`Round7/EraseAll/Script.lean` puts the chunks together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

/-- Chunk 13 of `xDefsOk_fixed`, `xRelsOk_fixed` and `xAltsOk_fixed`. -/
theorem xScriptOk_chunk13 :
    ((Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.drop 325).take 25).all (xDefOk grE gdE) = true :=
  all_drop_take_add _ _ 325 13 12 xScriptOk_chunk13a xScriptOk_chunk13b

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
