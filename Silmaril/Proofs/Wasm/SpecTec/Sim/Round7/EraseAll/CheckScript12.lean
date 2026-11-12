module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript12a
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseAll.CheckScript12b

/-!
# Round 7, the whole-evaluator erasure: checked definitions, chunk 12 of the wasm-3.0 script

Top-level definitions 300–324 of the fixed script, from the two kernel-checked halves
`CheckScript12a` and `CheckScript12b` (this chunk is one of the heaviest);
`Round7/EraseAll/Script.lean` puts the chunks together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

/-- Chunk 12 of `xDefsOk_fixed`, `xRelsOk_fixed` and `xAltsOk_fixed`. -/
theorem xScriptOk_chunk12 :
    ((Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.drop 300).take 25).all (xDefOk grE gdE) = true :=
  all_drop_take_add _ _ 300 13 12 xScriptOk_chunk12a xScriptOk_chunk12b

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
