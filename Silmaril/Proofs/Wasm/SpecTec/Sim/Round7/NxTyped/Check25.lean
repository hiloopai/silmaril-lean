module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Sig

/-!
# Round 7, REH route 2: the flow check on top-level definitions 625–649 of the script

One kernel computation (`decide +kernel`, kernel reduction, no native code): in this slice of the fixed
wasm-3.0 script, the type entries of `sigExtra` agree with the type definitions, and every
definition and relation passes the flow check `NxTyped.flowItems sigX tsigFixed`.
`Round7/NxTyped/Assemble.lean` puts the forty slices together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 25 of `typItemsOk_fixed` and `flowItems_fixed`. -/
theorem check25 :
    typItemsOk sigExtra extraNames ((fixed.drop 625).take 25) = true ∧
      flowItems sigX tsigFixed ((fixed.drop 625).take 25) = 0 := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
