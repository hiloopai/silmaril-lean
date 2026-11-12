module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxDer.Defs

/-!
# Round 8, derivations across erasure without a swap set: the check on iterated premises

One kernel computation (`decide +kernel`, kernel reduction, no native code): every iterated premise of a rule of
a `grE` relation iterates over a list.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxDer

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **Every iterated premise of a checked rule iterates over a list.** -/
theorem iterRels_fixed : iterRels (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.NxDer
