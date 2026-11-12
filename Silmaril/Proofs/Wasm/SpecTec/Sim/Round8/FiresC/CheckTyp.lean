module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.FiresC.CheckTyp0
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.FiresC.CheckTyp1

/-!
# Round 8, typing across code erasure: the check on types

The two kernel-checked halves (`CheckTyp0`, `CheckTyp1`) together: every type over `tyC` passes
the check `xTy`: its expressions pass round 8's evaluator-level check, its type arguments are
closed, and the `CODE` field of `funcinst` has type `funccode`, no premises and an instance
without argument patterns.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec.Sem

/-- **Every type over `tyC` is checked.** -/
theorem xTypMap_fixed :
    xTypMap tyC (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  unfold xTypMap
  rw [← List.take_append_drop 200 (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed),
    List.all_append, xTypMap_fixed0, xTypMap_fixed1, Bool.and_self]

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
