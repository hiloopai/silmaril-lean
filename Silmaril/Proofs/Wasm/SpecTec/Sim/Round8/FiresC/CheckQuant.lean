module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.FiresC.CheckQuant0
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.FiresC.CheckQuant1

/-!
# Round 8, typing across code erasure: the check on quantifier types

The two kernel-checked halves (`CheckQuant0`, `CheckQuant1`) together: every quantifier of every
rule `Step` reaches has a type that passes `xTy` at `tyC`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec.Sem

/-- **Every quantifier type of a rule `Step` reaches is checked.** -/
theorem xRelQuants_fixed :
    xRelQuants tyC (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  have h0 := xRelQuants_fixed0
  have h1 := xRelQuants_fixed1
  unfold xRelQuants at h0 h1 ⊢
  rw [← List.take_append_drop 50 (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed),
    List.all_append, h0, h1, Bool.and_self]

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
