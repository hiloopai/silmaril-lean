module

public import Silmaril.Wasm.SpecTec.Sim.Round9.BadN.Defs

/-!
# Round 9, RE: the rules of `BadFwdE` left once indexed iterations are allowed

`stepBadN_fixed` (`decide +kernel`): of the eight rules of `BadFwdE`, `vload-pack-val` passes
`goodRuleN`; seven are left.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadN

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The rules of `Step` and `Step_read` that fail all three checks.** -/
theorem stepBadN_fixed : stepBadN (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) =
    ["Step/call_ref-hostfunc-res", "Step/call_ref-hostfunc-div", "Step/table.grow-succeed",
     "Step/memory.grow-succeed", "Step_read/block", "Step_read/loop", "Step_read/try_table"] := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.BadN
