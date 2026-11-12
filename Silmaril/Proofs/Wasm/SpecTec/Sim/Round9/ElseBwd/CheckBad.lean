module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs

/-!
# Round 9, `otherwise` rules: the rules of `BadFwd` left once `otherwise` is allowed

`stepBadE_fixed` (`decide +kernel`): of the 36 rules of `Step` and `Step_read` that fail
`NxStep.goodRule`, the 28 `otherwise` rules pass `goodRuleE`. Eight are left: the two host-call
rules, `table.grow-succeed`, `memory.grow-succeed`, `block`, `loop`, `try_table` and
`vload-pack-val`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The rules of `Step` and `Step_read` that fail both checks.** -/
theorem stepBadE_fixed : stepBadE (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) =
    ["Step/call_ref-hostfunc-res", "Step/call_ref-hostfunc-div", "Step/table.grow-succeed",
     "Step/memory.grow-succeed", "Step_read/block", "Step_read/loop", "Step_read/try_table",
     "Step_read/vload-pack-val"] := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
