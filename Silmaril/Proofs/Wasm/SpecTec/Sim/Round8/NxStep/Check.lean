module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxStep.Defs

/-!
# Round 8, `Step` and `Step_read` across erasure: the rules that fail the check

One kernel computation (`decide +kernel`): the rules of `Step` and `Step_read` in the fixed script
that fail `goodRule`. They are:

* four of `Step`: the two host-call rules (`$hostcall`), and `table.grow-succeed` and
  `memory.grow-succeed` (whose conclusions call `$with_tableinst` and `$with_meminst`);
* 32 of `Step_read`: `block`, `loop` and `try_table` (which call `$blocktype_`),
  `vload-pack-val` (an iteration `^(k<M)` rather than `^*`), and the 28 rules with an `otherwise`
  premise.

The other 32 rules of `Step` and 71 of `Step_read` pass.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxStep

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The rules of `Step` and `Step_read` that fail the check.** -/
theorem stepBad_fixed : stepBad (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) =
    ["Step/call_ref-hostfunc-res", "Step/call_ref-hostfunc-div", "Step/table.grow-succeed",
     "Step/memory.grow-succeed", "Step_read/block", "Step_read/loop",
     "Step_read/br_on_cast-fail", "Step_read/br_on_cast_fail-fail",
     "Step_read/throw_ref-handler-next", "Step_read/try_table", "Step_read/table.fill-zero",
     "Step_read/table.fill-succ", "Step_read/table.copy-zero", "Step_read/table.copy-le",
     "Step_read/table.copy-gt", "Step_read/table.init-zero", "Step_read/table.init-succ",
     "Step_read/vload-pack-val", "Step_read/memory.fill-zero", "Step_read/memory.fill-succ",
     "Step_read/memory.copy-zero", "Step_read/memory.copy-le", "Step_read/memory.copy-gt",
     "Step_read/memory.init-zero", "Step_read/memory.init-succ", "Step_read/ref.test-false",
     "Step_read/ref.cast-fail", "Step_read/array.fill-zero", "Step_read/array.fill-succ",
     "Step_read/array.copy-zero", "Step_read/array.copy-le", "Step_read/array.copy-gt",
     "Step_read/array.init_elem-zero", "Step_read/array.init_elem-succ",
     "Step_read/array.init_data-zero", "Step_read/array.init_data-num"] := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round8.NxStep
