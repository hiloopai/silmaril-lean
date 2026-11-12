module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.Defs

/-!
# Round 7, `BD`: the rules of `Step_pure`, `Step_read` and `Step` that call `$hostcall`

Three kernel computations (`decide +kernel`, kernel reduction, no native code) on the relations as the fixed
wasm-3.0 script's environment finds them:

* no rule of `Step_pure` and no rule of `Step_read` refers to `$hostcall`;
* of `Step`, only rules 8 (`call_ref`-host, returning) and 9 (diverging) do.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

set_option maxRecDepth 100000

theorem relRulesUsers_pure : VBytes.relRulesUsers "hostcall" "Step_pure" = some [] := by
  decide +kernel

theorem relRulesUsers_read : VBytes.relRulesUsers "hostcall" "Step_read" = some [] := by
  decide +kernel

theorem relRulesUsers_step : VBytes.relRulesUsers "hostcall" "Step" = some [8, 9] := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
