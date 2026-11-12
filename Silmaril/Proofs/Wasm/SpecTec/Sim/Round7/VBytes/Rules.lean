module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VBytes.Defs

/-!
# Round 7, memory SIMD: the rules of `Step_pure`, `Step_read` and `Step` that call `$vbytes_`

Three kernel computations (`decide +kernel`, kernel reduction, no native code) on the relations as the fixed
wasm-3.0 script's environment finds them:

* no rule of `Step_pure` refers to `$vbytes_`;
* of `Step_read`, only rule 43 (`vload-num-val`) does;
* of `Step`, only rule 23 (`vstore-val`) does.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VBytes

set_option maxRecDepth 100000

theorem relRulesUsers_pure : relRulesUsers "vbytes_" "Step_pure" = some [] := by
  decide +kernel

theorem relRulesUsers_read : relRulesUsers "vbytes_" "Step_read" = some [43] := by
  decide +kernel

theorem relRulesUsers_step : relRulesUsers "vbytes_" "Step" = some [23] := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.VBytes
