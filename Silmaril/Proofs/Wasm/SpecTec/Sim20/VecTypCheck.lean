module

public import Silmaril.Wasm.SpecTec.Sim20.VecTyp.Defs

/-!
# Kernel check: in the corrected 2.0 script, typing avoids the vector builtins

**`defsTypsOkB_fixedT20`**: in `fixedT20`, every definition outside `badV20` and every type refers
to no relation and to no definition in `badV20`. In particular no type of the script, and no
definition a type can reach, calls `$lanes_`, `$inv_lanes_`, `$vunop_`, `$vbinop_` or `$vrelop_`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTyp

open Silmaril.Wasm.SpecTec.Sim20.StoreFix (fixedT20)

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **The definitions outside `badV20` and the types of `fixedT20` are harmless** (kernel). -/
theorem defsTypsOkB_fixedT20 : defsTypsOkB badV20 fixedT20 = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim20.VecTyp
