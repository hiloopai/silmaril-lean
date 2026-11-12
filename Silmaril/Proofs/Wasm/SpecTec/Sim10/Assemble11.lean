module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CallIndirectTrap

/-!
# `Task.wholeStepBwd10`, proved

`Step_read` 4 (`call_indirect-trap`) is discharged at every builtins (`bwd10_callIndirectTrap`), so
`BwdRest10j` holds and, with `Assemble10`, the backward half of the 1.0 whole step is proved at the
spec's builtins (`wholeStepBwd10`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.V1.Execution (HostSemantics)

variable {H : Type}

/-- `BwdRest10j` holds at every builtins. -/
theorem bwdRest10j (B : Builtins) (hn : H → String) (host : HostSemantics H) :
    BwdRest10j B hn host where
  callIndirectTrap _ _ hg _ _ hf := bwd10_callIndirectTrap hg hf

/-- **`Task.wholeStepBwd10` is proved.** -/
theorem wholeStepBwd10 : Task.wholeStepBwd10 :=
  wholeStepBwd10_of_rest10 fun _ hn _ host _ _ => bwdRest10j _ hn host

end Silmaril.Wasm.SpecTec.Sim10.Whole
