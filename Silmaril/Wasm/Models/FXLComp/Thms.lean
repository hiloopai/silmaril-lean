module

public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Proofs.Wasm.Models.FXLComp.RefuteCall

/-!
# Why the explainer's schedulers are compiled to `StepFXT`

`StepFX'` keeps continuation references on the operand stack only. Besides
`stepFX'_localSet_cont_stuck` (`Silmaril.Wasm.Models.FXT`: a continuation cannot be stored in a
local, which refutes the dynamic schedulers as written), this module records why the static
scheduler cannot be written either (proof in `Silmaril.Proofs.Wasm.Models.FXLComp.RefuteCall`):

* **`callRef_cont_stuck`** (no host calls): `V, ref.cont k, ref.func a; call_ref; T` has no
  `StepFX'` step when `a` is a host function that is not an FX function of zero parameters,
  such as the explainer's imported `$enqueue`: a host or FX function takes Core values only.

The compiler of `Silmaril.Wasm.Models.FXLComp` therefore turns `$enqueue`, `$dequeue`, locals and
`print_i32` into the intrinsics of `StepFXT`.

A Silmaril addition.
-/
