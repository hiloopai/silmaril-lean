module

public import Silmaril.Wasm.FX.Examples.Control.Defs
public import Silmaril.Wasm.Models.FXTRun.Defs
public import Silmaril.Wasm.Models.FXLComp.Defs

/-!
# Two `suspend` splits of a compiled `control0`

`splitAt P m n`: after `n` interpreter steps of the compiled program `P` (main function `m`),
the next step can be taken with the payload arity of `$control` (`ctlAr`, one value) and with
payload arity `0`; the first result can take a further interpreter step and the second cannot
(its `br 0` out of the `block (result i32 (ref $cont))` finds one value instead of two). Both
are `StepFXT` steps (`tstep_sound` holds for every payload arity), so `StepFXT` is not
deterministic at the `control0` of these programs (`Silmaril.Wasm.FX.Examples.ControlX.Thms`).

A Silmaril addition (Follow-up 5 workflow, track fx).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.ControlX

open Silmaril.Wasm.Models.FXTRun Silmaril.Wasm.Models.FXLComp Silmaril.Wasm.FX.Examples.Control

/-- The configuration of `P` (main function `m`) after `n` interpreter steps. -/
def cfgAt (P : Silmaril.Wasm.Models.FXL.Prog) (m n : Nat) :=
  runT ctlAr (fxOf P 1) (intrOf P) 40 n (initT P 1 m)

/-- **Two splits at step `n`**: the step with payload arity `1` and the step with payload arity
`0` both exist; only the first can continue. -/
def splitAt (P : Silmaril.Wasm.Models.FXL.Prog) (m n : Nat) : Bool :=
  let a := stepC ctlAr (fxOf P 1) (intrOf P) 40 (cfgAt P m n)
  let b := stepC (fun _ => 0) (fxOf P 1) (intrOf P) 40 (cfgAt P m n)
  a.isSome && b.isSome && (a.bind (stepC ctlAr (fxOf P 1) (intrOf P) 40)).isSome &&
    (b.bind (stepC ctlAr (fxOf P 1) (intrOf P) 40)).isNone

end Silmaril.Wasm.FX.Examples.ControlX
