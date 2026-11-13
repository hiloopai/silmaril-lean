module

public import Silmaril.Wasm.FX.Asyncify.Shadow.Defs
public import Silmaril.Wasm.Models.FXAsync.Thms

/-!
# The shadow-stack strategy: an example run

The forwarding generator `fwdP` of `FXAsync` (two suspensions forwarded through a middle layer,
each handled by resuming the captured stack), compiled, annotated and run on `mstep` from
`mInit 2 []`: it returns `[3]` in 35 steps, as on `fstep` (`fwd_shadow_run`), and the memory
then holds 18 cells, the dead records of the buffers written while unwinding
(`fwd_shadow_mem`). Closed evaluations by `rfl`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Shadow

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC Silmaril.Wasm.FX.Asyncify.Shadow
open Silmaril.Proofs.Wasm.Models.FXAsync (fwdP natTest)

/-- The annotated program of the example. -/
def fwdA : Prog (AIns Nat) := annP (compP fwdP)

/-- Its code table for a call of function 2. -/
def fwdB : Nat → Option (List (TIns Nat)) := bodies (compP fwdP) (rootCode 2)

theorem fwd_shadow_run : runN (mstep fwdA fwdB natTest) 35 (mInit 2 []) = .stop (.done [.val 3]) :=
  rfl

theorem fwd_shadow_mem :
    (match runN (mstep fwdA fwdB natTest) 34 (mInit 2 []) with
      | .next c => c.mem.length
      | .stop _ => 0) = 18 := rfl

end Silmaril.Proofs.Wasm.FX.Asyncify.Shadow
