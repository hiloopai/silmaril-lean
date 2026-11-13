module

public import Silmaril.Proofs.Wasm.Models.FXAsync.Sim

/-!
# A generator with forwarding, run on both machines

`fwdP` (values `Nat`):

* function 0, the generator: `push 1; suspend 0 1; push 2; suspend 0 1; push 0`;
* function 3, a middle layer: `contNew 0; resume 0 (on 1 4)`. It resumes the generator under a
  handler for tag 1 only, so the generator's tag-0 suspensions are forwarded through it and its
  frame is captured with the generator's;
* function 1, the tag-0 handler: `resume 0 (on 0 1); prim 2 (+)`. It resumes the captured
  continuation under a fresh handler and adds the yielded value to the result;
* function 2, main: `contNew 3; resume 0 (on 0 1)`.

`fwd_src_run`, `fwd_tgt_run`: called from `sInit 2 []`, the source returns `[3]`, and so does
the compiled program from `tInit 2 []` (after its unwinding and rewinding steps). Both are closed
evaluations by `rfl`. `fwd_beh`: the source's only behaviour is returning `[3]`, and by
`beh_eq` so is the target's.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsync

open Silmaril.Wasm.Models.FXAsync

/-- The example program. -/
def fwdP : Prog (Ins Nat)
  | 0 => some (0, [.push 1, .suspend 0 1, .push 2, .suspend 0 1, .push 0])
  | 1 => some (2, [.resume 0 [⟨0, 1⟩], .prim 2 fun vs => [vs.sum]])
  | 2 => some (0, [.contNew 3, .resume 0 [⟨0, 1⟩]])
  | 3 => some (0, [.contNew 0, .resume 0 [⟨1, 4⟩]])
  | _ => none

/-- The branch test of the example (unused by `fwdP`). -/
def natTest (v : Nat) : Bool := v != 0

theorem fwd_src_run :
    runN (sstep fwdP natTest) 40 (sInit 2 []) = .stop (.done [.val 3]) := rfl

theorem fwd_tgt_run :
    runN (tstep (compP fwdP) natTest) 80 (tInit 2 []) = .stop (.done [.val 3]) := rfl

theorem trC_sInit {V : Type} (f : Nat) (args : List (SV V)) : trC (sInit f args) = tInit f args :=
  rfl

theorem fwd_beh : beh (sstep fwdP natTest) (sInit 2 []) = {.done [.val 3]} :=
  beh_of_stop fwd_src_run

theorem fwd_beh_tgt : beh (tstep (compP fwdP) natTest) (tInit 2 []) = {.done [.val 3]} := by
  rw [← trC_sInit, ← beh_eq, fwd_beh]

end Silmaril.Proofs.Wasm.Models.FXAsync
