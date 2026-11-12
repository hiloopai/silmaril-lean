module

public import Silmaril.Wasm.FX.Asyncify.Selective.Defs

/-!
# Selective instrumentation: an example

`twiceP` (values `Nat`):

* function 0, `inc`: `prim 1 (+1)`;
* function 1, `twice`: `call 0; call 0`;
* function 2, the generator: `push 1; call 1; suspend 0 1; push 0`;
* function 3, main: `contNew 2; resume 0 (on 0 4)`;
* function 4, the handler: `drop` (it drops the continuation and returns the payload).

The analysis on the functions `< 5` finds `{0, 1, 4}` (`twice_analyze`): `inc`, `twice` and the
handler cannot suspend. The instrumented program has three call-site checks (after the two calls
in `twice` and the call of `twice`); the optimized one has none (`twice_checks`). From a call of
main, the kernel returns `[3]` in 17 steps, the instrumented program in 24 and the optimized one
in 21 (`twice_opt_run`, `twice_tgt_run`); the instrumented one is still running after 21 steps
(`twice_tgt_slower`). All by closed evaluation (`rfl`).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Selective

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.Selective

/-- The example program. -/
def twiceP : Prog (Ins Nat)
  | 0 => some (1, [.prim 1 fun vs => vs.map (· + 1)])
  | 1 => some (1, [.call 0, .call 0])
  | 2 => some (0, [.push 1, .call 1, .suspend 0 1, .push 0])
  | 3 => some (0, [.contNew 2, .resume 0 [⟨0, 4⟩]])
  | 4 => some (2, [.drop])
  | _ => none

/-- The branch test of the example (unused by `twiceP`). -/
def twiceTest (v : Nat) : Bool := v != 0

/-- The analysis result. -/
def twiceS : Nat → Bool := analyze (compP twiceP) 5

/-- The number of call-site checks (`chk`) in the bodies of functions `< n`. -/
def checks (Q : Prog (TIns Nat)) (n : Nat) : Nat :=
  ((List.range n).map fun f => ((Q f).map fun x => (x.2.filter isChk).length).getD 0).sum

theorem twice_analyze : (List.range 6).map twiceS = [true, true, false, false, true, false] := rfl

theorem twice_checks : checks (compP twiceP) 5 = 3 ∧ checks (compSel twiceS twiceP) 5 = 0 := ⟨rfl, rfl⟩

theorem twice_src_run :
    runN (sstep twiceP twiceTest) 17 (sInit 3 []) = .stop (.done [.val 3]) := rfl

theorem twice_opt_run :
    runN (tstep (compSel twiceS twiceP) twiceTest) 21 (selInit twiceS 3 []) = .stop (.done [.val 3]) := rfl

theorem twice_tgt_run :
    runN (tstep (compP twiceP) twiceTest) 24 (tInit 3 []) = .stop (.done [.val 3]) := rfl

theorem twice_tgt_slower : ∃ c, runN (tstep (compP twiceP) twiceTest) 21 (tInit 3 []) = .next c :=
  ⟨_, rfl⟩

end Silmaril.Proofs.Wasm.FX.Asyncify.Selective
