module

public import Silmaril.Proofs.Wasm.FX.Asyncify.SelSim

/-!
# Selective asyncify on an example, and an unsound analysis

`selP` (values `Nat`):

* function 0, a generator: `push 1; call 5; suspend 0 1; push 0`;
* function 5, a calm helper: `prim 1 (+1)`;
* function 6, a middle layer: `call 0`;
* function 1, the tag-0 handler: `resume 0 (on 0 1); prim 2 (+)`;
* function 2, main: `contNew 6; resume 0 (on 0 1)`.

The generator yields `2` (its `1` incremented by the helper) and finishes with `0`; the handler
adds them, so main returns `[2]`. The analysis `selS` excludes only the helper (`selS_sound`),
so the call of `5` has no check. Source, selective target and the first-order target with
`br_table` dispatch all return `[2]` (closed evaluations by `rfl`), and the selective code is
shorter (`sel_shorter`).

The analysis `noneS` that instruments nothing is unsound (`noneS_unsound`), and the lowering is
then wrong: unwinding reaches the middle layer's call site without its check and traps
(`noneS_run`, `noneS_wrong`).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Wasm.Models.FXAsyncPC (fstep annP bodies rootCode fInit)
open Silmaril.Proofs.Wasm.Models.FXAsync (natTest beh_of_stop)

/-- The example program. -/
def selP : Prog (Ins Nat)
  | 0 => some (0, [.push 1, .call 5, .suspend 0 1, .push 0])
  | 1 => some (2, [.resume 0 [⟨0, 1⟩], .prim 2 fun vs => [vs.sum]])
  | 2 => some (0, [.contNew 6, .resume 0 [⟨0, 1⟩]])
  | 5 => some (1, [.prim 1 fun vs => vs.map (· + 1)])
  | 6 => some (0, [.call 0])
  | _ => none

/-- The analysis: everything but the helper may suspend. -/
def selS (f : Nat) : Bool := f != 5

/-- The analysis that instruments nothing. -/
def noneS (_ : Nat) : Bool := false

theorem selS_sound : Sound selS selP := by
  intro f np body h hf
  rcases f with _ | _ | _ | _ | _ | _ | _ | f
  all_goals first
    | exact absurd hf (by decide)
    | (cases h; intro i hi; rcases List.mem_singleton.mp hi with rfl; trivial)
    | cases h

theorem noneS_unsound : ¬ Sound noneS selP := fun h =>
  h 0 0 _ rfl rfl (.suspend 0 1) (by simp)

theorem sel_src_run :
    runN (sstep selP natTest) 40 (sInit 2 []) = .stop (.done [.val 2]) := rfl

theorem sel_tgt_run :
    runN (tstep (compPO (.selective selS) selP) natTest) 60 (tInit 2 []) =
      .stop (.done [.val 2]) := rfl

theorem sel_pc_run :
    runN (fstep (annP (compPO (.selective selS) selP))
      (bodies (compPO (.selective selS) selP) (rootCode 2)) natTest) 60 (fInit 2 []) =
      .stop (.done [.val 2]) := rfl

theorem sel_src_beh : beh (sstep selP natTest) (sInit 2 []) = {.done [.val 2]} :=
  beh_of_stop sel_src_run

/-- The selective code of the generator is one check shorter than the whole-program code. -/
theorem sel_shorter :
    (compO (V := Nat) (.selective selS) [.push 1, .call 5, .suspend 0 1, .push 0]).length + 1 =
      (compO (V := Nat) .whole [.push 1, .call 5, .suspend 0 1, .push 0]).length := rfl

theorem noneS_run :
    runN (tstep (compPO (.selective noneS) selP) natTest) 60 (tInit 2 []) = .stop .trap := rfl

/-- **An unsound analysis breaks the lowering**: the source returns `[2]`, the target traps. -/
theorem noneS_wrong :
    beh (sstep selP natTest) (sInit 2 []) ≠
      beh (tstep (compPO (.selective noneS) selP) natTest) (tInit 2 []) := by
  rw [sel_src_beh, beh_of_stop noneS_run]
  intro h
  have hm : (Obs.trap : Obs Nat) ∈ ({.done [.val 2]} : Set (Obs Nat)) := h ▸ rfl
  cases hm

end Silmaril.Proofs.Wasm.FX.Asyncify
