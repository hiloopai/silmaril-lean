module

public import Silmaril.Wasm.FX.Logic.Thms
public import Silmaril.Wasm.FX.Logic.Tactic.Defs
public import Silmaril.Wasm.FX.Examples.EveryRun.Defs

/-!
# Cancelling a generator: a run, by the existential WasmFX calculus

`cancel_mem`: the program `cancelProg` has a `StepFX'` run that throws the exception at address
`0`, at every profile and host relation, proved with the weakest-precondition calculus of
`Silmaril.Wasm.FX.Logic` (`wp_*` rules and the `fx_*` tactics).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.FX.Logic
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {host : HostSemantics Nat}

/-- The postcondition: the exception at address `0`. -/
abbrev cancelQ : PostFX Nat := fun _ _ _ o => o = .ofResult (.throw 0)

/-- The frame of every function. -/
abbrev cF : Frame := ⟨[], kitM 2⟩

/-- The generator's code after its first `suspend`. -/
abbrev cRest : List AdminFX :=
  [.core (.plain (.intConst .i32 2)), .core (.plain .nop), .fx (.suspend (ix 0)),
    .core (.plain (.intConst .i32 3)), .core (.plain .nop), .fx (.suspend (ix 0)),
    .core (.plain (.intConst .i32 0)), .core (.plain .nop)]

theorem cancel_wp :
    WP P host (kitFx 2 cancelWY) (kitStore 2) [] cF [.core (.plain (.call (ix 1)))] cancelQ := by
  show WP P host (kitFx 2 cancelWY) (kitStore 2) [] cF (fvals [] ++ [Admin.plain (.call (ix 1))].map .core ++ []) _
  refine wp_coreStep [] [] (Step.call (a := 1) rfl rfl) ?_
  show WP P host (kitFx 2 cancelWY) (kitStore 2) [] cF
    (cvals [] ++ [.core (.ref (.func 1)), .core (.callRefType kitTypes.head!)]) _
  fx_call
  show WP _ _ _ _ [] cF (fvals [] ++ [.core (.plain (.refFunc (ix 0)))] ++
    [.fx (.contNew (ix 0)), InstrFX.toAdmin (resumeFX [.fx (.resumeThrow (ix 0) (ix 0) [])])]) _
  refine wp_refFunc [] _ rfl ?_
  show WP _ _ _ _ [] cF (fvals [] ++ [.core (.ref (.func 0)), .fx (.contNew (ix 0))] ++
    [InstrFX.toAdmin (resumeFX [.fx (.resumeThrow (ix 0) (ix 0) [])])]) _
  refine wp_contNew [] _ rfl ?_
  show WP _ _ _ _ _ cF (fvals [] ++ (fvals [.cont 0] ++ [.block btD _]) ++ []) _
  refine wp_block [] [] rfl rfl ?_
  show WP _ _ _ _ _ cF [.label 1 [] (fvals [.cont 0] ++ _)] _
  refine wp_label ?_
  show WP _ _ _ _ _ cF (fvals [] ++ (fvals [.cont 0] ++ [.block btH _]) ++
    [.fx (.resumeThrow (ix 0) (ix 0) [])]) _
  refine wp_block [] _ rfl rfl ?_
  show WP _ _ _ _ _ cF (fvals [] ++ [.label 2 [] _] ++ [.fx (.resumeThrow (ix 0) (ix 0) [])]) _
  refine wp_seq (Or.inr (by simp)) (wp_label ?_)
  show WP _ _ _ _ _ cF (fvals [] ++ (fvals [] ++ [.contRef 0,
    .fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)])]) ++ [.core (.plain (.br (ix 1)))]) _
  refine wp_seq (Or.inr (by simp)) ?_
  fx_resume
  show WP _ _ _ _ _ cF (cvals [] ++ [.core (.ref (.func 0)), .core (.callRefType kitTypes.head!)]) _
  fx_call
  show WP _ _ _ _ _ cF (fvals [] ++ (fvals (liftV [Val.i32 1]) ++
    [Instr.nop].map fun i => .core (.plain i)) ++ (.fx (.suspend (ix 0)) :: cRest)) _
  fx_exec
  show WP _ _ _ _ _ cF (fvals [] ++ (fvals [.val (Val.i32 1)] ++ [.fx (.suspend (ix 0))]) ++ cRest) _
  refine wp_seq (Or.inr (by simp)) (wp_suspend ?_)
  fx_post
  fx_catch
  rw [show (ix 0 : LabelIdx).toNat = 0 from rfl]
  refine ⟨[], _, rfl, rfl, ?_⟩
  simp only [List.map_nil, List.append_nil]
  refine wp_val ?_
  fx_post
  show WP _ _ _ _ _ cF (cvals [Val.i32 1] ++ [.contRef 1, .fx (.resumeThrow (ix 0) (ix 0) [])]) _
  refine wp_resumeThrow_handle (vs := [Val.i32 1]) rfl rfl rfl ?_
  show WP _ _ _ _ _ cF [.frame 1 cF [.label 1 [] (cthrowing 0 ++ cRest)]] _
  refine wp_frame (wp_label (wp_app (by simp) (wp_throwing ?_)))
  fx_post
  rfl

/-- **A run of the cancelled generator throws the exception at address `0`**, at every profile
and host relation. -/
theorem cancel_mem : Behaviour.throws 0 ∈
    behavioursFX' P host (kitFx 2 cancelWY) (cancelProg P host) :=
  WP.behaviour (r := .throw 0) cancel_wp

end Silmaril.Proofs.Wasm.FX.Examples.EveryRun
