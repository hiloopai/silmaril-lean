module

public import Silmaril.Wasm.FX.Logic.Thms
public import Silmaril.Wasm.FX.Logic.Tactic.Defs
public import Silmaril.Wasm.FX.Examples.EveryRun.Defs

/-!
# Switching between two coroutines: a run, by the existential WasmFX calculus

`switch_mem`: the program `switchProg` has a `StepFX'` run that returns `[42]`, at every profile
and host relation, proved with the weakest-precondition calculus of `Silmaril.Wasm.FX.Logic`.

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

/-- The postcondition: the result `[42]`. -/
abbrev switchQ : PostFX Nat := fun _ _ _ o => o = .ofResult (.values [Val.i32 42])

/-- The frame of every function. -/
abbrev wF : Frame := ⟨[], swM⟩

abbrev wRestB : List AdminFX :=
  [.core (.plain .drop), .core (.plain (.intConst .i32 42)), .core (.plain .nop)]

abbrev wRest : List AdminFX :=
  [InstrFX.toAdmin (startFX 1), InstrFX.toAdmin (.block btR [.fx (.resume (ix 0) [.onSwitch (ix 0)])])]

theorem switch_wp :
    WP P host swFx swStore [] wF [.core (.plain (.call (ix 2)))] switchQ := by
  show WP P host swFx swStore [] wF (fvals [] ++ [Admin.plain (.call (ix 2))].map .core ++ []) _
  refine wp_coreStep [] [] (Step.call (a := 2) rfl rfl) ?_
  show WP P host swFx swStore [] wF
    (cvals [] ++ [.core (.ref (.func 2)), .core (.callRefType kitTypes.head!)]) _
  fx_call
  -- start B
  show WP _ _ _ _ [] wF (fvals [] ++ (fvals [] ++ [.block btS _]) ++ wRest) _
  refine wp_block [] _ rfl rfl ?_
  refine wp_seq (Or.inr (by simp)) (wp_label ?_)
  show WP _ _ _ _ [] wF (fvals [] ++ [.core (.plain (.refFunc (ix 0)))] ++
    [.fx (.contNew (ix 0)), .fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)])]) _
  refine wp_refFunc [] _ rfl ?_
  refine wp_contNew [] _ rfl ?_
  show WP _ _ _ _ _ wF (fvals [] ++ [.contRef 0, .fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)])]) _
  fx_resume
  show WP _ _ _ _ _ wF (cvals [] ++ [.core (.ref (.func 0)), .core (.callRefType kitTypes.head!)]) _
  fx_call
  show WP _ _ _ _ _ wF ((fvals [] ++ [.fx (.suspend (ix 0))]) ++ wRestB) _
  refine wp_app (by simp) (wp_suspend ?_)
  fx_post
  fx_catch
  rw [show (ix 0 : LabelIdx).toNat = 0 from rfl]
  refine ⟨[], _, rfl, rfl, ?_⟩
  simp only [List.map_nil, List.append_nil]
  refine wp_val ?_
  fx_post
  -- start A
  show WP _ _ _ _ _ wF (fvals [.cont 1] ++ (fvals [] ++ [.block btS _]) ++
    [InstrFX.toAdmin (.block btR [.fx (.resume (ix 0) [.onSwitch (ix 0)])])]) _
  refine wp_block [.cont 1] _ rfl rfl ?_
  refine wp_seq (Or.inl (by simp)) (wp_label ?_)
  show WP _ _ _ _ _ wF (fvals [] ++ [.core (.plain (.refFunc (ix 1)))] ++
    [.fx (.contNew (ix 0)), .fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)])]) _
  refine wp_refFunc [] _ rfl ?_
  refine wp_contNew [] _ rfl ?_
  show WP _ _ _ _ _ wF (fvals [] ++ [.contRef 2, .fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)])]) _
  fx_resume
  show WP _ _ _ _ _ wF (cvals [] ++ [.core (.ref (.func 1)), .core (.callRefType kitTypes.head!)]) _
  fx_call
  show WP _ _ _ _ _ wF ((fvals [] ++ [.fx (.suspend (ix 0))]) ++ [.fx (.switch (ix 0) (ix 0))]) _
  refine wp_app (by simp) (wp_suspend ?_)
  fx_post
  fx_catch
  rw [show (ix 0 : LabelIdx).toNat = 0 from rfl]
  refine ⟨[], _, rfl, rfl, ?_⟩
  simp only [List.map_nil, List.append_nil]
  refine wp_val ?_
  fx_post
  -- resume A with B
  show WP _ _ _ _ _ wF (fvals [] ++ (fvals [.cont 1, .cont 3] ++ [.block btR _]) ++ []) _
  refine wp_block [] [] rfl rfl ?_
  refine wp_label ?_
  show WP _ _ _ _ _ wF (fvals [.cont 1] ++ [.contRef 3, .fx (.resume (ix 0) [.onSwitch (ix 0)])]) _
  fx_resume
  show WP _ _ _ _ _ wF [.frame 1 wF [.label 1 [] (fvals [] ++ [.contRef 1, .fx (.switch (ix 0) (ix 0))])]] _
  refine wp_frame (wp_label (wp_switch ?_))
  fx_post
  refine Or.inl ⟨_, _, _, rfl, rfl, by simp [CtxV.Handles], rfl, ?_⟩
  refine wp_handler ?_
  show WP _ _ _ _ _ wF [.frame 1 wF [.label 1 [] (fvals [] ++ [.contRef 4, .core (.plain .drop)] ++
    [.core (.plain (.intConst .i32 42)), .core (.plain .nop)])]] _
  refine wp_frame (wp_label (wp_dropCont [] _ ?_))
  show WP _ _ _ _ _ wF (fvals [] ++ (fvals (liftV [Val.i32 42]) ++
    [Instr.nop].map fun i => .core (.plain i)) ++ []) _
  fx_exec
  show WP _ _ _ _ _ wF (fvals [.val (Val.i32 42)]) _
  refine wp_val ?_
  fx_post
  exact ⟨rfl, rfl, rfl⟩

/-- **A run of the switch program returns `42`**, at every profile and host relation. -/
theorem switch_mem : Behaviour.returns [Val.i32 42] ∈ behavioursFX' P host swFx switchProg :=
  WP.behaviour (r := .values [Val.i32 42]) switch_wp

end Silmaril.Proofs.Wasm.FX.Examples.EveryRun
