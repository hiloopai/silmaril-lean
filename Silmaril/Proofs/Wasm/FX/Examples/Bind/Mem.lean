module

public import Silmaril.Wasm.FX.Examples.Bind.Defs
public import Silmaril.Wasm.FX.Logic.Thms
public import Silmaril.Wasm.FX.Logic.Tactic.Defs

/-!
# The `cont.bind` program: a run, by the existential WasmFX calculus

`bind_mem`: `bindProg` has a `StepFX'` run that returns `[42]`, at every profile and host
relation (bind the argument `2`, resume with no further arguments), proved with the
weakest-precondition calculus of `Silmaril.Wasm.FX.Logic`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.Bind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXAsyncFX (ix)
open Silmaril.Wasm.FX.Logic
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {host : HostSemantics Nat}

/-- The postcondition of the run: the result `[42]`. -/
abbrev bindR : PostFX Nat := fun _ _ _ o => o = .ofResult (.values [Val.i32 42])

theorem bind_wp :
    WP P host bdFx bdStore [] ⟨[], bdM⟩ [.core (.plain (.call (ix 1)))] bindR := by
  show WP P host bdFx bdStore [] _ (fvals [] ++ [Admin.plain (.call (ix 1))].map .core ++ []) _
  refine wp_coreStep [] [] (Step.call (a := 1) rfl rfl) ?_
  show WP P host bdFx bdStore [] _ (cvals [] ++ [.core (.ref (.func 1)), .core (.callRefType bdT)]) _
  fx_call
  show WP _ _ _ _ [] _ (fvals [.val (Val.i32 2)] ++ [.core (.plain (.refFunc (ix 0)))] ++
    [.fx (.contNew (ix 0)), .fx (.contBind (ix 0) (ix 2)), .fx (.resume (ix 2) [])]) _
  refine wp_refFunc _ _ rfl ?_
  show WP _ _ _ _ [] _ (fvals [.val (Val.i32 2)] ++ [.core (.ref (.func 0)), .fx (.contNew (ix 0))] ++
    [.fx (.contBind (ix 0) (ix 2)), .fx (.resume (ix 2) [])]) _
  refine wp_contNew _ _ rfl ?_
  show WP _ _ _ _ _ _ (fvals [] ++ (fvals [.val (Val.i32 2)] ++
    [.contRef 0, .fx (.contBind (ix 0) (ix 2))]) ++ [.fx (.resume (ix 2) [])]) _
  refine wp_contBind [] _ rfl ?_
  show WP _ _ _ _ _ _ (fvals [] ++ [.contRef 1, .fx (.resume (ix 2) [])]) _
  refine wp_resume_handle (C := bindCont (newCont 0 ⟨kitTypes.head!, bdM, .host 0⟩)
    [.val (Val.i32 2)]) (by simp) rfl ?_
  show WP _ _ _ _ _ _ (cvals [Val.i32 2] ++ [.core (.ref (.func 0)), .core (.callRefType _)]) _
  fx_call
  show WP _ _ _ _ _ _ (fvals [] ++ (fvals (liftV []) ++
    [Instr.localGet (ix 0), .intConst .i32 40, .intBinOp .i32 .add].map fun i => .core (.plain i)) ++ []) _
  fx_exec
  show WP _ _ _ _ _ _ (fvals [.val (Val.i32 42)]) _
  refine wp_val ?_
  fx_post
  exact ⟨rfl, rfl, rfl⟩

/-- **A run of the `cont.bind` program returns `42`**, at every profile and host relation. -/
theorem bind_mem : Behaviour.returns [Val.i32 42] ∈ behavioursFX' P host bdFx bindProg :=
  WP.behaviour (r := .values [Val.i32 42]) bind_wp

end Silmaril.Proofs.Wasm.FX.Examples.Bind
