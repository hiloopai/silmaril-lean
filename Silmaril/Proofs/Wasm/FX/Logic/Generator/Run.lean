module

public import Silmaril.Wasm.FX.Logic.Generator.Defs
public import Silmaril.Wasm.FX.Logic.Tactic.Defs

/-!
# The one-shot generator, proved with the WasmFX calculus

The proof follows the program: enter the block, make the continuation, resume it under the
handler (`fx_resume`), call `gen` (`fx_call`), reach `suspend $yield` (`wp_suspend`), catch it
(`fx_catch`: the branch to `$on_yield` with `1` and the new continuation), leave the block,
resume the rest (`fx_resume` again, no handler clauses), return `2` through the frame and the
handler, and add (`fx_exec`, the FX form of `wasm_step`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.Generator

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {host : HostSemantics Nat}

/-- The postcondition: the result `[3]`. -/
abbrev genQ : PostFX Nat := fun _ _ _ o => o = .ofResult (.values [Val.i32 3])

/-- The frame of `gen`. -/
abbrev genFg : Frame := Frame.forCall genM [] []

/-- The context captured by `suspend $yield`: the rest of `gen`'s body, in its label and frame. -/
abbrev genE : CtxV :=
  .frame 1 genFg (.label 1 [] (.seq [] .hole [.core (.plain (.intConst .i32 2))]))

/-- The end: `1 + 2`. -/
theorem gen_add (K : Conts) :
    WP P host genFx genStore K genF0
      (fvals [.val (Val.i32 1), .val (Val.i32 2)] ++ [.core (.plain (.intBinOp .i32 .add))])
      genQ := by
  show WP P host genFx genStore K genF0
    (fvals [] ++ (fvals (liftV [Val.i32 1, Val.i32 2]) ++
      [Instr.intBinOp .i32 .add].map fun i => .core (.plain i)) ++ []) genQ
  fx_exec
  exact wp_ends (.normal [.val (.num ⟨.int .i32, 1#32 + 2#32⟩)]) rfl rfl

/-- After the yield: resume the rest of `gen`, which returns `2`, and add. -/
theorem gen_rest (K : Conts) (hK : K[1]? = some (some ⟨genE.plug⟩)) :
    WP P host genFx genStore K genF0
      (fvals [.val (Val.i32 1), .cont 1] ++
        [.fx (.resume (ix 0) []), .core (.plain (.intBinOp .i32 .add))]) genQ := by
  show WP P host genFx genStore K genF0
    (fvals [.val (Val.i32 1)] ++ (fvals [] ++ [.contRef 1, .fx (.resume (ix 0) [])]) ++
      [.core (.plain (.intBinOp .i32 .add))]) genQ
  refine wp_seq (Or.inl (by simp)) ?_
  refine wp_resume_handle hK rfl ?_
  show WP P host genFx genStore (K.set 1 none) genF0
    [.frame 1 genFg [.label 1 [] (fvals [.val (Val.i32 2)])]] _
  refine wp_frame (wp_label (wp_val ?_))
  exact ⟨rfl, gen_add _⟩

/-- The instance of `gen`. -/
abbrev genFi : FuncInst Nat := ⟨genTypes.head!, genM, .host 0⟩

/-- The postcondition of the block `$on_yield`'s body, from inside the handler. -/
abbrev blockQ : PostFX Nat :=
  seqPost P host genFx [] [.core (.plain .unreachable)]
    (labelPost P host genFx 2 []
      (seqPost P host genFx [] [.fx (.resume (ix 0) []), .core (.plain (.intBinOp .i32 .add))]
        genQ))

/-- Inside the handler: call `gen`, which yields `1`; the handler catches the yield. -/
theorem gen_yield :
    WP P host genFx genStore [none] genF0
      [.core (.ref (.func 0)), .core (.callRefType genFi.type)]
      (handlerPost P host genFx [.onLabel 0 (ix 0)] (blockQ (P := P) (host := host))) := by
  show WP P host genFx genStore [none] genF0
    (cvals [] ++ [.core (.ref (.func 0)), .core (.callRefType genFi.type)]) _
  fx_call
  show WP P host genFx genStore [none] genFg
    (fvals [] ++ (fvals [.val (Val.i32 1)] ++ [.fx (.suspend (ix 0))]) ++
      [.core (.plain (.intConst .i32 2))]) _
  refine wp_seq (Or.inr (by simp)) (wp_suspend ?_)
  show handlerPost P host genFx [.onLabel 0 (ix 0)] blockQ genStore [none] genF0
    (.susp genE [.val (Val.i32 1)] (ix 0))
  fx_catch
  show labelPost P host genFx 2 [] _ genStore [none, some ⟨genE.plug⟩] genF0
    (.br 0 [.val (Val.i32 1), .cont 1])
  exact ⟨[], _, rfl, rfl, wp_val (vs := [.val (Val.i32 1), .cont 1]) (gen_rest _ rfl)⟩

/-- **The generator's run**: `main` returns `1 + 2`. -/
theorem gen_main :
    WP P host genFx genStore [] genF0 (mainBody.map InstrFX.toAdmin) genQ := by
  show WP P host genFx genStore [] genF0
    ([.block (.typeIdx (ix 1)) _] ++
      [.fx (.resume (ix 0) []), .core (.plain (.intBinOp .i32 .add))]) genQ
  refine wp_app (by simp) ?_
  show WP P host genFx genStore [] genF0 (fvals [] ++ [.block (.typeIdx (ix 1)) _]) _
  fx_block
  show WP P host genFx genStore [] genF0
    (fvals [] ++ [.core (.plain (.refFunc (ix 0)))] ++
      [.fx (.contNew (ix 0)), .fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)]),
        .core (.plain .unreachable)]) _
  refine wp_refFunc [] _ rfl ?_
  show WP P host genFx genStore [] genF0
    (fvals [] ++ [.core (.ref (.func 0)), .fx (.contNew (ix 0))] ++
      [.fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)]), .core (.plain .unreachable)]) _
  refine wp_contNew [] _ rfl ?_
  show WP P host genFx genStore [some (newCont 0 genFi)] genF0
    (fvals [] ++ (fvals [] ++ [.contRef 0, .fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)])]) ++
      [.core (.plain .unreachable)]) _
  refine wp_seq (Or.inr (by simp)) ?_
  fx_resume
  exact gen_yield

/-- **The generator returns `3`** under `StepFX'`, for every profile and host relation. -/
theorem gen_behaviour :
    (Result.values [Val.i32 3]).toBehaviour ∈
      behavioursFX' P host genFx ⟨genStore, [], genF0, mainBody.map InstrFX.toAdmin⟩ :=
  WP.behaviour gen_main

end Silmaril.Wasm.FX.Logic.Generator
