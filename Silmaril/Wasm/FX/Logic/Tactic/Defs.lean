module

public import Silmaril.Wasm.FX.Logic.Thms

/-!
# Tactics for WasmFX program proofs

Each tactic applies one rule of the WasmFX calculus (`Silmaril.Wasm.FX.Logic`) and leaves the
program-specific obligations. The code at the head of the goal is put into the shape a rule
expects (`fvals us ++ c ++ rest`) by a `show`, which is checked by definitional unfolding.

* `fx_exec` — **symbolic execution** of straight-line Core code (`wp_exec`): the generalization
  of `wasm_step` (`Silmaril.Wasm.Logic.Tactic`) to FX code; it evaluates the Core calculus's
  interpreter `exec` with the same `simp` set (copied from `wasm_step`), leaving the `WP` of
  the rest of the FX code. Optional lemmas: `fx_exec [h₁, h₂]`;
* `fx_post` — unfold the context postconditions (`seqPost`, `labelPost`, `framePost`,
  `handlerPost`, `corePost`) at a concrete outcome;
* `fx_block` — enter a block (`wp_block_enter`), the block type computed by `rfl`;
* `fx_call` — call an FX function through `call_ref` (`wp_call_fx`), all side conditions by
  `rfl`;
* `fx_resume` — the effect-handler rule for `resume` (`wp_resume_handle`): the continuation slot
  and the handler clauses resolved by `rfl`;
* `fx_catch` — a `suspend` caught by a clause `(on x l)` of the handler (the first disjunct of
  `handlerPost`): tag resolution and the clause by `rfl`, "no inner handler" by `simp`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic

/-- Symbolic execution of straight-line Core code at the head of an FX `WP` goal. -/
syntax "fx_exec" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| fx_exec) => `(tactic| fx_exec [])
  | `(tactic| fx_exec [$ls,*]) => `(tactic|
      (refine wp_exec _ _ ?_ <;>
       simp only [Silmaril.Wasm.Logic.Core.exec_cons, Silmaril.Wasm.Logic.Core.exec_nil,
         Silmaril.Wasm.Logic.Core.exec1, Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV,
         Silmaril.Wasm.Logic.Core.localVal?,
         Silmaril.Wasm.Execution.Core.Frame.local?, Silmaril.Wasm.Execution.Core.Frame.setLocal,
         Silmaril.Wasm.Execution.Core.Val.i32, Silmaril.Wasm.Execution.Core.Val.i64,
         Silmaril.Wasm.Logic.Core.toOption_except_ok, Option.map_some, Option.bind_some,
         BitVec.ofNat_eq_ofNat, Silmaril.Wasm.Logic.Core.ofNat_i32_width,
         Silmaril.Wasm.Logic.Core.ofNat_i64_width, Silmaril.Wasm.Logic.Core.setWidth_i32_width,
         Silmaril.Wasm.Logic.Core.setWidth_i64_width, BitVec.toNat_ofNat,
         List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
         List.length_cons, List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
         List.set_cons_zero, List.set_cons_succ,
         Silmaril.Wasm.Logic.Core.intBinOp_i32_add, Silmaril.Wasm.Logic.Core.intBinOp_i32_sub,
         Silmaril.Wasm.Logic.Core.intBinOp_i32_mul, Silmaril.Wasm.Logic.Core.intBinOp_i32_and,
         Silmaril.Wasm.Logic.Core.intBinOp_i32_or, Silmaril.Wasm.Logic.Core.intBinOp_i32_xor,
         Silmaril.Wasm.Logic.Core.intBinOp_i32_shl, Silmaril.Wasm.Logic.Core.intBinOp_i32_shrU,
         Silmaril.Wasm.Logic.Core.intBinOp_i32_rotl, Silmaril.Wasm.Logic.Core.intBinOp_i32_rotr,
         Silmaril.Wasm.Logic.Core.intBinOp_i64_add, Silmaril.Wasm.Logic.Core.intBinOp_i64_sub,
         Silmaril.Wasm.Logic.Core.intBinOp_i64_mul, Silmaril.Wasm.Logic.Core.intBinOp_i64_and,
         Silmaril.Wasm.Logic.Core.intBinOp_i64_or, Silmaril.Wasm.Logic.Core.intBinOp_i64_xor,
         Silmaril.Wasm.Logic.Core.intBinOp_i64_shl, Silmaril.Wasm.Logic.Core.intBinOp_i64_shrU,
         Silmaril.Wasm.Logic.Core.intBinOp_i64_rotl, Silmaril.Wasm.Logic.Core.intBinOp_i64_rotr,
         Silmaril.Wasm.Models.FXV.liftV, List.map_cons, List.map_nil, $ls,*]))

/-- Unfold the context postconditions at a concrete outcome. -/
macro "fx_post" : tactic =>
  `(tactic| simp only [seqPost, labelPost, framePost, handlerPost, corePost,
    OutcomeFX.ofResult, List.nil_append, List.append_nil])

/-- Enter a block (`wp_block_enter`); the block type is computed by `rfl`. -/
macro "fx_block" : tactic =>
  `(tactic| refine wp_block_enter (by rfl) (by rfl) ?_)

/-- Call an FX function (`wp_call_fx`). -/
macro "fx_call" : tactic =>
  `(tactic| refine wp_call_fx trivial (by rfl) (by rfl) (by rfl) (by rfl) ?_)

/-- The effect-handler rule for `resume` (`wp_resume_handle`). -/
macro "fx_resume" : tactic =>
  `(tactic| refine wp_resume_handle (by rfl) (by rfl) ?_)

/-- A `suspend` caught by an `(on x l)` clause of the handler. -/
macro "fx_catch" : tactic =>
  `(tactic| refine Or.inl ⟨_, _, _, by rfl,
    by simp only [Silmaril.Wasm.Models.FXV.CtxV.Handles, not_false_eq_true, or_false], by rfl, ?_⟩)

end Silmaril.Wasm.FX.Logic
