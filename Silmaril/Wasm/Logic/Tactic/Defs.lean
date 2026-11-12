module

public import Silmaril.Wasm.Logic.Core.Thms
import Std.Tactic.BVDecide

/-!
# Tactics for Wasm program proofs

Each tactic applies one rule of the `WP` calculus to the goal as it stands and
leaves the program-specific obligations:

* `wasm_step` — **symbolic execution** of the straight-line code at the head of
  the goal: applies `wp_exec` (or one of its variants) and evaluates `exec` with
  `simp`, leaving the `WP` of the rest of the code with the new store, frame and
  stack. Optional lemmas (`wasm_step [h₁, h₂]`) are passed to `simp`, typically
  `Memory.load`/`Memory.store` facts (`load_eq`, `store_eq`) for the accesses.
* `wasm_block` — `wp_block_cons`: enter a block whose type is computed by `rfl`.
* `wasm_loop Inv` — `wp_loop_cons` with the invariant `Inv` (indexed by a
  measure): leaves the block-type obligation, the invariant-preservation goal and
  the initial invariant.
* `wasm_if` — `wp_if_bool32_cons`: a conditional on a comparison result.
* `wasm_br_if` — `wp_brIf_bool32`: a conditional branch on a comparison result,
  leaving an `if b then … else …` goal.
* `wasm_mem` — bounds and disjointness of regions: unfolds `Region` and closes
  the goal by `omega`.
* `wasm_arith` — integer instructions as `BitVec` operations, then `simp`,
  `bv_normalize` or `omega` (no SAT call, so no `Lean.ofReduceBool` axiom).
* `wasm_try_table` — `wp_tryTable_cons`: enter a `try_table` (Wasm 3.0).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Core

/-- Symbolic execution of the straight-line code at the head of a `WP` goal. -/
syntax "wasm_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| wasm_step) => `(tactic| wasm_step [])
  | `(tactic| wasm_step [$ls,*]) => `(tactic|
      ((first
        | refine wp_exec_all ?_
        | refine wp_exec_vals ?_
        | refine wp_exec₀ ?_
        | refine wp_exec ?_) <;>
       simp only [exec_cons, exec_nil, exec1, popInt, popV, localVal?,
         Silmaril.Wasm.Execution.Core.Frame.local?, Silmaril.Wasm.Execution.Core.Frame.setLocal,
         Silmaril.Wasm.Execution.Core.Val.i32, Silmaril.Wasm.Execution.Core.Val.i64,
         toOption_except_ok, Option.map_some, Option.bind_some,
         BitVec.ofNat_eq_ofNat, ofNat_i32_width, ofNat_i64_width, setWidth_i32_width,
         setWidth_i64_width, BitVec.toNat_ofNat,
         List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
         List.length_cons, List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
         List.set_cons_zero, List.set_cons_succ,
         intBinOp_i32_add, intBinOp_i32_sub, intBinOp_i32_mul, intBinOp_i32_and,
         intBinOp_i32_or, intBinOp_i32_xor, intBinOp_i32_shl, intBinOp_i32_shrU,
         intBinOp_i32_rotl, intBinOp_i32_rotr,
         intBinOp_i64_add, intBinOp_i64_sub, intBinOp_i64_mul, intBinOp_i64_and,
         intBinOp_i64_or, intBinOp_i64_xor, intBinOp_i64_shl, intBinOp_i64_shrU,
         intBinOp_i64_rotl, intBinOp_i64_rotr, $ls,*]))

/-- Enter a block (`wp_block_cons`); the block type is computed by `rfl`. -/
macro "wasm_block" : tactic =>
  `(tactic| refine wp_block_cons (by rfl) (by rfl) ?_)

/-- Enter a `try_table` (`wp_tryTable_cons`); the block type is computed by `rfl`. -/
macro "wasm_try_table" : tactic =>
  `(tactic| refine wp_tryTable_cons (by rfl) (by rfl) ?_)

/-- Enter a loop with the invariant `Inv` (`wp_loop_cons`). -/
macro "wasm_loop " inv:term : tactic =>
  `(tactic| refine wp_loop_cons $inv ?_ ?_ ?_)

/-- A conditional on a comparison result (`wp_if_bool32_cons`). -/
macro "wasm_if" : tactic =>
  `(tactic| refine wp_if_bool32_cons ?_)

/-- A conditional branch on a comparison result (`wp_brIf_bool32`). -/
macro "wasm_br_if" : tactic =>
  `(tactic| refine wp_brIf_bool32 ?_)

/-- Bounds and disjointness of memory regions: linear arithmetic on addresses. -/
macro "wasm_mem" : tactic =>
  `(tactic| ((try simp only [Region.Disjoint, Region.InBounds, Region.Contains,
    Region.stop] at *); omega))

/-- Integer instructions as `BitVec` operations, then `simp`'s `BitVec` lemmas,
`bv_decide`'s normalization pass (`bv_normalize`, no SAT call, no axiom) or
`omega`. -/
macro "wasm_arith" : tactic =>
  `(tactic| ((try simp only [intBinOp_i32_add, intBinOp_i32_sub, intBinOp_i32_mul,
      intBinOp_i32_and, intBinOp_i32_or, intBinOp_i32_xor, intBinOp_i32_shl, intBinOp_i32_shrU,
      intBinOp_i32_rotl, intBinOp_i32_rotr, intBinOp_i64_add, intBinOp_i64_sub,
      intBinOp_i64_mul, intBinOp_i64_and, intBinOp_i64_or, intBinOp_i64_xor, intBinOp_i64_shl,
      intBinOp_i64_shrU, intBinOp_i64_rotl,
      intBinOp_i64_rotr] at *); first | (simp; done) | bv_normalize | omega))

end Silmaril.Wasm.Logic.Core
