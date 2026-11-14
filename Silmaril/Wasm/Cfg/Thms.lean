module

public import Silmaril.Wasm.Cfg.Examples.Defs

@[expose] public section

/-!
# Control-flow graphs of Wasm functions: checked examples

CHECKED BY THE KERNEL (`decide +kernel`, standard axioms): the extracted CFGs of the example
functions of `Silmaril.Wasm.Cfg.Examples` are exactly the edge lists below, and their immediate
dominators are as stated. Each is checked against the rules of `Silmaril.Wasm.Cfg` by hand in
the comments.

NOT YET PROVED: a general theorem relating `ofExpr` to an operational semantics of structured
control (the next milestone; see `docs/projects/wasm-cfg.md`). These are kernel-checked facts
about specific extractions, not a correctness proof of the extractor.
-/

namespace Silmaril.Wasm.Cfg.Examples

open Silmaril.Wasm Silmaril.Wasm.Cfg

/-- `sum`: node 5 `block $done` → 6 `loop $next`; 16 `br_if $done` → 4 (after the block) and
15 (the next instruction); 7 `br $next` → 6 (the loop); 4 `local.get $acc` → 0 (exit). -/
theorem sum_edges : (ofExpr sum).edges =
    [(4, 0), (5, 6), (6, 19), (7, 6), (8, 7), (9, 8), (10, 9), (11, 10), (12, 11), (13, 12),
     (14, 13), (15, 14), (16, 4), (16, 15), (17, 16), (18, 17), (19, 18)] := by decide +kernel

/-- The only way out of the loop is the `br_if`: it immediately dominates the block's exit. -/
theorem sum_idom_after_loop : (ofExpr sum).graph.idom 4 = some 16 := by decide +kernel

/-- `dispatch`: the `br_table $a $b $c` (node 12) goes to the continuations of the three blocks,
nodes 10, 7 and 4 (its default is `$c`, already listed). -/
theorem dispatch_edges : (ofExpr dispatch).edges =
    [(4, 0), (5, 8), (6, 0), (7, 6), (8, 11), (9, 0), (10, 9), (11, 13), (12, 10), (12, 7),
     (12, 4), (13, 12)] := by decide +kernel

theorem dispatch_br_table_targets : (ofExpr dispatch).graph.succ 12 = [10, 7, 4] := by
  decide +kernel

/-- `edges`: `unreachable` (node 10) → `trap` (1); `throw` (6) → `raise` (2); `return` (4) →
`exit` (0); each `if` → its then-arm and the next instruction. -/
theorem specials_edges : (ofExpr specials).edges =
    [(4, 0), (5, 6), (5, 4), (6, 2), (7, 5), (8, 7), (9, 10), (9, 8), (10, 1), (11, 9)] := by
  decide +kernel

/-- A branch to a missing label goes to `invalid` (3). -/
theorem badBranch_edges : (ofExpr badBranch).edges = [(4, 5), (5, 3)] := by decide +kernel

/-- The compiled Rust `enter` has 46 nodes (42 instructions and the four special nodes). -/
theorem doorEnter_size : (ofExpr doorEnter).graph.size = 46 := by decide +kernel

end Silmaril.Wasm.Cfg.Examples
