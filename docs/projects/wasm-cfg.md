# Control-flow graphs of Wasm functions (`Silmaril.Wasm.Cfg`)

`Cfg.ofExpr`/`ofFunc` extracts the instruction-level CFG of a function body (structured control)
as a `Silmaril.Machine.Graph.Digraph`. This is the rooted-graph type whose dominators and dominator
trees `Silmaril.Automata.Graph` analyses, and which state machines use too.

## What is extracted

- One node per instruction occurrence, named by its path through nested bodies, plus the special
  nodes `exit` (0), `trap` (1), `raise` (2) and `invalid` (3).
- Edges follow the structured-control rules, with branch targets resolved syntactically by label
  depth:
  - `block`'s label is its continuation, and `loop`'s label is the loop itself;
  - `if` goes to both arms;
  - `br`, `br_if` and the `br_on_*` forms go to their label's target, and the conditional ones also
    go to the next instruction;
  - `br_table` goes to every listed target and to its default;
  - `return` and tail calls go to `exit`;
  - `unreachable` goes to `trap`;
  - `throw` goes to `raise`;
  - a missing label goes to `invalid`.

## Stated approximations

- **Exceptions.** An exception's handler is not resolved: `throw` goes to `raise`. `try_table`
  links to every catch target, which over-approximates.
- **Run-time traps.** Instructions that may trap at run time (division, memory, casts) and calls
  whose callee may trap or throw get no trap edge.
- **Calls.** Calls continue to the next instruction. The call graph is separate and not done yet;
  so is resolving `call_indirect` targets.

## Evidence

`Silmaril.Wasm.Cfg.Thms` checks the extractions of example functions in the kernel (exact edge
lists and dominators):

- `sum` of `Examples.Verified.prog`: a loop in a block. Its `br_if` is the immediate dominator of
  the block's exit.
- A `br_table` dispatcher: its targets are the continuations of the three blocks.
- `unreachable` / `throw` / `return` go to the special nodes.
- A missing label goes to `invalid`.
- The compiled Rust `enter` of `Examples.RustInst.door`.

**Not proved yet:** a general theorem relating `ofExpr` to an operational semantics of structured
control. That is the next milestone; the facts above are checked extractions, not a proof that the
extractor is correct.

## In the explorer

`silmaril/machines/wasm-cfg.toml` holds these CFGs as machine documents, written by
`ProjectSelfTest.WasmCfg.cfgDoc`. The `*_extracted` theorems prove in the kernel that each
document has exactly the extraction's nodes and edges.

The registry proves each document's immediate-dominator table. The explorer's machine page
(Machines → `silmaril.wasm.cfg.*`) shows the flat CFG and its Lean kernel-checked dominator tree.

## Roadmap: basic-block CFG relation

The instruction-level extractor above is a prototype. The target is a **relation** from a Wasm
function to a CFG whose nodes are basic blocks, with proofs that it is a function (existence and
uniqueness) and that the executable extractors realize it.

**Decisions so far:**

1. **Canonical partition** (`Silmaril.Wasm.Cfg.Block`, done).
   - *Terminators* are the structured instructions (`block`, `loop`, `if`, `try_table`), the
     branches (`br`, `br_if`, `br_table`, `br_on_*`), `return` and tail calls, `unreachable` and
     `throw`/`throw_ref`.
   - Calls are *simple*: their trap or throw exits are marked on the node, not made separate edges.
   - A segment is simple instructions followed by at most one terminator.
   - `IsSegmentation` is the relation: nonempty segments covering the sequence, where only the last
     may lack a terminator.
   - **Proved:** every sequence has exactly one segmentation (`existsUnique_segmentation`), and
     `segment` computes it.
   - A block's identity is (sequence path, position in the segmentation).
2. **Nested sequences and edges** (`Silmaril.Wasm.Cfg.BlockTree`, `Silmaril.Wasm.Cfg.BlockCfg`,
   done except the benchmark).
   - Nodes are the segments of every sequence of the body tree (bodies of `block`, `loop`, `if`
     arms and `try_table`). A `BlockId` is a sequence path of `(segment, arm)` steps plus a
     position. `lookup body b` names the block declaratively, through the canonical segmentations.
     **Proved:** `blocks` lists exactly the graph of `lookup` (`mem_blocks`).
   - Edges are given declaratively from `lookup` (`succOf`, `Edge`):
     - `entry` gives the block at a position, or else the sequence's continuation.
     - A nested sequence continues at its parent's next position; the body continues to `exit`.
     - `loop` labels go to the loop body's entry; other labels go to the continuation.
     - Branches resolve by depth; the outermost label is `exit`.
     - `try_table` has an edge to each catch label, resolved outside it.
   - Special nodes stay explicit: `exit`, `trap`, `raise`, `invalid`. Traps of ordinary
     instructions and throws inside a `try_table` body are not edges: the `try_table` block's
     catch edges stand for them.
   - **Proved:** the one-pass builder `blockCfg` realizes `Edge` (`blockCfg_eq`, `edge_iff`), and
     each block has exactly one successor list (`existsUnique_succ`). Kernel-checked examples:
     `sum_blockCfg`, `dispatch_br_table_edges` (`decide +kernel`, a few seconds).
   - Kernel against runtime evaluation: measured, see *Benchmark* below.
   - On the explorer: `silmaril/machines/wasm-block-cfg.toml` holds the block CFGs of `sum`,
     `dispatch`, `specials` and the Rust door's `enter`, as machine documents
     (`silmaril.wasm.blockcfg.*`), each with its kernel-checked dominator table.
     `ProjectSelfTest.WasmBlockCfg.*_blocks` proves that each document has exactly the builder's
     nodes, edges and entry, by node index. The instruction-level documents
     (`silmaril.wasm.cfg.*`) stay alongside for comparison.
3. **Node interfaces.**
   - Each block will carry its operand-stack input and output arity.
   - Branch arguments are the label arity from the block type.
   - Each block lists its trap and throw exits and the local, global and function indices it
     references.
   - The arities come from the existing validation typing, scoped to functions that validate.
4. **Bytes**, valid serializer profile only (`encodeModule?`).
   - A standalone function object is (locals, body).
   - Its *body encoding* is the locals vector, then the expression, then `end` (`0x0b`).
   - Its *code entry* is the body encoding with a u32 size prefix.
   - The code section lists entries in the order of defined functions; module function index `k`
     is `#imports + defined index`.
   - A block's bytes are its simple instructions followed by its terminator's header (opcode and
     block type). The nested sequences' bytes belong to their own blocks; the `else` and `end`
     delimiters are attributed to the end of their sequence.
   - To prove: the code entry of defined function `k` occurs in the module's bytes at the offset the
     encoder places it.
5. **Equivalences.**
   - Graph equivalence is an isomorphism of block CFGs that preserves block contents.
   - Dominator-tree equivalence goes through the exact dominator tree, which is unique on reachable
     nodes (`Graph.exact_unique`). So it does not depend on choosing a tree, unlike sound or region
     trees.
   - Behavioral equivalence (function to CFG injective up to equivalence: semantics preserved and
     reflected) needs the abstract environment and trace semantics owned by the Wasm games/traces
     work. This development reuses that, and does not port a second semantics.

## Benchmark: kernel against runtime evaluation of `blockCfg`

Method:
- Each case is one file importing `Silmaril.Wasm.Cfg.BlockCfg.Thms`, run with `lake env lean`.
- *Runtime* is `#eval (blockCfg body).length`; *kernel* is
  `theorem : (blockCfg body).length = n := by decide +kernel`.
- Wall time minus the 3.0 s import-only baseline. One run per case on a 2-core container,
  toolchain `nightly-2026-11-05`. Run-to-run variation of the whole process was about 0.3 s, so
  smaller differences are not resolved.

Bodies:
- `synth d` nests `d` loops, each level `local.get 0; br_if 1; loop … br 0 end; nop`
  (`3d + 1` blocks, nesting depth `d`).
- `flat w` is `w` copies of `local.get 0; br_if 0` at the top level (`w` blocks, depth 0).

| body | blocks | runtime | kernel |
|------|-------:|--------:|-------:|
| `synth 10` | 31 | not resolved | not resolved |
| `synth 50` | 151 | not resolved | not resolved |
| `synth 200` | 601 | not resolved | 2.3 s |
| `synth 400` | 1201 | not resolved | 9.7 s |
| `synth 800` | 2401 | not resolved | 57 s |
| `flat 1000` | 1000 | not resolved | 0.4 s (near resolution) |
| `flat 4000` | 4000 | not resolved | 1.7 s |

Reading (these single runs only; no general complexity claim):
- *Runtime:* every `#eval` run finished within the baseline's run-to-run variation. That is a
  measurement-resolution statement about these cases, not a time bound.
- *Kernel, nesting:* checking time is sensitive to nesting depth. Doubling the depth from 200 to
  400 multiplied it by about 4.2 (2.3 s to 9.7 s), and from 400 to 800 by about 5.9 (9.7 s to
  57 s). Three points from one run each do not fix a growth rate.
- *Kernel, flat:* for the flat family, 4000 blocks took 1.7 s.
- Each nested block's identity carries its full path, which is a plausible source of the depth
  sensitivity; this was not profiled.
- These two synthetic families say nothing measured about other function shapes.
