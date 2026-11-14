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
2. **Nested sequences and edges** (next).
   - Nodes are the segments of every sequence of the body tree (bodies of `block`, `loop`, `if`
     arms and `try_table`).
   - Edges are given declaratively by the structured-control rules used above: label depth resolved
     against the enclosing constructs, and a sequence's end continuing to its parent's continuation.
   - Special nodes stay explicit: `exit`, `trap`, `raise`, `invalid`, and *unsupported* markings for
     constructs the relation does not model exactly.
   - To prove: the relation determines a unique graph on the canonical node identities, and the
     executable and kernel-evaluated builders realize it. Kernel evaluation is to be benchmarked
     against runtime evaluation.
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
