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
