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
   - Special nodes stay explicit: `exit`, `trap`, `raise`, `invalid`.
   - **Proved:**
     - the one-pass builder `blockCfg` realizes `Edge` (`blockCfg_eq`, `edge_iff`);
     - each block has exactly one successor list (`existsUnique_succ`);
     - block identities are distinct (`blocks_ids_nodup`, `blockCfg_ids_nodup`).
   - Kernel-checked examples: `sum_blockCfg`, `dispatch_br_table_edges` (`decide +kernel`, a
     few seconds).
   - **Scope: syntactic and incomplete.** `Edge` is the structured-control reading of the
     instruction tree. It is not derived from, or proved against, the Core 3.0 semantics; no
     theorem says that executions follow it. That correspondence is the operational bridge
     (behavioral equivalence, item 5 below).
   - **Effect marks and effect edges** (`blockEffects`, `effectSucc`, `EffectEdge`). These are
     syntactic and conservative ("may"). They keep the control edges from looking complete
     where other instructions may leave the block:
     - `mayTrap`: division and remainder, `trunc`, memory and table accesses, null and cast
       checks, array operations. Effect edge to `trap`.
     - `call`: direct, indirect and reference calls, including tail calls. Effect edges to
       `trap` and `raise`, because the callee may trap, raise or not return.
     - `unresolvedHandler`: a block inside a `try_table` body that calls or throws. Its exception
       may be caught by an enclosing `try_table`, and the graph does not resolve which handler.
       Its `throw` flow edge still goes to `raise`.
     - Kernel-checked example: `guarded_effects`, `guarded_effect_edges`.
   - Kernel against runtime evaluation: measured, see *Benchmark* below.
   - On the explorer: `silmaril/machines/wasm-block-cfg.toml` holds the block CFGs of `sum`,
     `dispatch`, `specials` and the Rust door's `enter`, as machine documents
     (`silmaril.wasm.blockcfg.*`), each with its kernel-checked dominator table. There is also
     `guarded`, which has effects. Edges are labelled `flow` or `effect`, and blocks carry their
     effect marks.
   - Each document's description, and the explorer's dominator caption, say the graph is
     syntactic and incomplete: the dominator theorem is a fact about the drawn graph, not about
     execution.
     `ProjectSelfTest.WasmBlockCfg.*_blocks` proves that each document has exactly the builder's
     nodes, edges and entry, by node index. The instruction-level documents
     (`silmaril.wasm.cfg.*`) stay alongside for comparison.
3. **Node interfaces**, relative to a fixed module environment.
   - **The environment is not part of a body.** Every interface is under a `Validation.Context`
     built as `checkModule?` builds it (`moduleCtx`: types, funcs, globals, tables, mems, tags,
     elems, datas). A body never carries it.
   - **Body interface:** `(params, locals, results)` under that context, as in
     `Context.funcBody`.
   - **Block interface:** the label stack (`withLabel` along the block's path), the local
     initialisation state, and the operand stack in and out of the block's own frame.
   - This is shared with the abstract typed-body work (`docs/projects/component-semantics.md`),
     so there is one notion of interface.
   - **Local values are not in the context.** The context holds the local *types* and their
     initialisation state. Local values belong to the activation frame of a run, apart from the
     module store, as the abstract typed-body interface also has it.
   - **Done** (`Silmaril.Wasm.Cfg.BlockTyping`): `bodyIfaces C body` records each block's
     interface: static context, instructions, stack in → out, and local initialisations.
     `bodyIfaces_typed` proves that every recorded interface is an `Instrs_ok` derivation.
     `bodyIfaces_lookup` proves that a recorded interface's instructions are the segment
     `lookup` names for its identity. The explorer shows these interfaces for all 3,125 blocks.
   - `bodyIfaces_complete` proves that, when the validator's expression check accepts the body
     (as `funcCheck` runs it), every block gets an interface. So a validated body has one proved
     typed interface per block.
   - **Open:** a statement about runs.
   - The trap/throw effect marks and referenced indices stay syntactic.
4. **Bytes**, valid serializer profile only (`encodeModule?`).
   - The encoded object is (locals, body). It is an *encoding* object only: semantically, a
     function is (type index, body) under the module's context, and the explorer's function pages
     are (module, index).
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
   - The operational bridge comes first: a block step relation stated through Core 3.0 `Steps`,
     with a simulation onto CFG paths, starting with the fragment without calls.
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

## Plan: execution follows the CFG (operational bridge)

**Goal.** Theorems about Core 3.0 runs of a function body, which remove the "syntactic,
incomplete" caveat. Nothing here is assumed of a grouping of the graph, such as a dominator
or region tree. Every semantic claim is a theorem against `Silmaril.Wasm.Execution.Core.Step`.

**Audit of what can be reused:**
- The target is the block CFG over `Instr` (`Cfg.Edge`, `lookup`, `entry`/`cont`/`labels`).
- The proof tools are `Execution.Core.Sim.Context` (`Step.split_head`, `Exit`/`ExitShape`,
  context lifting) and the `Logic.Core` decomposition (`labelPost`, `blockPost`, `loopPost`).
  Both work on `Instr` against `Step`.
- Three developments do not fit:
  - the native interpreter (`Interp`, `native_adequacy`) and the structured fragment
    (`SSA.Fragment`, `behaviours_eq_run`) work on `BExpr` or the fragment `Expr`, are
    integer-only with no exceptions, and characterise only final outcomes, not the blocks a
    run passes;
  - the abstract `BodyM`/`IterOps` layer has no link to Core yet.

**Scope: coverage is not equivalence.** A forward simulation (every Core step from a
position moves along a CFG edge) shows that the graph *covers* execution: every run projects
to a graph path. It does not give equality with the function's behaviours, for two reasons:
- **Infeasible paths.** The graph's `if`, `br_if` and `br_table` edges ignore the data
  conditions, so many graph paths are not runs.
- **Conservative marks.** The effect marks and edges are conservative, so they include
  outcomes no run reaches.

Behavioural equivalence needs more:
- an *executable* CFG semantics: typed blocks carrying values, locals and the store, whose
  branches read the data;
- a reverse simulation, or adequacy (every run of that semantics is a Core run);
- matching treatment of initialisation, termination and divergence.

The plain graph stays an over-approximation, and claims about it say so.

**Milestones**, each a bounded PR with no `sorry` on `main`:
1. **Position invariant.** `At body pos cfg` relates a reachable configuration of the body
   (nested `LABEL_n{cont}` contexts around `val* rest`) to a position
   `(BlockId, offset, value stack)`. Every `cont`/`rest` is a suffix of a nested sequence of
   the body, and a loop continuation re-expands to its `loop`. Proved: the invocation
   configuration is `At` the entry.
2. **Straight-line steps.** A Core step from an `At` configuration whose next instruction is
   not a terminator is `At` the next offset of the same block. A trapping step is a `trap`
   effect edge of that block.
3. **Control steps.** The steps of the terminators (`block`/`loop`/`if` entry, `br`,
   `br_if`, `br_table`, `br_on_*`, `return`, label exit, `unreachable`) move from `b` to a
   position at the entry of some `t` with `Edge body b t`, or to `exit`/`trap`.
   *Done so far* (positions in `Cfg.Exec`, against `Step`): entering `block`, `loop`,
   `try_table` and the chosen `if` arm, and falling out of a `block`/`loop`/`if` arm
   (`resid_at_block_step` … `resid_inArm_done_step`). These use the shared Core inversions in
   `Execution.Core.Inversion` (stuck codes, `call`/`call_ref`, `LabelExit`/`HandlerExit`/
   `FrameExit`). Still to do: steps inside a label (lifting a body step through
   `ctxt-label`), branches and their bubbling, `try_table` fall-through and catches, and the
   projection of positions to `Cfg.Edge`.
4. **Exceptions as control** (#230): a `throw`, or a raise out of a call, resolves to the
   enclosing `try_table` catch target or leaves the function. The CFG gets resolved exception
   edges for this, proved against the `HANDLER` rules. This replaces `handler-unresolved` and
   the call → `raise` effect edge. Trap and raise stay distinct.
5. **Path theorem.** Every finite run prefix, and every infinite run, of a call-free body
   projects to an edge path from `cfgEntry`. Divergence is an infinite path.
6. **Precise effects.** Each `trap` edge is justified by a step that traps (no generic "may").
   The converse, that every such edge is reachable, is not claimed unless proved.
7. **Executable block semantics and adequacy.** A typed block semantics (values, locals,
   store; branches read the data) and the reverse simulation. Only with both may equivalence
   with `behaviours` be claimed. For the structured native fragment, equality of its runs with
   the fragment's `Run` then gives Core 3.0 call-equivalence (`callEquiv_of_run_iff`).
   *First slice done* (`Cfg.Region`): a compositional big-step region semantics `Run` on Core
   runtime code (values, non-control instructions, `block`/`loop`/`if`/`br`/`br_if`/`return`,
   `LABEL`, `TRAP`) with outcomes `normal`/`br`/`ret`/`trap`. It is adequate for Core 3.0 in
   both directions, for every profile and host, on terminating runs: `run_adequate`,
   `body_adequate`, and `frame_adequate` for function frames. Sequencing is
   `run_append_iff`. Divergence: `RunDiv` (structural greatest fixed point) with `div_iff`
   (`RunDiv ↔ Core Diverges` on the fragment), using `atomTerm` (every non-control instruction's
   reduction is strongly normalising, by expansion level and bulk counts). `br_table` and
   `br_on_*` are in the fragment (`BrStep`), and so are exceptions (`throw`, `throw_ref`,
   `try_table`, `HANDLER`, clause resolution `Catches`; outcome `throw a`). Calls inside bodies remain.
8. **Calls**, through an explicit call interface: a call node whose callee behaviour is a
   parameter (a `FRAME` run of the callee), first for direct calls.

9. **Native trees ↔ region semantics** (`Cfg.Bridge`, `Cfg.BridgeBwd`). The native evaluator
   on folded trees (`CallX.EvalOX`, oracle `C`) against `Region.RunC` of their lowering, with the
   same oracle; `ResOut` relates the ends (pending tail calls answered at the frame, branch and
   return values carrying the enclosing labels' values in the region).
   - **Forward, done** (#492): `bridge_fwd` (typed `EvalOXT`, `chkE tExt`-checked, oracle sound
     for the tail-aware check), `bridge_fwd_closedX` (the typed closed extended oracle, no oracle
     hypothesis).
   - **Backward, flat case, done**: `flat_bwd` (deterministic profile `SingleThreaded.profile o`,
     any host and oracle): a region run of a checked, typed flat instruction other than a call is
     its `evalFlat` result, from HostEval's `flat_complete` (#496).
   - **Backward, trees without extended calls, done**: `bridge_bwd` (deterministic profile, no
     host, an oracle sound for the tail-aware check that keeps typing) and `bridge_bwd_closedX`
     (the typed closed extended oracle, no oracle hypothesis): a region run of the lowering of
     typed trees with no `call_indirect`, `call_ref` or tail call (`CallX.xFreeL`; direct calls
     included) is a native `EvalOX` run with the same oracle, ending as `ResOut` says. Loops are
     by induction on their region run (`loop_aux`), re-entering at each branch back.
   - **Backward, trees without tail calls, done**: `bridge_bwd_tailFree` and
     `bridge_bwd_tailFree_closedX` add `call_indirect` and `call_ref` (resolved as the native
     evaluator resolves them, answered by the same oracle entry); `bridge_bwd` is its
     `xFreeL` case.
   - **Backward, every outcome but a pending tail call, done**: `bridge_bwd_nonTail` and
     `bridge_bwd_nonTail_closedX` cover every typed tree, tail calls included, when the region
     outcome is not `Out.tail`: `return_call_ref` on null and `return_call_indirect` without a
     callee trap natively. `return_call_indirect`'s `table.get; ref.cast` Core runs are forced at
     the deterministic profile without host (unique host-free normal forms,
     `BridgeBwdRci.run_rci_inv`).
   - **Backward, pending tail calls, done**: `bridge_bwd_tail` (and `_closedX`): a region run
     ending in `Out.tail W a c` corresponds, for **every** oracle answer to that call
     (`ResOut … (.tail W a c) r`), to a native run to `r`; the callee's parameters are on `W`
     (typing at the call site), so enclosing labels do not change the arguments.
     `bridge_bwd_answered` (and `_closedX`) is the existence form: if the outcome is not a
     pending tail call, or the oracle answers it, the region run is a native run with the same
     oracle, ending as `ResOut` says. This is the draft #494's `Task.bwd` with its honest
     hypothesis: without an answer to a pending tail call there is no native result. The draft's
     `sorry`s are replaced and it is not merged.
   - **CFG corollaries, done** (`Cfg.BridgeCfg`): `machine_native` (a machine run from
     `cfgEntry` of typed trees without tail calls to a sink is a native run with the same
     oracle, the sink's `EndsC` and the native result related by `ResOut`) and `native_machine`
     (a typed checked native run from the empty stack is a machine run from `cfgEntry` to a sink
     completing its region outcome, unless that outcome is a branch out of the body; pending tail
     calls are completed by the oracle answer `ResOut` carries), with the `closedXOk` instances
     `machine_native_closedX`, `native_machine_closedX` (no oracle hypothesis). These are about the
     block-CFG machine as an executable semantics; the plain graph stays an over-approximation.

10. **Branches to the function label (bug in the block-CFG machine; fixed).** A function
    body runs under its function's label (Core `FRAME_n{} (LABEL_n{} body)`), so a branch whose
    depth is the body's nesting depth returns; the native store check accepts it (labels
    `[rs.length]`) and the extracted CFG resolves it to `exit` (`labels body [] = [.exit]`). The
    machine's branch rules (`br`, `brIfTaken`, `brDataTaken`) need a label frame for the target,
    and the function label has none, so the machine is stuck exactly where the CFG has an `exit`
    edge; this is why `run_complete_initialC` excludes `br` outcomes.
    - **Regression fixtures, done** (`Cfg.ExampleBrOut`): the validated module `brOutMod`
      (`brOutMod_valid`) with a top-level `br 0`, a taken and an untaken `br_if`, a `br_table`
      to the function label from inside a block, and two results; Core returns their results
      under the function label (`core0` … `core4`), while the machine is stuck
      (`machine_stuck0/1/4`, `machine_no_sink0/1/4`, `machine_enter3` then `machine_stuck3`).
    - **Fix, done (machine transitions and soundness):** `MStepC.brOut`, `brIfOut`,
      `brDataOut` step from a block whose terminator branches to label index `ls.length` (the
      function boundary; deeper labels stay invalid) to `exit` with the block's values, as
      `return` does; `Ends` at `exit` adds `∃ W, o = .br 0 (W ++ stk)`. Every case analysis over
      `MStepC` is extended: soundness (`wrap_brOut`, `brOut_sound`, `brIfOut_sound`,
      `brDataOut_sound` in `mstep_sound`), the CFG edge (`resolveT_out`: the function label
      resolves to `exit`, so each new step is an `Edge` to `exit` in `mstep_edge`), and the Core
      simulation (`msim`: the new steps go to a sink). Divergence results are unaffected: the
      new steps end at a sink. The fixtures are restated as machine steps to `exit` with Core's
      results (`machine_exit0/1/3/4`).
    - **Completeness, done:** `run_complete_initial_outC`: every `RunC` run of the body that
      does not end in a pending tail call or in a branch past the function label is a machine run
      from `cfgEntry` to a sink, ending as `Ends` says; a branch to the function label reaches
      `exit`. The completeness induction's `Reach` asks, at a branch to label `ls.length`, for a
      run to `exit` (established by the new rules, carried outward through labels and handlers
      like `return`). `run_complete_initialC` (no branch outcome) is kept as a corollary.
    - **The same bug for `try_table`, fixed:** a catch clause whose label is the function label
      (`j + 1 + l = ls.length`) had no transition either (`catch_`/`bodyCatch` need a frame for
      the target). `MStepC.catchOut`/`bodyCatchOut` go to `exit` with the handler's outer values
      under the caught ones; soundness (`throw_catch_out`, `catchOut_sound`,
      `bodyCatchOut_sound`), the catch edge (`catch_edge` at index `ls.length` is `exit`), the
      Core simulation and completeness (`Reach` for a throw also asks for these catches) are
      extended.
    - `native_machine` now excludes only branches past the function label.

11. **A defined function's CFG execution against its Core invocation** (`Cfg.Function`).
    Fragment, stated explicitly: a typed invocation (`StoreOk`, `InvokeOk`) of a Wasm function in
    a store of Wasm functions with function types (`WasmFuncsT`) passing the tail-aware check
    (`StoreChkE tExt`: every call form, no `throw` or `try_table`), the deterministic profile, no
    host (closed: no observable call log). The machine runs the function's body in its call frame
    with calls answered by the typed closed extended oracle `CX closedCallX`.
    - **Finite runs, both directions, done:** `machine_core` (a machine run from the CFG entry to a
      sink is a native body run whose flow is a closed outcome of the invocation, and Core runs
      the invocation to the matching values or trap in the same final store) and `core_machine`
      (a stopping Core run of the invocation is terminal, a closed outcome, and the body's native
      run to it is a machine run from the CFG entry to a sink ending as that run; branches past
      the function label are ruled out by the body check).
    - **Callee divergence of every call form, soundness side:** `Region.DivFC` and the machine's
      `BodyCallDiv` admit a `call_indirect` resolved by `CallRes.IndRes` to a function and a
      `call_ref` of a function reference, answered by `C` or diverging inside the callee (`D`), next
      to direct calls. `div_soundC`, `bodyCallDiv_core` and `mdivC_core_initial` cover them under the
      same hypotheses (`CallSoundA`, `DivCallSound`, both stated for every `call_ref` form). A null
      table entry, null reference or failed cast traps (`RunC.callIndRes`, `RunC.callRefNull`) and
      has no divergence constructor.
    - **Callee divergence of every call form, completeness side:** `FragC` now has `call_indirect`
      and `call_ref`. `GuardedCalls` guards every `call_ref` of a function reference the run
      reaches, and a direct call's guard follows in one step (`guarded_call`). Finite completeness
      (`completeC`, `run_completeC`) rebuilds `call_indirect` from its Core unfolding
      `table.get; ref.cast; call_ref` (`callInd_back`, via the profile-generic inversions in
      `Proofs/Wasm/Cfg/IndSteps.lean`), and answers `call_ref` of a function by `callRef_incl`.
      Divergence completeness (`div_completeC`, hence `core_div_initialC`, `core_div_closed` and
      `mdivC_iff_core_closed_typed`) has `div_callInd`/`div_callRef`: the call diverges in the
      callee (`D`), or is answered with values and the continuation diverges. An unresolved index
      or null reference traps and never diverges. New Core inversions: `Step.callRef_top_inv(_seq)`
      and `Step.callIndirect_vals_inv_seq`. **Open:** completeness of divergence through a tail
      callee (`FragC` has no `return_call*`), a `call_indirect` fixture (needs a store with a
      table), and the function-level corollary via `invoke_diverges_iff_funDivX`.
    - **`call_ref` fixtures (`Wasm/Cfg/ExampleRef`):** `ref_machine_div`: in the frame of the
      validated self-call of `recMod`, `ref.func x; call_ref y` has no infinite machine run, yet
      `MDivC` with `closedCallOk`/`closedDiv` holds through `BodyCallDivRef`, and Core 3.0 diverges.
      `null_machine_trap`, `null_not_diverges`, `null_not_mdivC`: `ref.null; call_ref` moves to the
      `trap` sink in one step, and never diverges.
    - **Divergence through tail callees, soundness side:** `MDivT` is `MDivC` or a finite run to a
      block ending in a tail call of a callee `D` names (`TailCallDiv`, read as `MStepC.tail` reads
      it, with no answer). `mdivT_frame_initial` (and `mdivT_frame_closed`): from the CFG entry it
      is Core 3.0 divergence of the function's frame `FRAME_n{fi} (LABEL_n{} body)` in any outer
      frame. The tail call replaces the frame (`return_call_ref-frame-addr`, `frame_tail_div`), so
      the body's pending code and handlers are bypassed. Fixture `Wasm/Cfg/ExampleTail`:
      `block (return_call x); unreachable` in the frame of `recMod`'s self-call (`tail_machine_div`).
      **Converse (Core route, step 2):** `frame_div_complete`: a diverging Core frame either
      diverges inside, which is body divergence through the function label (`MDivC` by
      `core_div_initialC`; a label exit stops outside any frame), or is left; every frame exit stops
      except a tail call of a function (`return_call_ref-frame-addr`), whose call diverges: the body
      runs to the pending tail call (`run_completeC`), the machine reaches its block without an
      oracle answer (`run_complete_tail_block`, via `Reach`'s tail clause, now the block itself:
      `TailAt`), and `D` names the callee (`DivCallComplete`, guard by `Region.TailGuarded`).
      `mdivT_iff_frame` combines both directions. 
    - **Function-level divergence, both directions (Core route, step 3):**
      `Function.invoke_diverges_iff_mdivT`: on the fragment (typed invocation, `WasmFuncsT`,
      `StoreChkE tExt`, deterministic profile, no host), Core divergence of `invoke s a vs` is
      exactly `MDivT` with `CX closedCallX` and `calleeDivX o` on the body in the call frame.
      `Function.funDivX_iff_mdivT`: with `invoke_diverges_iff_funDivX`, so is native `FunDivX`.
      No hypothesis beyond the fragment: every instruction is in `FragC` (`fragIB_all`); the
      oracle is complete on the fragment (`callCompleteG_cx`, from `invoke_closedX_adequacy` and
      call transport), `calleeDivX` is (`divCallComplete_cx`), and the guards at calls and pending
      tail calls and the placement of pending tails come from typing of the entered frame
      (`guardedCalls_cx`, `tailGuarded_cx`, `tailsOk_of_typed`). Not claimed: hosts, exceptions
      (`tExt` rejects `throw`/`try_table`; no host alone does not exclude them), the
      store-retaining session view. Fixtures (`Wasm/Cfg/ExampleFunDiv`, a validated
      `tExt`-checked module): `fd_recursive`: functions recursing through `call_indirect`,
      `call_ref` and `return_call` diverge natively (`FunDivX`, by coinduction), in Core 3.0 and as
      `MDivT`; `fd_trap`: a `return_call_indirect` through a null slot and a `call_ref` on null
      trap (closed outcomes), so none of the three holds.
    - **Host-free function-list preservation** (`Wasm/Cfg/Restrict`): without a host, a region or
      machine run keeps the store's whole function list `F` (instances with types, modules and
      code), so every call and every `F`-only check (`StoreChkE`) sees `F`. Oracles agreeing on
      stores with `F` give the same runs, steps, infinite runs, `MDivC` and `MDivT`
      (`runC_funcs` … `mdivT_funcs`). Host-free only: nothing is claimed for host-mutated stores.
    - **Function-level divergence, soundness side:** `Function.invoke_diverges_of_mdivT`: on the
      fragment, `MDivT` with `CX closedCallX` and `calleeDivX o` (typed `tExt` callees whose
      invocation diverges) is Core divergence of `invoke s a vs`. With `F = s.funcs`, `CX
      closedCallX` answers as the Core-sound `closedXOk` (`cx_closedXOk`); the invocation steps to
      the function's frame (`call_ref-func`), which diverges by `mdivT_frame_initial`. **Open:**
      the converse, by the Core route (Core divergence ⇒ `MDivT`, reusing region completeness;
      `FunDivX` then by `invoke_diverges_iff_funDivX`).
    - **Tail calls in the fragment with calls (Core route, step 1):** `FragC` now has `return_call`,
      `return_call_indirect`, `return_call_ref` (and the runtime `return_call_ref` of a type).
      Core's `return_call_ref-label`/`-handler` moves all of a label's values out with the call, so
      on untyped code the reference may come from outside the label (`ref.func a; block
      (return_call_ref y)`), where the region semantics has no run: completeness with tail calls
      needs the typing fact that it does not (`TailWF`, along the run `TailsOk`; from typing,
      `tailsOk_of_typed`, via `retRef_ref_of_typed`). With it, `run_completeC` and `div_completeC`
      cover tail calls: a tail call ends the region in a pending tail call (`labelTail`,
      `handlerTail`, … through labels and handlers, which do not catch it), and a body never
      diverges at a pending tail call, which is stuck outside a frame. Divergence of the tail
      callee is frame divergence (`MDivT`), not body divergence. No EH coverage changes.
    - **Exit states carry the whole frame stack (semantic correction).** The machine's exits by
      `return`, a branch to the function label (`br`, taken `br_if`, `br_table`/`br_on_*`) and a
      caught exception branching to it (`catchOut`, `bodyCatchOut`) kept only the innermost
      block's stack, dropping the label frames' outer values; `Ends` at `exit` allowed any `W`
      below it. They now keep the whole stack Core unwinds, `brVals` (outer values under the
      block's; for a catch, the caught values over the handler's outer values, then the frames its
      branch leaves), and `Ends` at `exit` is exact (`o = .normal`/`.ret`/`.br 0` of the stack).
      Fall-through (via `popL`) and answered tail calls (frame replacement) were already exact and
      are unchanged; branches past the function label stay invalid. Soundness (`ret_sound`,
      `brOut_sound`, …, exact), completeness (`Reach`'s `br`/`ret`/catch clauses) and every
      downstream result were updated. Fixtures `Wasm/Cfg/ExampleExitStack`: nested `return`,
      `br`, `br_if` (taken, not taken) and `br_table` with an outer value, two results, against
      Core; an invalid body whose `return` reaches below its block (`machine_loss`, `core_loss`),
      on which the old exit lost a value (no general untyped claim).
    - **(b), host-free milestone: the CFG session is the instance session** (`Wasm/Cfg/Session`).
      Target: the canonical `DStrategy` `instSession I P s = StratSession.threadS (instTripleS I
      P) s` (`Abstract.InstSession`), hence the instance part of `core3SemD`, on an explicit
      typed fragment. Not "define the CFG object by Core and conclude `rfl`".
      1. **The CFG triple** `cfgTripleS I o`, operational: `cfgFinS` is machine runs (`MStepC`,
         oracle `CX closedCallX`) of the export's body in its call frame to a sink, the answer
         read off the sink state (`sinkResult`: the top `rs.length` values of the exit stack, the
         whole frame stack since the exit fix; `trap` keeping its store), and machine frame
         divergence `MDivT` with `calleeDivX o`; empty logs. It is **oracle-backed**: callees
         are answered by the native closed extended semantics `CX closedCallX`, not by recursive
         CFG machines. A self-contained recursive CFG closure would discharge the oracle later
         and is not claimed.
      2. **The fragment** `HFOk I s`: no imports, `I.WellFormed s`, only Wasm functions with
         function types (`WasmFuncsT`), `StoreChkE tExt`, at `profile o`. Preserved at every
         reachable store (`hfOk_of_reach`: the function list never changes host-free,
         `wellFormed_after_run`). Exceptions are excluded by `tExt`, separately from hosts; the
         proof derives that a closed outcome of a checked invocation is never a throw.
      3. **Equality**, both directions per activation (`instFinS_eq`): returning activations by
         NodeBridge `ret_iff` (empty logs) and `Function.core_machine`/`machine_core`, the sink
         reading matched against Core's result (`sink_cases`; values are typed, so the exit
         stack holds the results); divergent ones by `div_iff` and
         `invoke_diverges_iff_mdivT`. With empty `satP` and productive components (no import
         operations), `threadS_congr` gives `cfgSession_eq_instSession`; then `spull_cfgSession`
         (the finite plays are `I.strategy`) and `core3SemD_eq_cfgSessions`: `core3SemD
         (profile o)` interprets every numeric instance in the fragment at its instantiation
         store by its CFG session (and the others by their instance sessions).
      4. **No imports is not no infinite plays**: no imports removes import callouts, call logs
         and within-call productive host interaction, not infinite session plays.
         `mem_inf_cfgSession`: the infinite plays are exactly those of the coherent infinite
         sequences of export rounds (`InfRounds`, via `mem_inf_instSession`/`StoreDet` and
         `infRounds_iff`), trap-resume rounds included; `infRounds_repeat`. Fixtures
         (`Wasm/Cfg/ExampleSession`, a validated two-export module, no imports): `ses_hfOk`;
         export `0` traps and export `1` answers `7` on the machine; `trap_forever` and
         `alt_forever` (trap, answer, trap, …) are infinite plays of the CFG session and of the
         instance session.
         **`cfgSessions` is compatibility, not coverage**: outside `HFOk` it falls back to the
         Core 3.0 instance session; no CFG semantics of general modules or components is
         claimed without the domain hypothesis.
    - **The domain, checked, and components on it** (`Wasm/Cfg/SessionCheck`):
      - `hfOk_of_check`: for a validated module without imports, instantiated into the empty
        store, an instance passing the executable check `hfCheck` is in `HFOk`.
        - `hfCheck` uses existing checkers: `storeChkEB tExt`, a Wasm-function check, and export
          types via `expand?`.
        - Store typing comes from validation and instantiation.
      - `denUD_congrIn`: a denotation depends only on the core instances a component uses
        (`CompIn`).
      - `denUD_core3SemD_eq_cfgSession` and `denD_…`: when every core instance of a component
        is in `HFOk`, its Core 3.0 denotation is the one with CFG sessions. There is no
        fallback, and nothing is claimed outside the domain.
      - Regression: `ExampleSession.ses_hfOk_checked`.
    - **Catch exits (#866 regression)** (`Wasm/Cfg/ExampleCatchExit`, a validated module with a
      tag `[i32 i32] → []`): a caught exception branching to the function label exits with the
      whole frame stack: `machine_catch` (`1, 3, 4`: the `try_table`'s outer value under the
      payload) and `machine_catchNest` (`1, 2, 3, 4`, through an enclosing block), against Core
      returning the payload `3, 4` (`core_catch`, `core_catchNest`); the tag hypotheses hold at
      the module's instance (`catch_tag`). Exit state only: no exception coverage at the function
      or session level.
    - **Not implemented (ledger)**, in order:
      1. **Hosts**: imports in the CFG session: pending import calls and logs, productive
         within-call host interaction, host answers keeping or changing the store, and exceptions
         raised by host answers. Route H1–H3 below.
      2. **XP/EH**: exceptions in the session fragment (`throw`, `try_table`, handler matching,
         tail calls bypassing handlers, uncaught exceptions as `Answer.throw`), trap stores
         preserved. Covered by the same route: `EvalLXPS` has the exception rules.
      3. **Discharging the oracle**: callees run by the CFG machine through a recursive closure
         (H3), callee divergence included. Done at closure level by `CfgClosure` (H3-4):
         `cfgSessionTripleC` is CFG-defined and equals `sessionTripleXP`.
      4. Untyped stores and instructions outside the checked fragments: unsupported, excluded by
         hypotheses.
    - **Route for hosts, XP/EH and the oracle (H1–H3, coordinator-approved).** The CFG machine
      `MStepC` is unlabelled: simple steps are Core `Steps P host`, and calls go through a stateless
      `CallRel` oracle. A run's host-event log cannot be recovered from it, and a stateless host
      cannot encode one, so the logs need a logged CFG layer. It reuses the CFG graph, extraction
      and control rules, and the canonical store-retaining logged relation
      `HostClosingS.EvalLXPS` (open calls with arbitrary answers: values, an exception raised at
      the call, or a callee trap with its store).
      - **H1, the logged machine `MStepL`.** A block-CFG execution: each block runs its straight-line
        segment by `EvalLXPS` on `liftInstrs sg.body` (flat ops by `evalFlat`, calls open and
        logged), then its terminator with `MStepC`'s rules (label frames, `goto`, `brVals`,
        `topVals`, loops, the function label, `try_table` frames and `Catches`, pending tail
        calls). It is never a native evaluation of the whole structured function in one step.
        Machine stacks are bottom first and native ones top first (`reverse`). Obligations:
        - a projection to `MStepC` on their shared fragment, with its hypotheses stated where
          host observations cannot be forgotten;
        - the forward theorem (the first bounded PR): a logged run from the CFG entry to an end
          (`exit`, `trap` with its store, an uncaught exception, a pending tail call) with log
          `l` is an `EvalLXPS` run of the body with exactly `l` and the store.
      - **H1 status (done here): the logged machine and the forward theorem**
        (`Wasm/Cfg/MachineL`).
        - `MStepL`: each block's straight-line code runs by `EvalLXPS`, then the native outcome
          is dispatched (`DispL`) to `MStepC`'s CFG targets, with **native stack conventions** at
          frame boundaries (coordinator-approved option B).
          - Leaving an arm keeps the top `nr` values over the frame's outer values (`popN`,
            `gotoN`).
          - A branch keeps the label's arity of the branch-site stack (`branchN`).
          - `return` and a branch out of the function exit with the branch-site stack.
          - Arities come from the block type (`Binaryen.arity`), with no run-time checks.
          - Entering an arm and re-entering a loop split the stack as `EvalLXPS` does
            (`stk.take np`, `vs.take np ++ outer`), so no step is missing on short stacks.
          - `MStepC` keeps Core's conventions. The two agree on typed code; no untyped
            correspondence is claimed.
        - `forward_sink`, `forward_tail`: for **all code**, a logged run from the CFG entry to a
          sink (or to a pending tail call) is an `EvalLXPS` run of the body. The log, final store
          and frame are exactly the run's, and the result is one the sink stands for (`EndRel`).
          This covers stores kept by traps, and tail calls bypassing handlers.
        - The proof is an invariant (`Good`, `KL`, `WrapL`) carried backwards along the run: at
          each block the rest of the sequence runs natively, and each enclosing structured
          instruction's native rule carries the outcome out.
        - Fixture `Wasm/Cfg/ExampleLogged`: on an invalid body the logged machine exits with `3`
          (native) and `MStepC` with `1, 2, 3` (Core).
        - Run-level projection, done (`Wasm/Cfg/MachineLProj`, `project_sink_closedX`). A logged
          run from the CFG entry to a sink is an `MStepC` run to a sink with the same native
          result (`EndRel`, `ResOut`, `EndsC`). It composes `forward_sink`, `closed_iff_logged`
          and `native_machine_closedX`. Its fragment is stated:
          - every logged entry is answered by `closedXOk`, the typed closed extended oracle;
            host entries never are, so a log with a host call does not project;
          - direct calls only (`xFreeL`), no exceptions (`ehFreeL`), `TypedT` for `tExt`.
          It does not count as the stepwise projection. These restrictions are not its final
          coverage.
        - Still open in H1, in order:
          1. The stepwise typed stuttering projection `MStepL` → `MStepC` on the shared no-EH
             fragment.
             - Control agreement, done (`MachineLProj`): `popN_eq_popL`/`gotoN_eq_goto` under
               `PopFit`, `branchN_block`/`branchN_loop`, `armSel_condArm`, `labelArity_eq`.
               At exits the stacks differ by the left frames' outer values (`brVals_junk`).
             - Checker invariant, done (`MachineLProj`): `CInv`/`ChkF`, from the function's own
               `chkE (ehExt tags)` check (`cinv_initial`), preserved along logged runs answered by
               an arity-respecting oracle (`cinv_step`, `cinv_run`, via `evalOXP_goodO`), on
               bodies without `try_table` (`NoTry`). The fallthrough, branch and arm-entry
               targets are the native ones with fitting stacks.
             - Segment bridge, done (`MachineLProj`, `seg_runC`). Logged `Flat` straight-line
               code with `CloseOk C` calls of a sound oracle (`OracleSoundT`, e.g. `closedXOk`)
               is a `Region.RunC` run with `ResOut`. It needs checker facts only: the segment's
               `chkE (ehExt tags)`, which is `tExt`'s off the EH forms (`chkE_flat_tExt`), and
               `StoreChkE tExt`. There is no Core typing of states, because `EvalOXT` is `EvalOX`
               without indirect or reference calls. Fragment hypothesis: `DirectCalls body`
               (`seg_flat`).
             - Stepwise projection, done on the shared no-EH fragment (`MachineLProj`:
               `proj_step`, `proj_runL`, `proj_initial`). On checked states each logged step is
               **one** `MStepC` step. Targets are related by `ProjRel`: equal, or both `exit` with
               the `MStepC` stack the logged one under further values (`brVals`). Composition
               along runs, from the CFG entry.
               - Proof: the block's whole plain straight-line code goes to a region run
                 (`plain_runC`) and is split. The terminator's region run is classified
                 (`term_run`). Targets come from `CInv` and the control-agreement lemmas.
               - Fragment hypotheses: `NoTry`, `DirectCalls`, `PlainTerms` (no `throw` or
                 extended-call terminators, so no tail calls), and `StoreChkE tExt`.
               - Oracle hypotheses: `CloseOk C` logs, `OracleSoundT` and `ArityResp`.
             - Closed instance, done: `proj_initial_closedX` has no oracle hypothesis. It reads
               the checker invariant with `tExt` (`OracleX.evalOXT_goodT`, `SegGood`). For
               `closedXOk` (sound, and keeps the store's functions), a logged run from the CFG
               entry with `closedXOk`-answered calls is an `MStepC closedXOk` run, its end related
               by `ProjRel`.
             - Then: lift the fragment with the `EvalOXP`/EH bridge (`try_table`, `throw`,
               indirect and reference calls, tail calls and frame replacement). It needs a typed state and frame invariant, from the existing checker and
             typing APIs, covering stack orientation, parameter and result arities, normal arm
             exits, branch unwinding and tail-frame replacement. The relation is at block
             granularity (zero or more `MStepC` steps per `MStepL` step), with composition.
          2. An `EvalOXP`/`EvalOXE` → Core bridge for exception outcomes (`ehExt`).
             - Flat bridge, done (`MachineLProj.flat_runP`, `ResOutP`): an `EvalOXP C` run of
               flat code is a `Region.RunC` run with the same oracle. It needs a `chkE (ehExt
               tags)` check, `ArityResp Γ C` and `Γ.Good`. Flat code covers direct, indirect and
               reference calls, `throw`, `throw_ref`, the tail calls, branches, `return` and
               `unreachable`.
               - Outcomes: a flow goes to the same store and frame under `FlowRel` (throws
                 included). A pending tail call goes to `Region.Out.tail W a c`, whose top
                 `ps.length` values are the arguments, with `n` the callee's result count.
             - Stepwise projection over `EvalOXP`, done (`proj_stepE`, `proj_runLE`,
               `proj_initialE`). Hypotheses: `NoTry`, `ArityResp Γ C`, `CloseOk C` logs and
               `Ctx.Good`. `DirectCalls`, `PlainTerms`, `StoreChkE tExt` and `OracleSoundT` are
               dropped. `throw`/`throw_ref` terminators are `MStepC.raise`, tail calls of null are
               `MStepC.tailNull`, and indirect and reference calls go through the bridge.
             - Next:
               - answered tail calls, done (`proj_tailE`, `proj_tail_initialE`). A logged run ending
                 in `TailL`, with its tail answer a `CloseOk C` entry, is an `MStepC` run whose
                 last step is `MStepC.tail` (frame replacement), to `tailSink`;
               - `try_table`, done (`cinv_stepE`, `cinv_runE`, `proj_stepK`, `proj_runLK`,
                 `proj_initialK`, `proj_tail_initialK`). `ChkF` records each `try_table` frame's
                 clause check. `catch_arity` (`Interp.catches_count` under `TagsOk`) gives the
                 caught values' arity. Catches map to `MStepC.catch_`/`bodyCatch`/`catchOut`/
                 `bodyCatchOut`. The stepwise projection now holds for **every call form and
                 structured instruction, exceptions on**. Its hypotheses: `ArityResp Γ C` with
                 `CloseOk C` logs, `Ctx.Good`, and the body's own `chkE (ehExt tags)` check.
             - Remaining for the stepwise projection: none. For the session result, `CloseOk`
               is discharged by the canonical closing correspondence (host-free: done,
               `MachineLClose`, below). It must keep
             the exception outcomes, tag matching, trap stores, and tail calls bypassing the
             caller's handlers. Then the stepwise projection extends to EH.
          3. Validated typed nested fixtures (block, loop, if, catch) on which it holds.
             - Fixtures, done (`Wasm/Cfg/ExampleNested`; the module `nestMod` validates).
               On each of three bodies, `MRunL` (empty log) and `MStepC` (every profile, host
               and oracle) reach the same `exit` state, with the same stack, store and frame:
               - `bodyNest`: `block`/`loop`/`if` with a `br 2` across two labels, exit `9, 42`;
               - `bodyLoops`: the inner loop's `br_if 1` re-enters the outer loop once, with a
                 counter local, exit `2` (`loops_logged_via`, `loops_core_via`);
               - `bodyTry`: a `throw` in a block nested in a `try_table` is caught to an outer
                 `block`, exit `4`, under stated tag hypotheses that hold at the instance
                 (`nest_tag`).
               Native `EvalLXPS` runs follow by `forward_sink`.
             - Limits: no `ExampleNested` fixture exits from frames with outer values. The
               `brVals_junk` boundary is exercised by `Wasm/Cfg/ExampleRetJunk` instead.
             - These are concrete agreement facts on these bodies, proved by running both
               machines. They are not derived from the stepwise projection
               (`proj_step`, `proj_initial_closedX`). `bodyTry` lies outside its fragment
               (`try_table`, `throw`).
          The `CloseOk` hypothesis is discharged in the session/host result by the canonical
          store-retaining closing correspondence, not kept as an assumption that all logs are good.
          - **Host-free discharge, done** (`Wasm/Cfg/MachineLClose`). No assumption on the logs.
            - `closeOk_of_session` (no typing): a behaviour `([], .ret b s₂)` of
              `wasmEvFunXPS s (g, args)` is `CloseOk closedCallXP (SCall.mk g args s b s₂)`:
              values (trimmed to the result count), exceptions and callee traps
              (`.inr ()`), each in the store the closure leaves. Least-fixpoint induction on
              `Shape.close wasmHOpenXPS`: with the empty log every call is internal and resolved
              with the empty log, so the body run is `EvalOXP closedCallXP` (`closed_iff_logged`),
              and `closedCallXP_fixpoint` with `FrameP` gives the answer. A pending tail call is
              answered at the frame (`FrameP.tail`); its `n` is the callee's result count
              (`evalLXPS_tail_wf`), so the closure's `tailAnsS` trimming is `closedCallXP`'s.
              `session_ret`: every session behaviour ends in `.ret`.
            - `logged_of_session`: for a Wasm function `a` (`s.funcs[a]? = some fi`,
              `fi.code = .wasm fn`, type `(ps, rs)`), called with `vs.length = ps.length`, from a
              store with `Γ.Good s`, a behaviour `([], e)` is an `MRunL` run of `fn.body` from the
              CFG entry (frame `Frame.forCall fi.module vs fn.locals`) with every entry
              `CloseOk (fitP closedCallXP)`: to a sink (`EndRel`) whose exit flow gives `e`
              (`endOfFlowS`), or to a `TailL` block whose tail answer is also such an entry and
              `e = tailAnsS rs.length n b s₂`.
            - `proj_of_session`: then `proj_initialK`/`proj_tail_initialK` with
              `arityResp_fitClosed` give an `MStepC P host (fitP closedCallXP)` run from the CFG
              entry to a state `ProjRel`-related to that sink, or to `tailSink b s₂ f₁`.
            - Fitting (`ArgsFit`): the body's calls fit by its `StoreChkE` check
              (`TypedCatFit.evalOXP_closed_iff_fit`); the pending tail call fits by the new
              `MachineLProj.tail_fit_initialK` (from `flat_runP`'s `ResOutP`). The invocation
              must fit (`vs.length = ps.length`): `StoreChkE` checks the body with `ps.length`
              parameter locals, and the frame has `vs.length`. This is the hypothesis every
              `fitP` answer carries for its own call.
            - Next: the host case (logs with host events, through `CfgSession`'s session
              correspondence), and stating the result over `CfgSession.cfgEvFunXPS`.
        - Converse support: `MachineLSeq.split` (a run of `es₁ ++ es₂` falls through `es₁` then runs
          `es₂`, or ends abruptly in `es₁`), the converse of `append`.
        - Converse design (next PR): induction on the native derivation, level by level.
          - At sequence level `p`, a native run of the rest of the sequence from block `i` gives
            a machine run to the state that `DispL` (or the fall-through to `contRev`) assigns to
            its outcome.
          - Structured terminators recurse on the arm's derivation, then on the parent's
            continuation derivation (both sub-derivations).
          - `loopBack`'s re-run of `.loop :: rest` is a sub-derivation started from the arm
            entry, not from the segment. So the induction's start states are "the point where a
            structured instruction is entered", which covers both the fresh entry (`enter`) and
            the re-entry (`branchN`).
      - **H2 status: the converse for finished outcomes is done** (`MachineL.backward`).
        - Hypotheses: a native run of the body to `r`, where `r` is not `brk (k + 1) _`. So `r`
          is a fall-through, `return`, `brk 0`, a trap, an uncaught exception, or a pending tail
          call.
        - Conclusion: a logged run from the CFG entry to an end standing for `r` (a sink, or the
          block making the pending tail call), with exactly the native log.
        - The excluded class: a native body outcome `brk (k + 1)` (a branch past the function
          label) can exist on invalid code. It has no machine end (no `DispL` rule) and no framed
          finished counterpart (`exitFlow` gives `none`, so no `wasmHOpenXPS` behaviour).
        - Proof: continuation passing on the native derivation (`MachineLBwd`). The motive
          covers mid-segment positions and arm entries, so `loopBack`'s re-run of the loop
          starts where the machine re-enters it.
        - The re-entered loop frame's arity is now the block type's parameter count, the same as
          a fresh entry.
        - **Pending calls, done** (`MachineL.pending_iff`, both directions): the body reaches the
          internal call `z` after the native log `l` exactly when the logged machine runs from
          the CFG entry to a block reaching `z` (`ReachL`), the logs splitting `l`.
          - Encoding, coordinator-approved, as an internal witness only: answering the call with
            a callee trap (`reach_trap` for every trap store, `trap_reach` the converse,
            `trap_last`), then the finished correspondence.
          - The pending question, its pre-call store and the prefix log are the statement's; the
            synthetic trap store is not.
          - Pending tail calls are ends of the body (`TailL`), not pending internal calls.
          - Fixture `Wasm/Cfg/ExamplePending`: a call in a handler that is pending, answered by an
            exception (caught: exit) or by a callee trap (uncaught: trap); a tail call in a
            handler (`TailL`).
        - **Divergence, step D1 done**: `MachineL.closed_iff_logged`.
          - A closed run `EvalOXP C` is exactly a store-retaining logged run (`EvalLXPS`) whose
            entries are all `C`-answers (`CloseOk`).
          - Answers are exact: callee values trimmed to the callee's result arity; exceptions and
            traps with the stores `C` leaves.
        - **Divergence, D2 done** (`Silmaril.Wasm.Cfg.MachineLDiv`). The machine's host-free
          divergence has three distinct forms, every logged call answered by `closedCallXP`
          (`StepK`):
          - `InfK`: an infinite run of local steps;
          - `CalleeDivK`: a finite run to a reached call (`ReachL`) whose callee diverges at the
            frame (`FunDivXP`);
          - `TailDivK`: a finite run to a pending tail call (`TailL`) whose callee diverges. This
            one is function-level only.
          `MDivL := InfK ∨ CalleeDivK`; `FunDivL` adds `TailDivK` at the frame, as `funDivXP_iff`
          does.
          - `div_iff`: `EvalDivXP s f [] (liftInstrs body) ↔ MDivL body (initial body s f)`.
          - `funDiv_iff`: `FunDivXP s a args ↔ FunDivL s a args`.
          - Native to machine: the infinite run is built from the native unfolding. Finite parts
            of structured instructions go through the converse's arm clause, with a strict stop
            state, so every unfolding makes at least one machine step.
          - Machine to native for `InfK`: coinduction on `EvalDivXP` over positions of the run.
            Steps are classified by depth (`MStepS`): re-entering a loop counts as leaving its
            arm. At the first step leaving an arm, the arm's run is read natively by a forward
            invariant relative to the arm's frame (`Proofs/Wasm/Cfg/MachineLRel`, `arm_fwd`).
        - **Divergence after a log, D3 done.** `MLogDivL body st l`: logged steps, then a
          boundary inside a step, then host-free divergence (`MDivL`, or a reached call whose
          callee diverges). The log is the calls before the boundary.
          - Native to machine, exact log: `logDiv_machine`. `LogDivXP s f [] (liftInstrs body) L`
            gives `MLogDivL body (initial body s f) (L.map OCall.toS)`.
          - Machine to native, up to oracle-answered calls: `machine_logDiv`. `MLogDivL ... l`
            gives `LogDivXP ... L` with `L.map OCall.toS = l ++ c`, every entry of `c` a
            `closedCallXP`-answer. `LogDivXP` places the boundary only where the remaining
            subproblem diverges; the machine's may come earlier, the run then leaving that
            sequence through closed calls. The closure resolves such entries with empty host logs.
          - Proof of the converse:
            - the run after the boundary eventually never leaves a sequence (`stays_point`: a
              block, or the arm entry of a loop re-entered forever), so that point diverges
              natively (`MachineLDivI.qx_div`);
            - the logged run from the CFG entry to it is a `LogDivXP` prefix (`prefix_logDiv`, a
              finite-horizon version of the coinduction, with arms left read by `arm_fwd`);
            - a diverging callee goes through the pending-call correspondence (`reach_logDiv`).
        - **Productive streams, P1 and P2 done (both directions).** `ProdL body st ω`: an infinite
          logged machine run whose step logs concatenate to `ω`, with infinitely many calls.
          - `infL_machine`: `InfLXP s f [] (liftInstrs body) ω` gives
            `ProdL body (initial body s f) (fun n => (ω n).toS)`, the same stream. The proof is an
            induction on `InfLXP`, as for divergence after a log. A loop iterating forever is the
            chain of its iterations on the machine (`prod_of_chain`, each iteration a nonempty run
            from the arm's entry back to it).
          - `machine_infL` (P2, machine to native, exact stream): `ProdL body (initial body s f) ν`
            gives `InfLXP s f [] (liftInstrs body) ω` with `ν = fun n => (ω n).toS`. `prodL_iff`
            states both directions together.
          - Proof of P2 (`Proofs/Wasm/Cfg/MachineLProdB`): a strong induction on the size of the
            remaining code, at positions of the run that never leave their sequence (`claims`:
            the block claim `PBC` and the arm-entry claim `PAC`).
            - An arm the run never leaves is a descent.
            - An arm left forward is a finished instruction, read natively by `arm_fwd`
              (`first_leave`).
            - A loop re-entered finitely often ends in `loopBack` iterations.
            - A loop re-entered infinitely often is `loopInf`. Its stream is the iterations'
              concatenation, the same stream as the run's tail (`streamConcat_unique`).
        - The closed oracle `closedCallXP` used here is the native one. These results do not
          discharge H3, which still needs the recursive logged CFG closure.
        - Fixtures: nested-loop `continue` (`ExampleNested.loops_*_via`) and a tail call inside
          a handler (`ExamplePending.tail_handler`, `tail_handler_machine`).
      - **H2 ledger (exact).** Every theorem is stated for **all code**, with no typing. The
        domain is a body run from the CFG entry `initial body s f`, natively from the empty
        stack on `liftInstrs body`. Logs are store-retaining session calls (`SCall`, each with
        its answer).

        | Notion | Theorem(s) | Directions | Domain and limits |
        |---|---|---|---|
        | Finished ends (exit, trap with its store, uncaught exception) | `MachineL.forward_sink`, `MachineL.backward` | both | `backward` excludes a native `brk (k + 1)` outcome. It occurs only on invalid code and has no framed counterpart. Logs are exact. |
        | Pending tail call (an end) | `MachineL.forward_tail`, `MachineL.backward` (`TailL`) | both | Bypasses handlers. Log exact. |
        | Pending internal call | `MachineL.pending_iff` (`ReachLXPS` ↔ `MRunL` then `ReachL`) | both, one iff | Log exact, split at the machine step. |
        | Closed runs | `MachineL.closed_iff_logged` (`EvalOXP C` ↔ `EvalLXPS` with `CloseOk C` logs) | both | Any oracle `C`. Host calls are never `CloseOk`. |
        | Host-free divergence | `MachineL.div_iff` (`EvalDivXP` ↔ `MDivL`); parts `div_machine`, `infK_div`, `calleeDiv_div` | both | Calls answered by `closedCallXP` (`StepK`). |
        | Frame divergence | `MachineL.funDiv_iff` (`FunDivXP` ↔ `FunDivL`); parts `funDiv_machine`, `funDiv_of_infK`, `funDiv_of_calleeDiv`, `funDiv_of_tailDiv` | both | At a call's frame, including a diverging tail callee (`TailDivK`). |
        | Divergence after a log | `MachineL.logDiv_machine` (exact log); `MachineL.machine_logDiv` (log extended by `closedCallXP`-answers) | both, the converse up to closed entries | The extension is necessary: the machine's boundary may come earlier. |
        | Productive streams | `MachineL.infL_machine`, `MachineL.machine_infL`, `MachineL.prodL_iff` (`InfLXP` ↔ `ProdL`) | both, one iff | Exact stream, each call with its answer. |

        - The session's productive part (`HostClosingInfXP.InfLwXP`) is exactly `InfLXP` at
          `Frame.forCall` from the empty stack. Its pending calls are `ReachLXPS`, and tail-call
          productivity and recursion enter through the closure's descent (`Shape.closeInfL`)
          over the open module's logs. So the body-level theorems above are the H2 obligations.
          Composing them at the function frame and through recursion is H3's equality, not a
          further H2 item.
        - **Not claimed in H2:** coherence of answers with a closure. Every H2 statement takes the
          calls' answers as given, by `SCall`/`OCall`; resolving them by CFG-run callees is H3.
        - EH: handler matching (`Catches`), and pending tail calls bypassing handlers. Both are
          covered by the theorems above, for all code.
        - Stack caveat: a native `return`/branch flow carries only the innermost stack, while
          `MStepC` keeps the whole frame stack. The projection relates them by `ProjRel` (junk
          prefix). Fixture `Wasm/Cfg/ExampleRetJunk` reaches the junk case on valid code
          (`ret_ne`, `ret_projRel`, `ret_top`).
        - Fixtures: `ExamplePending` (pending call answered by an exception or a trap; a tail call
          in a handler); `ExampleNested` (nested control, nested-loop continue, caught throw);
          `ExampleRetJunk` (exit across a frame with outer values).
      - **H3, the recursive CFG closure.** `cfgHOpenXPS`, the open module whose Wasm bodies run
        on the logged machine. It is defined from the machine, not as an alias of `wasmHOpenXPS`.
        Its closure `Shape.close cfgHOpenXPS` resolves callees through CFG-run bodies, which
        discharges `CX closedCallX`.
        - **H3-1, finished behaviours, done** (`Wasm/Cfg/CfgSession`). `cfgHOpenXPS` is
          defined from `MRunL` to a sink (`EndRel`, `exitFlow`, `endOfFlowS`), from `TailL` with
          the tail call's answer (`tailAnsS`), and from host calls.
          - `cfgHOpen_eq : cfgHOpenXPS = wasmHOpenXPS`, for all code, with every call form,
            exceptions on and traps keeping their store. It follows from `forward_sink`,
            `forward_tail` and `backward`; `backward`'s excluded `brk (k + 1)` has no framed end.
          - `cfgEvFun_eq : cfgEvFunXPS = wasmEvFunXPS`. So `wasmEvFunXPS`'s Core adequacy with
            hosts and exceptions (`wasmEvFunXPS_*_iff`) holds for the CFG closure.
        - **H3-2, pending host calls, done**: `CfgPendLXPS`, `cfgPend_iff`, and
          `cfgEvPend_eq : cfgEvPendXPS = wasmEvPendXPS`. They go via `pending_iff`,
          `forward_tail`/`backward` and `cfgHOpen_eq`.
        - Then H3-3: the divergent part (`closeDLog wasmHOpenXP LDLwXP`) and the productive part
          (`closeInfL wasmHOpenXP InfLwXP`). Together with H3-1 and H3-2 they give the CFG
          session triple equal to `sessionTripleXP`. Both parts use the **trap-erasing** canonical
          module `wasmHOpenXP` (`EvalLXPh` logs, `OCall`), through `DescPath`/`Descends`, through
          `close`, and through the per-function sets.
          - **Obstacle.** `evalLXPh_session`/`evalLXPS_canonical` convert only runs not ending in
            a trap. On trapping runs the relations differ: a callee trap is an answered entry
            in `EvalLXPS`, and an over-long value answer (`callCut`) in `EvalLXPh`, by the internal
            `HostClosingS.ToH`.
          - **H3-3a, done.** The trap cases are exported: `HostClosingS.evalLXPS_canonical_cut`
            (a callee-trap answer reads as a cut answer, for every over-long `ws`) and
            `evalLXPh_session_cut` (a cut run is a session run with the trap answer). The machine
            module is `CfgSession.cfgHOpenXP`, which reads machine logs canonically by
            `CanonRead`. Theorems: `cfgHOpenX_eq : cfgHOpenXP = wasmHOpenXP` and
            `cfgEvFunX_eq : cfgEvFunXP = wasmEvFunXP`.
          - **H3-3b, done: the session triple.** `CfgSession` defines the per-function sets
            from the machine: `LDLcfg` (the body diverges after a log by `MLogDivL`, the log the
            session reading of a canonical log) and `InfLcfg` (the body runs productively by
            `ProdL`, the stream the session reading of a canonical stream). From them it defines
            `cfgEvFunDXP := closeDLog cfgHOpenXP LDLcfg`, `cfgEvInfNXP := closeInfL cfgHOpenXP
            InfLcfg`, `cfgEvFunDXPS` and `cfgSessionTriple := (cfgEvFunDXPS, cfgEvPendXPS,
            cfgEvInfNXP)`.
            - `cfgEvInfN_eq : cfgEvInfNXP = wasmEvInfNXP`. By `cfgHOpenX_eq`, it suffices that
              `InfLcfg = InfLwXP`, which follows from `prodL_iff` because `OCall.toS` is
              injective.
            - `cfgEvFunD_eq : cfgEvFunDXP = wasmEvFunDXP`. This holds at the level of `closeDLog`,
              not per function. `logDiv_machine` gives `LDLwXP ⊆ LDLcfg`. For the converse,
              `machine_logDiv` extends the log by canonical entries answered by `closedCallXP`.
              These are value or exception answers, since a session reading has no trap answer.
              Each entry resolves to the empty host log in `close wasmHOpenXP`, by the new
              per-call header theorems `HostClosingInfXPBack.close_of_closedCallXP_vals` and
              `_throw`, which export `closed_good`. So the host log `qs ++ q` does not change.
            - `cfgEvFunDS_eq : cfgEvFunDXPS = wasmEvFunDXPS`, and
              `cfgSessionTriple_eq : cfgSessionTriple = sessionTripleXP`, which uses
              `cfgEvFun_eq` and `cfgEvPend_eq`.
            - With this, H3's equality with the store-retaining session triple is done. The
              closure's callees, including diverging and productive ones, now run on the CFG
              machine. Inside one body, the closed answers of `MLogDivL`/`CloseOk` and the
              diverging callees (`FunDivXP`) are still named by the native oracle. The closure
              equality covers them, but they are not defined from the machine. `cfgSessionTriple`
              and its theorems are kept with this scope; H3-4 removes the dependency.
        - **H3-4, done: the self-contained CFG closure** (`Wasm/Cfg/CfgClosure`).
          - Generic divergence over a call-answer predicate `A` and a callee divergence `D`:
            `StepKG`, `InfKG`, `CalleeDivKG`, `TailDivKG`, `MDivLG`, `FunDivLG`, `MLogDivLG`.
            `MachineLDiv`'s definitions are the instance at `CloseOk closedCallXP` and `FunDivXP`,
            by `rfl` (`stepK_eq` … `mLogDivL_eq`).
          - CFG instances. `cfgAns`: an internal call is answered when `([], ret b s₂)` is a
            behaviour of `cfgEvFunXPS`. `cfgFunDiv`: the greatest fixpoint of
            `D ↦ FunDivLG cfgAns D`, which gives mutual, coinductive callee divergence on the
            machine. `LDLcfgC`, `cfgEvFunDXPC`, `cfgEvFunDXPSC` and `cfgSessionTripleC` are
            defined over `MLogDivLG cfgAns cfgFunDiv`.
          - Theorems, with no hypothesis:
            - `cfgAns_eq : cfgAns = CloseOk closedCallXP`. The new direction is
              `session_of_closeOk`: every `closedCallXP` answer (values, exception, or trap with
              its store) is a session behaviour with the empty log, by least-fixpoint induction.
            - `funDivXP_of_post`: every post-fixpoint of `FunDivLG (CloseOk closedCallXP)` lies
              below `FunDivXP`, by native coinduction.
            - `cfgFunDiv_eq : cfgFunDiv = FunDivXP`, and the fixpoint law `cfgFunDiv_iff`.
            - `ldlcfgC_eq`, `cfgEvFunDC_eq`, and `cfgSessionTripleC_eq : cfgSessionTripleC =
              sessionTripleXP`.
          - Core, deterministic profile, under assumed typed-invocation hypotheses (`StoreOk`,
            `InvokeOk`, `StoreChkE (ehExt tags)`, `TagsOk`; for answers also `HostTyped`,
            `NativeHostSlice`, `HostSliceE`): `cfgFunDiv_iff_diverges`, and
            `cfgAns_trap_iff`/`_vals_iff`/`_throw_iff` (host-free Core runs, exact store).
        - **Definition dependency audit (H3).** These definitions name no native closed or
          divergent object (`closedCallXP`, `FunDivXP`, `EvalDivXP`, `LogDivXP`, `InfLXP`,
          `wasmEvFunXPS`, `sessionTripleXP`):
          - `cfgHOpenXPS`, `cfgEvFunXPS`, `CfgPendLXPS`/`cfgEvPendXPS`, `CanonRead`,
            `cfgHOpenXP`, `cfgEvFunXP`, `ProdL`, `InfLcfg`, `cfgEvInfNXP`;
          - `cfgAns`, `cfgFunDiv`, `LDLcfgC`, `cfgEvFunDXPC`, `cfgEvFunDXPSC`,
            `cfgSessionTripleC`;
          - the generic `Shape.close`, `closeDLog`, `closeInfL`, `SubstPre`, `Descends` and
            `DescPath`.

          These do name native objects: `MachineL.StepK`, `InfK`, `CalleeDivK`, `TailDivK`,
          `MDivL`, `FunDivL` and `MLogDivL` (`CloseOk closedCallXP`, `FunDivXP`), and through
          `MLogDivL` also `LDLcfg`, `cfgEvFunDXP`, `cfgEvFunDXPS` and `cfgSessionTriple`. They
          remain the scoped native instance.

          Every machine step (`MStepL`) runs a straight-line segment by the open logged relation
          `Abstract.EvalLXPS`. Its calls are open entries with arbitrary answers, and no oracle
          answers them.

          The audit is checked at build time by `Proofs/Wasm/Cfg/CfgClosureAudit`. Its scope:
          - **Definitional dependencies.** It walks the types and bodies of definitions, and the
            types of inductives, constructors and recursors, transitively. It does not follow
            theorem proofs. The build fails if a native closed or divergent object is reachable
            from any closure or instance-triple root.
          - **Fail closed, whatever the origin.** A reached constant whose body cannot be
            inspected fails the audit, from any module or topic. This covers opaque constants,
            axioms, missing names and unexposed imported bodies. The exceptions are kernel proofs
            (type is a `Prop`) and the explicit allowlist `trustedOpaque`, which is the trust
            boundary: `Classical.choice` and seven Lean-core definitions with unexposed bodies
            (`Lean.mkAtom`, `List.all₂`, `Nat.land`, `Nat.lor`, `Nat.repr`, `Nat.xor`,
            `String.Internal.append`).
          - **Axiom closure, proofs included.** For each root, `Lean.collectAxioms` must give only
            `propext`, `Classical.choice` and `Quot.sound`.
          - **Positive controls.** The native instance `cfgSessionTriple` reaches `closedCallXP`
            and `FunDivXP`. The audit must reject adversarial aliases of `closedCallXP`: an `opaque`
            alias in the same module, and, from another topic's module
            (`Wasm.Abstract.AuditControl`), an `opaque` alias and an alias whose body is not
            exposed. `sorryAx` must fail the axiom check.
        - **Remaining before all generic gaps can be called closed:**
          1. Typed-invocation hypotheses (`Wasm/Cfg/CfgValid`). These are now derived from
             `StoreOk` and `InvokeOk`, at the store's own tags:
             - the function type and exact parameter count (`funcType_of_invokeOk`);
             - `TagsOk` and `Ctx.Good` (`storeCtx_good_of_storeOk`).

             Corollaries: `logged_of_valid`, `proj_of_valid`, `cfgFunDiv_iff_diverges_valid` and
             `cfgAns_{trap,vals,throw}_iff_valid`.

             The checker's acceptance `StoreChkE (ehExt s.tags) s.funcs` is a fragment
             restriction, because `chkE` accepts only `xInstr` (`xInstr_of_flatChkE`) plus EH.
             It is now **discharged relative to validation and an explicit computable profile**
             (`Wasm/Interp/CheckComplete`):
             - `supported`/`storeSupportedB`: every flat instruction is in `xInstr`, and
               structured control recurses;
             - `chkE_complete`: every `InstrsOk` derivation in the profile is accepted, with the
               validated arity;
             - `storeChkE_of_storeOk (hs : StoreOk s) (hsup : StoreSupported s.funcs)`;
             - the decision `storeChkE_of_storeSupportedB`;
             - `typed_invocation_supported`.

             Validated code outside the profile is rejected: `floatBody` (`f32.const 0; drop`)
             validates in every context (`floatBody_ok`), the checker rejects it
             (`floatBody_rejected`), and `not_storeChkE_floatBody`. Host hypotheses are about
             the host, not the module.
          2. Instance sessions through the CFG closure (`Wasm/Cfg/CfgInst`). Nothing is
             redefined, and there is no fallback to Core sessions.

             Domain (`InstDom`, or `I.WellFormed` with `StoreSupported`): a well-formed
             instance, the store's functions in the checker profile, and **legal** host
             exceptions. An import answer `Answer.throw a` at a call with store `s` must have
             `a < s.exns.length` (`LegalRes`, `Answer.ThrowsBelow s.exns.length`, the legality
             in `IsInstance.adequacy`). Instances can raise, catch and leak exceptions in Wasm
             code, and can catch or leak legal host exceptions.
             - Hosts: `instHostQ I Q` is `instHost I` at typed callouts, keeping the answers that
               `Q` allows. Three cases: `instHostL` (`Q = LegalRes`), `instHostNT` (no
               exception) and `instHostU` (every answer). Without hypotheses:
               `hostTyped_instHostL`, `hostSliceT_instHostL`/`hostSliceT_instHostQ` (through
               `HostSliceT.of_funcs_eq`) and `hostSliceE_instHostL`. The `instHostNT` facts
               still hold as special cases.
             - `legalT` restricts a Core triple to host events whose thrown answer is legal at
               the event's call store. `instTripleL I P := viewTriple I (legalT (coreTripleSO P
               (instHost I)))` is `instTripleS I P` restricted that way. Import calls do not
               record their store, so the restriction is stated on Core events. Facts:
               `instTripleL_sub`, `noThrowT_sub_instTripleL`, and `instTripleL_eq_of_nil`
               (without imports it is `instTripleS`). `legalT_coreTripleSO_agree` shows that
               `legalT (coreTripleSO P (instHost I))` is `coreTripleSO P (instHostL I)`.
             - `instTripleL_agree`: on `InstDom I s`, `instTripleL I (profile o)` equals
               `cfgInstTripleL I := viewTriple I (openRestrict (coreHostRel (instHostL I))
               cfgSessionTripleC)`. The equality covers finished behaviours (values,
               exceptions, traps with their store), divergence, pending calls and productive
               streams.
             - `threadS_instTripleL_eq`: the same for the threaded sessions, from a start store
               in the domain. The domain persists (`instDom_of_reachL`, `funcs_of_reachL`,
               `supported_of_reachL`): a legal round is a Core run at the typed host
               `instHostL`, so `Abstract.Step.preservation_typed` keeps the configuration typed
               through caught host exceptions. Wasm `throw` only appends exception instances,
               and functions and tags are kept.
             - Families without fallback: `cfgInstSessionsL m` is the session of
               `cfgInstTripleL m.inst` at `m.inst.store`, defined for every instance.
               `legalSemD P` interprets each instance by its legal session.
               `legalSemD_sem_eq` and `denUD_legalSemD_eq_cfgInstSessionsL` hold on
               `CompIn (fun m => InstDom m.inst m.inst.store) c`.
               `core3SemD_sem_eq_cfgInstSessionsL` and `denUD_core3SemD_eq_cfgInstSessionsL`
               hold for instances without imports in the domain (`instSession_eq_cfgL`). The
               earlier `cfgInstSessions`, which fell back to Core, is removed.
             - Throw-free results are kept: `noThrowT_instTripleS_agree`, `threadS_noThrowT_eq`
               and `instSession_eq_cfg` against `cfgInstTriple`.
             - Audit: `CfgClosureAudit` also walks `cfgInstTripleL` and `cfgInstSessionsL`. It
               now exempts Prop-typed constants, since a module shows an imported theorem as
               an axiom. Example: `Strategy.nil_mem`, reached via `threadS`.

             Outside the domain the bridge's hypotheses fail. Without `I.WellFormed s` there is
             no `StoreOk`/`InvokeOk` for `InvOkXP`. Without checker acceptance there is no
             `StoreChkE (ehExt s.tags)`.

             **Dangling host exceptions: classified, forward direction done, converse open**
             (`Wasm/Cfg/DanglingExn`). For instances with imports, `core3SemD` uses
             `instSession`, which also contains logs where an import answers `Answer.throw a`
             with `a ≥ s.exns.length` (`Dangling s a`). These are outside `instTripleL`. No
             equality of `core3SemD` with a CFG family is claimed on such instances.

             - **Native and Core agree on the operational behaviour.** Both read `s.exns[a]?`
               through the same `CatchMatches`. A tagged clause never matches a dangling
               exception, and a catch-all clause always does (`catchMatches_iff`).
               `catches_iff` (native `Catches`) gives the resolution `danglingCatch a cs`:
               tagged clauses are skipped, `catch_all l` catches with no payload,
               `catch_all_ref l` pushes `ref.exn a` itself, and otherwise the exception is
               rethrown.

               Core matches this step for step. `step_handler_iff`/`step_handler_nil_iff`
               give the only step of a handler around `throwing a`. `steps_handler`/
               `handler_final`: every Core handler run that stops ends at
               `handlerOut a (danglingCatch a cs)`. `evalLXPh_try` is the native `try_table`.
             - **Uses of the reference.** `steps_throwRef`: `throw_ref` rethrows the
               reference, and the rethrow is resolved by `catches_iff` again.
               `not_refOk_exn`/`not_valOk_exn`: no type types the reference. So Core's
               `ref.test` answers `0` and `ref.cast` traps for every target type
               (`step_refTest`, `step_refCast`). These are outside the checker profile, which
               has no native counterpart. `not_resultTyped_throw` is the `HostTyped` failure.
               `not_storeOk_of_global`: code in the profile can store the reference in an
               `exnref` global (`catch_all_ref`, then `global.set`). The round then leaves a
               store that is not `StoreOk`, outside `InvOkXP`/`InstDom`.
             - **Aliasing.** Wasm `throw` allocates at `s.exns.length`, the least dangling
               address, in both semantics. `catches_alloc`: after that allocation, a tagged
               clause catches the formerly dangling address. Concretely on `hxMod`:
               `hx_catches_before`, `hx_core_alloc`/`hx_native_alloc` (both leave
               `hxThrown v`), `hx_catches_after`. A reference kept across the allocation then
               names the new exception. Both semantics read the store at handler time, so
               this does not separate them. It does rule out padding the store: padding moves
               the allocation address, which is observable.
             - **Fixture.** `callH_dangling_round`: on the CFG closure, `callH` with
               `h() ↦ throw 0` at `hxStore` ends with the uncaught exception `0`. The same
               answer from `hxThrown v` is caught (`callH_caught_existing`).
               `callH_dangling_core_U` is the same round as a Core run at `instHostU hxI`.
             - **Forward direction, without `HostTyped`.** `fin_sub`, `pend_sub`, `inf_sub`
               hold for any host in `HostSliceT`/`HostSliceE` on `InvOkXP`: every finished
               behaviour, pending call and productive stream of the native session triple is
               one of the open Core triple. `cfgInstTripleU_sub`: on `InstDom`, the CFG
               instance triple at `instHostU I` (`cfgInstTripleU`) is contained in
               `instTripleS I P`, componentwise.

             **The converse inclusion** (`instTripleS ⊆ cfgInstTripleU`): its legal part is stage 2
             below; the full inclusion, on well-formed stores in the checker's profile, is stage 3a
             below; the threaded sessions are stage 3b below. The original obstacle, in the proof: `HostClosingXP.back_all` (and the divergence and
             productive backward simulations, `HostClosingInfXPBack`, `HostEval`) carries
             `Sim.ContextTyped` across Core steps through `ContextTyped.steps_typed hT`. With
             a dangling reference on the stack, in a local or in a global, no `ConfigOk`
             holds (`not_valOk_exn`).

             **The relaxed invariant, done; the reverse simulation, open**
             (`Wasm/Cfg/DanglingTyped`, on `cfg/dangling-rev`). Aliasing is not harmless for
             `StoreOk`: a `throw` whose payload is `ref.exn s.exns.length` (a dangling host
             exception caught by `catch_all_ref`) allocates an exception whose field names itself,
             in Core and natively alike (`DanglingExn.step_throw_self`, `evalLXPh_throw_self`),
             and the store breaks `acyclicExns` (`not_storeOk_addExn_self`). So the invariant does
             not relax `RefOk`/`StoreOk` on the actual store. It types the actual frame and code on
             a **typing witness** `gst s T X`: the actual store with tags `T` (a prefix extension)
             and exceptions `X` (each actual exception at its address with its tag, fields equal up
             to exception addresses; pads with a fresh tag and no field at dangling addresses).
             - `ConfigOkD c`: supported profile (`ASupp`: no `ref.test`, `br_on_cast*`, aggregate
               instructions, `ref.cast` only at a defined type; frames and functions name only
               tags of the store), `HeapBelow`, and `Sim.ContextTyped` on some witness.
               `StoreOkD s`: the same for stores (`StoreOk` witness).
             - Preservation, every numeric profile: `ConfigOkD.step`/`steps` (host-free Core
               steps), `ConfigOkD.event` (one answer that keeps the store and types its values,
               any exception address), `ConfigOkD.evRun` (labelled runs against `HostTypedD`
               hosts), `hostTypedD_instHostU`. A step that keeps the exceptions is matched on the
               witness with the same code (`catchMatches_gst_iff`, `refOk_gst_iff`: every
               decision agrees), typed there by Core preservation; caught payloads differ only in
               exception addresses. A Wasm `throw` allocates at `s.exns.length` but at `X.length`
               on the witness; the next witness moves the exception to its actual address and
               redirects every exception field to the last pad, which excludes the cycles.
             - Entry and exit: `storeOkD_of_storeOk`, `configOkD_invoke`,
               `storeOkD_of_configOkD` (the end store of a round satisfies `StoreOkD`).
             - `FuncsSupp` constrains Wasm functions only (host functions push no frame).

             **Stage 2: entry domain, fixture, legal reverse inclusion; the dangling reverse
             simulation, open** (`cfg/dangling-rev-2`).
             - Entry domain. `DanglingTyped.funcsSupp_of_storeSupported`: a `StoreOk` store in the
               checker's instruction profile (`CheckComplete.StoreSupported`, `storeSupportedB`)
               has `FuncsSupp`. `configOkD_invoke_of_storeOk` (padded witness),
               `configOkD_of_supported`: on `I.WellFormed s ∧ StoreSupported s.funcs` (hence
               `InstDom`), every export question enters `ConfigOkD`. Checker acceptance alone
               does **not** suffice: `ExampleAlias.dc_instDom`, `dc_not_funcsSupp` (a validated
               spec instance, accepted by `storeChkEB`, whose function holds `ref.test` in dead
               code after `unreachable`, which the checker skips). So the relaxed domain is
               `StoreSupported`, not `InstDom`.
             - Validated aliasing fixture (`Wasm/Cfg/ExampleAlias`, `alMod`: a host import
               `h : [] → []`, a tag `$t : [exnref]`, `grab` = `try_table (catch_all_ref 0)
               (call h; unreachable)`, `run` = `call grab; throw $t`). Spec instance, `StoreOk`,
               `storeChkEB`, `storeSupportedB`, `InstDom`, `StoreOkD`. With `h()` answered by the
               dangling `throw 0` (an `instHostU` answer): natively on the CFG session triple
               (`run_round`, explicit logged-machine runs) and in Core at every profile
               (`run_core_U`, by `fin_sub`) the round ends with the uncaught exception `0` in
               `alEnd = alStore.addExn ⟨0, [ref.exn 0]⟩`; the allocation itself is
               `run_throw_core`/`run_throw_native`. `alEnd_not_storeOk`, `alEnd_storeOkD`.
             - Reverse inclusion, legal part only (`Wasm/Cfg/DanglingRev`). On `InstDom`, at
               `profile o`: `instTripleL I ⊆ cfgInstTripleU I ⊆ instTripleS I` per question and
               componentwise (`instTripleL_sub_cfgInstTripleU` with `cfgInstTripleU_sub`). Without
               imports the ends coincide (`instTripleS_agree_cfgInstTripleU_of_nil`, trivially:
               there is no host call).

             **Stage 3a: the backward simulations factored through an interface; the dangling reverse
             inclusion and the per-question equality** (`cfg/dangling-rev-3`).
             - Interface (`Interp.CtxInv`, `Interp.BackInv`, `Wasm/Interp/CtxInv`). `CtxInv H`: an
               invariant `CT` of configurations with the context decompositions `suffix`, `label`,
               `handler`, `frame`, preservation under host-free steps at every profile (`step`), and a
               typing witness (`wit`): the same frame and code `Sim.ContextTyped` on the store with tags
               `T` extending the store's and exceptions `X`, with every defined-type cast
               (`m.instRef ⟨b, .typeIdx y⟩`, what `call_indirect` performs) deciding as on the actual
               store. `BackInv H` adds a host class `HostOk` with preservation along Core runs
               (`steps_host`), closure under answering one call by a trap in its store (`hostOk_trap`),
               and divergence through host-free steps (`through`, on the actual store).
             - Facts read off the witness, proved once (`Proofs/Wasm/Interp/CtxInv`): `tyFuncs`,
               `tyTypes_callee`, `evalFlat_progress` (`evalFlat_gst`: `evalFlat` reads no tag and no
               exception), `truthy_progress`, `callRef_top`, `returnCallRef_top`, `throwRef_top`,
               `indirect_res` (`indRes_wst`), `typeArity_of_callRef_site`, `tailAnn_typed`
               (`tailRes_wst`), `entry_of_ref_site` (from `step`, `frame`, `label`).
             - The typed problems (`CtxInv.TypedP`, `CallTypedP` and their lemmas, `PTyped`;
               `invoke_callTyped`, `PDivIff`), the logged backward simulation (`HostClosingXP` `Back*`,
               `PendRun`) and the divergent/productive backward simulations (all of
               `HostClosingInfXPBack`) are proved once for every `BackInv`. `diverges_through_steps`,
               `evDiv_through_steps`, `coreInf_not_diverges` are derived from `through`.
             - Typed instance: `Interp.ctxTyped`, `Abstract.backTyped` (`Sim.ContextTyped`, `HostTyped`).
               Every existing public theorem of `HostClosingXP.Thms` and `HostClosingInfXPBack.Thms` is
               re-derived at `backTyped` with an unchanged statement (an invocation enters through
               `ctxTyped_invoke`); the old `Interp.TypedP` lemmas are the instance `ctxTyped`. Generic
               statements: `BackInv.evRun_wasmEvFunXP_vals`/`throw`/`trap`, `evRunN_back`,
               `evRunN_back_vals`, `funcType_of_callRef_cfg`, `funcType_of_returnCallRef_site`,
               `evRun_pendXP`, `evRun_wasmEvFunDXP_div`, `coreInf_wasmEvInfNXP`, and
               (`Abstract/BackInv`) `coreBehSXP_mem`, `coreCallout_mem`, `coreInf_mem` (Core behaviours,
               callouts and productive runs are session behaviours).
             - `through` for invariants whose store is not `StoreOk`: `BackInv.diverges_through_of`
               (invariant kept by host-free steps, stores with closed-valid principal types `StoreTy`, code
               with the interpreter's cast side conditions); the interpreter's exactness reads `StoreOk`
               only through `Ref.type?_tyOk`, and is stated at that minimal hypothesis in place
               (`SingleThreaded.Exec.interpHead_exact_of_ty`/`interpHead_complete_of_ty`,
               `referenceStep?_complete_of_ty`, `refOk?_complete_of_ty`/`refOk?_iff_of_ty`;
               `Execution.Core.refOk?_complete_of_ty`/`refOk?_iff_of_ty`/`RefOk.principal'_of_ty`),
               the `StoreOk` statements being their corollaries with unchanged statements.
             - Relaxed instance `DanglingBack.backD`: `ConfigOkD` against `HostTypedD` hosts. Fields:
               `ConfigOkD.suffix`/`label`/`handler`/`frameHole` (the hole of a supported context is
               supported), `ConfigOkD.step`, `ConfigOkD.wit` (`refOk_gst_iff`: defined-type casts are
               supported), `ConfigOkD.steps_host`, `hostTypedD_trapAt`, `ConfigOkD.through`
               (`storeTy_of_ghost`: an existing exception's principal type is `exnref`, every other
               reference has its witness type). The witness is used only for typing facts that read no tag
               and no exception instance; no operational step is taken on it.
             - **Reverse inclusion** (`DanglingBack.instTripleS_sub_cfgInstTripleU`): on `I.WellFormed s`
               with `CheckComplete.StoreSupported s.funcs`, at `profile o`, every finished behaviour
               (values, uncaught exception, trap in its store, divergence after a log), pending call and
               productive stream of `instTripleS I (profile o)` (host `instHost I`, dangling throws
               included) is one of `cfgInstTripleU I` (host `instHostU I`). With #988
               (`cfgInstTripleU_sub`): **`instTripleS_agree_cfgInstTripleU`, per question `AgreeAt` on all
               four observations.** The supported profile is the stated hypothesis `StoreSupported` (it
               excludes the instructions where Core's decision on a dangling reference differs from the
               witness's).

             **Stage 3b: threaded sessions on a relaxed domain** (`Wasm/Cfg/DanglingSession`,
             `cfg/dangling-rev-4`). Deterministic profile `profile o` for the backward direction; the
             forward direction and the domain's preservation hold at every profile. Every profile,
             with profile-free functions: stage 3c below.
             - What a round changes in the real store. `instHost I` and every `instHostQ I Q` keep the
               store (`NodeBridge.storePreserving_instHost`); only Wasm steps change it.
               `DanglingSession.step_store` (every host-free Core step, every profile): functions and
               tags kept, exceptions only appended (`throw`), `TagsOk tags` kept; `evRunQ_store`: the
               same along labelled runs at `instHostQ I Q`. Globals, memories, tables, structs and
               arrays are not constrained beyond the witness typing of `StoreOkD`.
             - Counterexample (the raw domain is not kept): `al_round`, `reach_alEnd`: on
               `ExampleAlias`, `run()` with `h()` answered by the dangling exception `0` is a finished
               round of `instTripleS alI P` from `alStore` (`InstDom`) to `alEnd`, which is not
               `StoreOk` (`not_instDom_alEnd`); `instDomD_alEnd`: it is in the relaxed domain.
             - The domain `InstDomD I s` (strictly weaker than `StoreOk`, no `acyclicExns`): the function
               clauses of `WellFormed` (`FuncsWF`), `StoreChkE (ehExt s.tags) s.funcs`, **real
               `Interp.ExnsOk s.tags s`** (every real exception's tag is a tag of the store, with its
               field count), and `StoreOkD s`. `exn_typed` relates them: a real exception's tag is a real
               tag of parameter types `ts`, and its fields are, up to exception addresses
               (`ValApprox`), values of types `ts` on the witness. Entry: `instDomD_of_supported`
               (`WellFormed` + `StoreSupported`), `instDomD_of_instDom` (`InstDom` + `FuncsSupp`).
               Preservation: `domD_of_round` (every finished round, store-keeping traps included),
               `domD_of_reach`, `funcs_of_reach`.
             - Forward direction without `StoreOk`: `DanglingExn.fin_sub_of`/`pend_sub_of`/`inf_sub_of`
               (store check, `TagsOk`, typed invocation); #988's `fin_sub`/`pend_sub`/`inf_sub` are
               their corollaries with unchanged statements. On the domain: `cfgInstTripleU_sub`,
               `sub_cfgInstTripleU` (via `configOkD_of_domD` and `backD`), **`agree`** (per question,
               `AgreeAt` on all observations).
             - **Sessions**: `threadS_eq`, `instSession_eq`, `instSession_eq_of_supported`:
               `threadS (instTripleS I (profile o)) s₀ = threadS (cfgInstTripleU I) s₀` (`=
               cfgInstSessionU I s₀`) from `InstDomD I s₀`, by `StratSession.threadS_congr` at every
               store reachable by the instance session (each in the domain by `domD_of_reach`); this
               covers finite plays, pending plays, divergences after a log and infinite plays. Infinite
               plays are either finished rounds followed by a productive stream of the current round
               (at a reachable store: the third component of `agree`) or coherent infinite sequences of
               finished rounds: `infRounds_iff` (round `k` starts at a store reachable by the first `k`
               rounds, `reach_of_infRounds`, so in the domain; induction on `k` in both directions).
             - What follows: the raw instance session only (`instSession`). `core3SemD` does not feed
               host throws to instance sessions (#995), so there is no `core3SemD`/`cfgSemD` corollary.
               `cfgInstSessionU` is a root of `CfgClosureAudit`.
             - Ledger: `HostEval` and `FullObsNative` still use the old typing
          Open technical debt, not accepted duplication: `Proofs/Wasm/Abstract/BackInv/Through.lean` still copies
          about 100 lines of `interpHead_exact`, `refOk?_complete` and `referenceStep?_complete`, at closed-valid
          types. Their in-place generalization (#1074, Part A) is blocked by `CI time budget`. Editing the widely
          imported `SingleThreaded/Exec` and `Execution/Core/Exec/ValCheck` headers puts the compiler-explorer
          closure in scope. Its selected post-build checks then exceed the 240 s non-compile limit, measured at
          370.5 s:
          - 9 `leanchecker` replays, about 148 s;
          - process gates and the Cerberus oracle, about 82 s.

          Parallel replay was measured and rejected. Over the same 9 targets, sequential takes 448/450 s,
          4-way 400 s and 2-way 503 s, with peak RSS of 1.5 to 7.9 GiB per replay. The work is bound by I/O, not
          CPU. No budget exception has been granted.
               (`Sim.ContextTyped`/`HostTyped`) and are not on the instance path.

             **Stage 3c: every numeric profile** (`Wasm/Cfg/ProfileFree`, `Wasm/Cfg/DanglingProfile`,
             `cfg/profile-indep`). The backward results of `CfgInst`, `CfgLegal`, `CfgLegalComp`,
             `DanglingBack` and `DanglingSession` now also hold at **every** `Numerics.Profile` `P`
             (`nd`, `relaxed`, `nan`, `grow` arbitrary), on start stores whose functions are
             profile-free.
             - Where determinism was used, and why it was inessential. The deterministic profile
               enters the backward proofs only through Core steps of supported code: same-log runs end
               alike (`HostClosingXP.BackDet` `evRunN_event_det`, `evRun_det_end`, `TrapExact`
               `evRun_trap_det`); a stuck or host-call end excludes divergence on the same log
               (`DivBase.noDiv_of_evRun`, `InfSplit.noInf_of_evRun`, `HostClosingInfXPBack.Reach`); the
               native divergent and productive witnesses follow the Core run by `Det.DStep` chains
               (`InfGoal` `Lifts`, `InfLoop`, `InfWhole`, `trace_of_tgChain`); `BackInv.through`
               (`diverges_through_of`, `HostCall.diverges_through`); and, for sessions, `StoreDet`
               (`storeDet_instTripleS`, used by `mem_inf_instSession`, `instSession_eq_iff` and the
               `restrictLog` pullbacks of `CfgLegal`; the `DanglingSession` equalities use none). All of
               these are facts about Core steps of the code that runs. No use needs determinism of
               a profile beyond that.
             - The step lemma (`ProfileFree.step_profile`, any host). `PSens`: the instructions whose
               Core rules read the profile (float unary and binary operations, conversions, vector
               operations other than `v128.const`, `memory.grow`, `table.grow`). On code without them
               (`IFree`/`AFree`; `select`, every call form including `call_indirect`, `call_ref` and
               tail calls, references, type tests, aggregates, `throw`/`throw_ref`/`try_table`,
               labels, handlers and frames are allowed), a step at `P` is a step at every `P'`. The
               invariant `ConfigFree` (code and `FuncsFree` functions) is kept by every step against
               a `HostFree` host (`step_free`; store-preserving hosts such as `instHost I`), and
               `StoreSupported` gives `FuncsFree` (`funcsFree_of_storeSupported`).
             - Lifts with the same witnesses (no choice, no compactness): `hEvStep_profile`,
               `evRun_profile_iff`, `diverges_profile_iff` (the same trace), `coreInf_profile_iff` (the
               same segmented run), `coreObsLXP_profile_iff` (every `FullObs`),
               `coreBehSXP_profile_iff`, `coreCallout_profile_iff`, `coreTripleSO_profile`.
             - Instance level: `instTripleS_profile`, `instTripleL_profile` (`AgreeAt`, at a store with
               `FuncsFree`); every finished round keeps `FuncsFree` (`funcsFree_of_round`), so
               `instSession_profile`, `threadS_instTripleL_profile`, `threadS_noThrowT_profile`;
               `storeDet_at`; `mem_inf_instSession_P`.
             - Derived at every `P`: `instTripleS_agree_cfgInstTripleU_P` (`WellFormed`,
               `StoreSupported`), `agree_P`, `threadS_eq_P`, `instSession_eq_P`, `infRounds_iff_P`
               (`InstDomD` and `FuncsFree`), `instSession_eq_of_supported_P` (`WellFormed`,
               `StoreSupported`); legal and throw-free: `instTripleL_agree_P`,
               `noThrowT_instTripleS_agree_P`, `threadS_instTripleL_eq_P`, `threadS_noThrowT_eq_P`
               (`InstDom` and `FuncsFree`); components: `core3SemD_sem_profile`,
               `legalSemD_sem_profile`, `denUD_core3SemD_profile`, `denUD_legalSemD_profile`,
               `denUD_cfgSemD_eq_core3_P`, `denD_cfgSemD_eq_core3_P` (`CompIn InstDom` and
               `CompIn FuncsFree`); for every `BackInv`: `coreBehSXP_mem_P`, `coreCallout_mem_P`,
               `coreInf_mem_P` (with `FuncsFree` and a `HostFree` host).
             - Restriction. The hypothesis is syntactic. `InstDom` and `InstDomD` do not give
               `FuncsFree`: the checker skips code after an instruction that never falls through, so
               a profile-sensitive instruction may sit in dead code. The statements there take
               `FuncsFree` (or `StoreSupported`) explicitly. A global `StoreDet (instTripleS I P)` is
               not claimed, since it quantifies over stores whose functions read the profile; only
               `storeDet_at` is proved. On profile-free stores no backward statement needs a
               deterministic profile, so there is no counterexample to give there.
               Characterizations stated through `LegalPlay`/`restrictLog` (`mem_legalSession` and its
               variants, `legalSession_eq_iff`, `instSession_eq_iff`) were not restated at every
               profile.

             **The legal typed canonical object** (`Games/Abstract/SessionLegal`,
             `Wasm/Abstract/NodeLegal`, `Wasm/Cfg/CfgLegal`). The legal domain is stated on
             the plays of the instance session, on its own interface `I.E ↠ ssig I.exports`.
             It is not stated only on Core events. Deterministic profile `profile o`.
             - Game level: `SessionLegal.restrictLog Lg t` keeps the behaviours, call prefixes
               and streams of `t` whose logs satisfy a prefix-closed, store-dependent log
               legality `Lg s a c`. `PLegal`/`SLegal` are the play predicates: the store is
               threaded by the session automaton `StratThread.TSt`. For `StoreDet` triples
               without plain traps, `mem_threadS_restrictLog`, `div_threadS_restrictLog` and
               `inf_threadS_restrictLog` make `threadS (restrictLog Lg t)` the exact pullback
               of `threadS t`: finite plays are `PLegal` (legal before each Proponent move,
               since a strategy is receptive), divergences are `SLegal`, and infinite plays
               have `PLegal` prefixes. `pLegal_snoc` covers pending calls.
             - The call store: `NodeLegal.RoundLegal I P Q s a c` says each answer `x.2` of
               the log is allowed by `Q` at the store `s'` of every hidden instance state
               `.waiting a s' t x.1` that waits for it. `instTripleQ_agree`: at every store,
               `instTripleQ I (profile o) Q := viewTriple I (evRestrict Q (coreTripleSO …))`
               equals `restrictLog (RoundLegal …) (instTripleS I (profile o))` on behaviours,
               call prefixes and streams. Core event stores are the `.waiting` stores, and
               `Path.functional` makes those unique. `instTripleS` is saturated
               (`satP_instTripleS_sub`). `instTripleL` is `instTripleQ` at `LegalRes`, by
               `rfl` (`CfgLegal.instTripleL_eq`).
             - Node sessions (`CfgLegal.LegalPlay`, `LegalPlayD`; read through
               `roundLegal_iff`, `Answer.ThrowsBelow s'.exns.length`): `mem_legalSession`,
               `pending_legalSession`, `div_legalSession` and `inf_legalSession` show that
               `threadS (instTripleL I (profile o)) s₀` is exactly the `LegalPlay` part of
               `instSession I (profile o) s₀`. `mem_cfgSession` and its `pending`, `div` and
               `inf` variants give the same for the CFG-built `threadS (cfgInstTripleL I) s₀`
               on `InstDom I s₀`.
             - Nodes of the component semantics: `mem_legalSemD_sem` and `div_legalSemD_sem`
               show that a play or divergence of a `legalSemD` node is the visible part of an
               interaction through `importH`/`exportH` whose hidden instance play is a legal
               play of the `core3SemD` session. `legalSemD_le` gives `legalSemD ≤ core3SemD`
               node by node. `CfgLegal.cfgSemD := threadSemSD cfgInstSessionsL` (an audit
               root) satisfies `cfgSemD_sem_eq`, `mem_cfgSemD_sem` and `div_cfgSemD_sem` on
               the domain.
             - Components: `denUD_legalSemD_le` gives `c.denUD (legalSemD _) ≤ c.denUD
               (core3SemD _)` for every `c`. `denUD_cfgSemD_eq` and `denUD_cfgSemD_le` hold on
               `CompIn (fun m => InstDom m.inst m.inst.store) c`.
             - Injectivity (`CfgLegal.legalSession_eq_iff`, `cfgSession_eq_iff`; generic
               `SessionLegal.threadS_restrictLog_eq_iff`): legal sessions of `I` are equal
               iff their start stores are `StratThread.ObsEq` for the legal parts
               `restrictLog (RoundLegal …) (instTripleS …)`. This is the legal counterpart of
               `InstSession.instSession_eq_iff`. It is not compared with Core 3.0 session
               equality, because legality reads hidden call stores.
             - **Exact component legality** (`Games/DivCompAns`, `Wasm/Abstract/NodeLegalComp`,
               `Wasm/Cfg/CfgLegalComp`). The import coercion `importH m` of every `semOfSD`
               node answers with `payloadAnswer`, i.e. `.values` or `.trap` and never `.throw`
               (`NodeLegalComp.toResult_payloadAnswer_ne`). `LegalRes` only constrains
               exceptions, so every such answer is legal at every store, including the
               importer's `.waiting` store (`answersIn_importH`, `nonExnLegal_legalRes`). It
               asks nothing of values, arity, references or stores. Wiring, `ext`, nested
               instances and hidden composition all act above `importH m`. The generic law
               `DStrategy.comp_eq_of_ansPart` covers finite plays, local divergence, hidden
               chatter and infinite plays. Its witnesses are coherent: `InfInteraction.ansRight`
               and `ansLeft` lift, and `ofLe` lowers, with the same chains. Combined with
               `ansPart_comp` and `SessionLegal.sLegal_of_lAnsIn`, it gives:
               - `CfgLegalComp.legalSemD_eq : legalSemD (profile o) = core3SemD (profile o)`
                 at the node interface, hence `denUD_legalSemD_eq` and `denD_legalSemD_eq` for
                 every component, with no domain restriction.
               - `nodeHidLegal`, `compLegal`: every hidden node interaction of every component
                 is legal at every importer point, at any profile. `mem_`, `pending_`, `div_` and
                 `inf_denUD_legalSemD_iff` (chatter included) are the exact pullback with
                 `CompLegal`.
               - Node forms with explicit witnesses: `mem_legalSemD_sem_iff`,
                 `div_legalSemD_sem_iff` and `inf_legalSemD_sem_iff`. In
                 `NodeLegalComp.inf_inner_lift`, one coherent inner infinite interaction has
                 legal hidden instance stages.
               - `denUD_cfgSemD_eq_core3` and `denD_cfgSemD_eq_core3`: on
                 `CompIn (fun m => InstDom m.inst m.inst.store) c`, the CFG-built denotation
                 equals the `core3SemD (profile o)` denotation, imports included.
             - Owner interface (`docs/projects/component-semantics.md`, 0e76ca84): see
               `Wasm/Cfg/CfgLegalOwner` for the exact obligations. A legal reference injection
               needs the reference relation stated at the same `payloadAnswer` boundary. Nothing
               in the owner's modules is changed.
             - **Not claimed.** The equalities above are at the IR node boundary. On the session
               interface `ssig`, before `importH`, an environment may answer `throw a`, and the
               legal session drops the dangling throws. Unrestricted equality of `instSession`
               with a CFG reading is **not established** on such environments, and no
               inequality is proved either. The node-level equality does not prove
               native/Core equality on arbitrary throwing `ssig` environments. The raw dangling
               backward bridge (`DanglingExn`) is separate. By design of the IR boundary there
               is no cross-node exception propagation: an escaping exception becomes a trap
               (`answerPayload`). Nothing here covers a reference interface that passes
               exceptions between instances.
          3. **Regressions, done** (`Wasm/Cfg/ExampleRegress`). One validated store (`rgMod`,
             one host import `h : [i32] → []`, a spec instance, `StoreOk`, `StoreChkE (ehExt
             tags)` by `storeChkEB`). Each fixture is proved on the CFG closure directly, by
             explicit logged-machine runs resolved by `Shape.close`/`closeInfL`, not via
             `cfgSessionTripleC_eq`:
             - recursion through a host: `rec_run` and `rec_log`, where `rec k` has the host
               log `h(k), …, h(0)`, one call per depth;
             - trap then resume: `trap_then_get`, where `trap` writes a global and traps, and
               the session continues and `get` reads `42`;
             - productive host interaction: `pump_prod`, `pump_stream`, `pump_session`, a loop
               with the exact stream `h(0), h(1), …`; `regress_play` chains `trap`, `get`
               and the infinite `pump` play from the trap's store in one session.
          4. **Host exceptions and traps under `try_table`, done** (`Wasm/Cfg/ExampleHostExn`).
             One validated store (`hxMod`: tag `$e : [i32]`, host import `h : [] → [i32]`, a
             spec instance, `StoreOk`, `StoreChkE (ehExt tags)` by `storeChkEB`), proved on the
             CFG closure by explicit logged-machine runs:
             - pending calls: `callH_pending` and `tailH_pending` give the same
               `cfgEvPendXPS` observation (empty log, `h()`). The machine shows the
               difference: `callH` reaches the call under the `try_table` handler frame
               (`ReachL`), while `tailH` ends in a pending tail call (`TailL`). `pend_session`
               shows the pending call after a completed round.
             - caught host throw: `callH_caught`, where the host allocates and throws an
               exception of `$e` and `catch 0 0` returns its payload, in the host's store.
             - tail host throw bypasses the handler: `tailH_uncaught`, where the same answer
               through `return_call` ends `.ret (.inl (.inr 0)) s'`. `exn_session` puts the
               caught and the uncaught round in one session.
             - host trap is not caught: `trapH_trap`, where `catch_all` lets a host trap
               through and the function ends `.ret (.inr ()) s'`. `trapH_caught` shows the
               same `catch_all` catching a throw. `trap_session` resumes after the trap.

             Not covered: the validity of the host-answered stores (`hxThrown v`).
        - Equality with the store-retaining session closure `wasmEvFunXPS`/`sessionTripleXP`
          (not the trap-store-erasing `wasmEvFunXP`): done (`cfgEvFun_eq`,
          `cfgSessionTriple_eq`).
        - Then the instance session with imports and exceptions, via the existing Core adequacy
          (`wasmEvFunXPS_*_iff`, `wasmEvPendXPS_eq`, productive streams) and NodeBridge, on a
          typed fragment with the exception checker (`ehExt tags`).
        - Regressions: recursion through a host, trap-then-resume, productive host interaction:
          done (`Wasm/Cfg/ExampleRegress`, item 3 above). Host exceptions and traps under
          handlers, pending calls versus pending tail calls: done (`Wasm/Cfg/ExampleHostExn`,
          item 4).

**Also tracked:** byte occurrence (a function's code entry in its module's bytes, for the valid
serializer profile) is not started. Typing completeness for validated bodies is done
(`bodyIfaces_complete`).

## CFG variants: traps and raises

The legacy graph (**L**, `Cfg.Edge`) is kept unchanged, with its APIs, examples and
kernel-checked tables. The variants below are related to it by theorems, not by relabelling.

- **TE: traps as an abrupt outcome, raises as control.** This is the proposed default.
  - **Done** (`Silmaril.Wasm.Cfg.Variant`): `EdgeTE` is the legacy edges without the `trap`
    sink. `mustTrap` marks a block ending in `unreachable`; that is a terminal, non-returning
    outcome, not a state effect.
  - `edge_iff_te`: a legacy edge is exactly a TE edge, or the `trap` edge of a must-trap block.
  - `succOf_trap_iff`: only `unreachable` has a `trap` edge, because labels and continuations
    never resolve to `trap`.
  - `succTE_of_mustTrap`: a must-trap block has no TE successors.
  - May-trap marks (`Effect.mayTrap`) stay distinct from `mustTrap`.
  - **Next:** handler-resolved raise edges. A `throw`, or a call that may raise, gets edges to
    the `catch` targets of enclosing `try_table`s, innermost first, with an escape edge unless
    a `catch_all` covers it. A caught throw resumes; it is never terminal. These edges are to be
    proved against Core's `HANDLER` rules in the operational bridge.
- **AE: traps and raises both as outcomes, with resolved handlers.** This is the default the
  user chose.
  - **Done** (`Silmaril.Wasm.Cfg.Variant`): `succAE`/`EdgeAE` drop the `trap`/`raise` sinks and
    the `try_table` catch edges. `mustTrap`/`mustRaise` mark the abrupt outcomes, and
    `raiseHandlers` lists the possible handlers (enclosing catches, innermost first, then the
    caller unless a `catch_all` intervenes).
  - `edge_iff_ae`: a legacy edge is an AE edge, a must-trap `trap` edge, a must-raise `raise`
    edge, or a catch edge.
  - Explorer data: `variants["all-effects"]` and `variants["all-effects-instr"]`, with
    `default: "all-effects"` (`tools/wasm-pages/SCHEMA.md`).
  - The handler outcomes follow #230: a raise is control resumed by its handler, a trap is
    abrupt. They are to be proved against Core's `HANDLER` rules in the operational bridge.
- **Maximal blocks** (`Cfg.canMerge`, `canMerge_succ`, `canMerge_pred`,
  `canMerge_not_entry`): AE blocks are merged along a fallthrough whose target has no other AE
  or handler predecessor and is not the entry. The explorer's default is
  `variants["all-effects-max"]`, which keeps each member's identity (`members`).
  `Cfg.Maximal`: merges are functional and injective (`canMerge_functional`, `canMerge_inj`),
  so the merged blocks are disjoint chains. The contracted graph's edges are exactly the AE
  edges other than the merged fall-throughs (`mem_maxFlow`), plus every handler edge
  (`mem_maxHandler`). This is a graph construction, not an execution theorem.
- **Graph analyses are per variant.** Removing a sink changes no dominator of the remaining
  nodes, since a sink lies on no path to another node; this is to be proved as a graph lemma.
  It does change postdominators and exit reachability, so those are stated per variant.
- **Renderer:** TE's new edge kinds get IDs in `tools/wasm-pages/SCHEMA.md` with a version bump,
  coordinated with the explorer's renderer, before any page switches its default.


## Paused: F6, the CFG ↔ `BodyM` correspondence (owner 0e76ca84)

F6 of the typed Wasm/CFG → `BodyM` functor plan is **paused**. It is not forgotten: it resumes after the critical component work, or when the coordinator reassigns it.

- **Done around it:** the CFG operational bridge, both directions, for typed trees at a deterministic profile with no host (`Cfg.Bridge.bridge_fwd`, `bridge_bwd*`, `Cfg.BridgeCfg.machine_native`; #786 #790 #791 #793 #795). The `BodyM` side is the canonical semantics `CallXP` with `ExposeP.denListXP`, `FunctorP.OpEquivP` and `BodyStrat.toDStratBody_denL_iff`.
- **Exact goal:** for a typed function body `es`, the block-CFG runs of its graph, labelled with call events, are the logged `EvalLXP` runs of `es`. As corollaries:
  - CFG-trace equivalence of two bodies coincides with `OpEquivP`;
  - the CFG view has the same canonical `DStrategy` (`toDStratBody (denL es)`).
- **Hypotheses expected:** typed trees; a deterministic profile for the bridge; the scope of #786–#795 (no host, and pending tail calls answered by every oracle).
