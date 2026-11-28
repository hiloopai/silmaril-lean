# Sea of Nodes source-to-Lean coverage

This ledger records the C1 source inventory, C4 bridges and supporting
Sea of Nodes results. The original ledger used Silmaril `main` at
`08337a41d017aeec6653dcaeb39b5a24ae0f62b5`. The coverage below credits
merged results through the [theorem cutoff][coverage-cutoff] at
`6e351345b6f5497ed986813c6abda35742b83ea5`.
Each source row keeps its full obligation. The coverage column names the
proved portion and records the remaining scope. The [proof sequence](#proof-sequence)
continues to track the broader work. The initial Lean comparison used
`f32f986f8780a179d01365ace2e92dfc01c0b8e9`.

A targeted pass on top of that cutoff credits three PRs that landed loop-aware
GCM and cyclic GVN results: [#4895][pr-gvn-dead-header] and
[#4934][pr-gvn-dead-header-cleanup] check and repeat dead-header-write erasure
in one two-backedge quad loop family, and [#4918][pr-gcm-compact-exit-phi]
reads explicit Φ rows from a compacted loop exit. These sit on `GCM.LoopForest`,
`GCM.LoopHoist` and `GVN.Cyclic`, all introduced the same day, each on its own
admitted CFG or loop-region shape (see the Start Here and PLDI/thesis rows
below).

A second pass the same day found that this ledger's GCM rows were already
considerably more stale than the above: `GCM.EarlyPlacement`, `GCM.LatePlacement`
and `GCM.Dominance.Tree.Synthesis` (new that day) and the pre-existing
`GCM.NaturalLoop`/`GCM.LoopPlacement`/`GCM.Corridor` chain (from PR #3716)
already give a constructive, exact dominator-tree synthesis and a constructive,
checked Schedule Early/Schedule Late/loop-depth-ranked placement choice for one
pure total floating node over a successor-closed finite CFG inventory — none of
it previously credited here. The §§2/2.1–2.4 rows below now cite it. This pass
still does not re-audit the rest of the ledger against current `main`; in
particular `GCM.Hoist`, `GCM.Sink` and the thesis/Quads/Simple rows beyond
§§2–2.4 were not re-checked.

## Start here

### Straight-line pure producers

```lean
import Silmaril.SSA.SeaOfNodes.Pure.Thms
import Silmaril.SSA.SeaOfNodes.MLIR.Thms
```

- Build a `Pure.Program` from a typed producer table in dependency order
  and a single returned wire. `Program.lower_run` identifies the singleton
  RVSDG result with source evaluation for every typed input in a total
  primitive model. By `Equation.satisfaction`, a translated equation holds
  in the induced RVSDG model iff the native results agree at every typed input.
  [Definitions][son-pure-defs] · [Theorems][son-pure-thms] · [Worked example][son-pure] · [#3188][pr-pure]
- For scalar Arith, `SeaOfNodes.MLIR.lower` takes a `Diamond.Dataflow` and a
  selected word-valued wire. `lower_denote` identifies its value with the
  single-block MLIR result for every typed input. This profile has
  positive-width bitvectors, constants, add and multiply with empty overflow
  flags. The block keeps one binding per producer, including shared producers.
  [Definitions][son-scalar-defs] · [Theorem][son-scalar-thms] · [Worked example][son-scalar] · [#3175][pr-scalar]

### Pure branch diamond

```lean
import Silmaril.SSA.SeaOfNodes.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Thms
```

- `Diamond.Graph` has one Boolean If, two distinct projections entering
  one Region in either order, and a single returned Phi. Its unpinned total
  producers are acyclic. `Graph.lower_returns_iff` preserves and reflects
  each finite return in the generated RVSDG γ graph. `Graph.lower_denote`
  gives the corresponding categorical equality in types.
  [Definitions][son-diamond-defs] · [Theorems][son-diamond-thms] · [#3135][pr-diamond]
- `Diamond.LambdaSSA.lower` emits a CFG for this one scheduled diamond.
  `lower_hasType` checks its original input context and single typed
  external exit. `edge_transfer_iff` relates the selected Phi occurrence
  to the transfer into the sole join. `lower_eval_iff` characterizes every
  finite target evaluation by external exit zero, the encoded source value
  and unchanged ambient state. `returns_iff` relates that evaluation to the
  native return relation. General typed CFG correspondence remains open.
  [Definitions][son-diamond-ssa-defs] · [Theorems][son-diamond-ssa-thms] · [Source note and example][son-diamond-ssa] · [#3211][pr-diamond-ssa]
- `Diamond.Institution.inst` gives native diamond equations over a fixed
  data-sort alphabet and the Boolean predicate sort. Its signature maps
  preserve each opcode’s ordered input sorts and single result sort.
  `denote_mapGraph` and `Equation.satisfaction` prove the native
  denotation and satisfaction laws for opcode relabelling and model reduct.
  [Definitions][son-diamond-inst-defs] · [Theorems][son-diamond-inst-thms] · [Worked example][son-diamond-inst] · [#3237][pr-diamond-inst]
- `Diamond.MLIR.lower` sends that graph through γ lowering to the project's
  scoped dialect with isolated region bodies. `returns_iff_denote` and
  `denote_eq` compare the one returned value with the native source.
  `Diamond.MLIR.satisfaction` compares two lowered diamonds of the same
  input and result types in the induced model. It is equivalent to equality
  of native denotations at every typed input, even with different producer
  tables. General Sea of Nodes CFGs and standard MLIR CFG or graph regions
  remain outside this result.
  [Definitions][son-diamond-mlir-defs] · [Theorems][son-diamond-mlir-thms] · [Worked example][son-diamond-mlir] · [#3189][pr-diamond-mlir] · [#3215][pr-diamond-eq]
- `Diamond.Institution.ToRVSDG` lifts typed opcode maps, commutes with
  equation relabelling and model reduct, and preserves and reflects
  satisfaction in the induced RVSDG model. `satisfaction_map` gives the
  corresponding law after signature change. `Diamond.MLIR.Institution`
  gives `sentenceTranslation`, `model_reduct` and `satisfaction_induced`
  for the isolated scoped dialect. These laws quantify over models induced
  from native diamonds. An unrestricted scoped model can interpret γ
  differently, and the singleton-carrier counterexample excludes an
  all-target-model reduct for the stated sentence translation.
  [RVSDG theorems][son-diamond-rvsdg-inst-thms] · [MLIR theorems][son-diamond-mlir-inst-thms] · [MLIR model regression][son-diamond-mlir-inst-regression] · [#3302][pr-diamond-rvsdg-inst] · [#3266][pr-diamond-mlir-inst]
- `Diamond.PhiElim.eliminate_eq_some_iff` characterizes exactly when
  equal typed wire addresses admit a straight-line `Pure.Program` with
  the same producer table. `returns_iff` and `lower_run_eq` relate
  finite source returns and the existing γ and straight-line RVSDG runs.
  [Theorems][son-phi-elim-thms] · [#3293][pr-phi-elim]
- `Diamond.RTL.lower_returns_iff` compares the source diamond to the whole
  program's `Prog.oracle`. The generated function has four strictly forward
  blocks, takes two 64-bit words, and returns one word with unchanged
  memory. The admitted primitives are constants, wrapping add and subtract,
  and equality.
  [Theorems][son-diamond-rtl-thms] · [#3272][pr-diamond-rtl]

### Pure single loop

```lean
import Silmaril.SSA.SeaOfNodes.Loop.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Theta.Thms
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms
```

- `Loop.Graph` has an acyclic total preheader and header, one entry
  occurrence and one backedge, and one returned value. The first header
  evaluation can return with zero completed backedges. `Graph.latch_get`
  reads each selected Phi operand from the same predecessor snapshot.
  `Graph.evalBackedges_eq_some_iff` bounds completed backedges.
  `Graph.returns_iff_mem_denote` identifies finite returns with membership
  in the partial denotation.
  `Graph.not_returns_of_backedge_invariant` rules out a finite return when
  an invariant at initialization forces another backedge at every step.
  [Definitions][son-loop-defs] · [Theorems][son-loop-thms] · [#3192][pr-loop]
- `Graph.lowerTheta` generates a numbered RVSDG graph with one θ.
  `Graph.lowerTheta_returns_iff`, `Graph.lowerTheta_observe_eq_some` and
  `Graph.lowerTheta_finishes_iff` give iff statements for a finite numbered
  return, the partial observation and the existence of a finite completed
  Petri firing sequence in the generated model. Universal termination of
  firing sequences remains open.
  [Definitions][son-theta-defs] · [Theorems][son-theta-thms] · [Regression][son-theta-regression] · [#3210][pr-theta]
- `Loop.LambdaSSA.Generic.lower` emits a typed λSSA CFG for the pure
  single-loop `Graph` profile. `entry_latch` and `feedback_latch` read
  the corresponding argument column from one activation snapshot.
  `lower_eval_iff` characterizes each finite target return by the native
  return, external exit zero, its encoded payload and unchanged ambient
  state. The regression includes an empty-carried loop with no finite
  return. General CFGs and source-loop correspondence to scoped MLIR remain open.
  [Theorems][son-loop-generic-ssa-thms] · [Regression][son-loop-generic-ssa-regression] · [#3279][pr-loop-generic-ssa]

### Related public interfaces

- `RVSDG.MLIR.Graph.lower` and `denote_lower` translate state-free acyclic
  numbered RVSDG graphs with primitives and nested γ into isolated MLIR
  blocks, matching the entire ordered result tuple in the induced total
  model. `lower_map` and `model_reduct` cover signature change.
  [Theorems][rvsdg-mlir-graph-thms] · [Profile][rvsdg-mlir-graph] · [#3162][pr-gamma]
- `RVSDG.MLIR.Graph.Feedback.lower` covers numbered nested γ/θ graphs
  in the stateless institution with a `NoState` witness. It targets a
  project-defined MLIR-style block with strict bindings.
  `returns_lower_iff` and `observe_eq_some_iff` compare finite returns
  of the full tuple and the source’s partial observation.
  [Theorems][rvsdg-mlir-feedback-thms] · [Profile][rvsdg-mlir-feedback] · [#3235][pr-feedback]
- `RVSDG.MLIR.Regionless.translateGraph` and `ProfileMap.pullback` apply
  to value-port graphs with a match for every opcode of the dialect.
  `denote_translateGraph` compares each returned slot and `satisfaction`
  preserves and reflects value-equation satisfaction in the pullback.
  The graph, equation and model laws cover opcode relabelling and MLIR
  signature change. The diamond dispatch returns a control port, so its
  scoped lowering uses the γ interface above.
  [Theorems][rvsdg-mlir-regionless-thms] · [Profile][rvsdg-mlir-regionless] · [#3133][pr-regionless]
- `PhiView.ofBlockArgs` and `toBlockArgs` transpose existing typed λSSA
  branch arguments into an occurrence-indexed Phi table and back. The
  input certifies right-associated tuples of typed variables ending in
  unit. `latch_eq_transfer` proves a single selected transfer agrees with
  the simultaneous latch and leaves state unchanged. Two occurrences
  from one block can target the same label.
  [Definitions][phi-view-defs] · [Theorems][phi-view-thms] · [Worked example][phi-view] · [#3186][pr-phi-view]
- `GCM.checkPlacement` checks one proposed insertion for a pure total node
  in a typed CF graph, given operand and use positions and a sound supplied
  dominator-tree certificate. `checkPlacement_sound` gives dominance and
  local order for accepted cuts. `Use.phi_point?_eq_some_iff` resolves a
  Phi use at the source terminator for its exact branch occurrence.
  Discovery chooses the first accepted cut in the actual entry and supplied
  typed blocks. `discoverPlacement_sound` confirms its membership and checker
  acceptance. `discoverPlacement_eq_none_iff_no_legal`
  excludes legal cuts in that enumeration when the supplied tree has complete
  reachability and dominance evidence.
  [`GCM.Dominance.Tree.Synthesis.synthesize?`][son-gcm-dominance-synthesis-thms]
  builds that certificate itself, exactly, for any successor-closed finite
  block inventory, closing general dominator-tree construction for this
  profile; a whole-CFG reducibility certificate still remains open.
  [`GCM.EarlyPlacement.earlyBound?`][son-gcm-earlyplacement-thms] and
  [`GCM.LatePlacement.lateBound?`][son-gcm-lateplacement-thms] constructively
  compute the Schedule Early and Schedule Late bounds (deepest operand
  definition; common dominated bound of resolved uses) with the matching
  universal property on each side, refusing exactly when operand or use
  blocks are pairwise incomparable; `EarlyPlacement.legal_iff_bounds`
  composes both into an exact rewrite of `Legal`.
  [`GCM.LoopForest`][son-gcm-loopforest-thms] discovers every dominating-backedge
  natural loop on the typed CFG, certifies that their member sets are disjoint
  or strictly nested, and derives each block's enclosing-loop depth for the
  existing cut ranking; an irreducible cycle with no dominating backedge gets
  no depth. [`GCM.Corridor.chooseSynthesized?`][son-gcm-corridor-thms] composes
  all of the above into one constructive, loop-depth-ranked placement choice
  from a raw successor-closed CFG and operand/use list.
  [`GCM.LoopHoist.pickAndHoist?_run_eq`][son-gcm-loophoist-thms]
  proves execution preservation after hoisting one invariant producer, or one
  bounded dependency slice, into a single self-backedge loop's existing
  preheader. Pinned/faulting operations, irreducible loops, and an executed,
  behavior-preserving move for the general case remain open.
  [Definitions][son-gcm-defs] · [Checker][son-gcm-thms] · [Discovery theorems][son-gcm-discovery-thms] · [Early bound][son-gcm-earlyplacement-thms] · [Late bound][son-gcm-lateplacement-thms] · [Dominator-tree synthesis][son-gcm-dominance-synthesis-thms] · [Loop ranking][son-gcm-loopforest-thms] · [Corridor][son-gcm-corridor-thms] · [Loop hoist][son-gcm-loophoist-thms] · [Worked example][son-gcm] · [#3200][pr-placement] · [#3294][pr-gcm-discovery] · [#4918][pr-gcm-compact-exit-phi]
- `GVN.checkRepresentative` checks a supplied earlier producer in the same
  typed pure table using the exact opcode and ordered operand addresses.
  `checkRepresentative_sound` proves value equality for an accepted pair
  in every pure total model. `redirectResult_read` preserves the value
  when redirecting a single returned wire in that table. Discovery enumerates
  earlier typed producers, and one checked elimination deletes a binding
  with an all-original-wire routing guarantee. The bounded pass rescans the
  rewritten table and recomputes keys after each deletion. `run_sound` proves
  that routing preserves every original wire. Normalization uses the original
  binding count plus one as fuel, and `normalize_normal` excludes
  checker-accepted duplicates in the final table. This is an
  exact ordered-key normal form for pure acyclic tables. Algebraic identities,
  cyclic congruence and worklist invalidation remain open for this acyclic
  profile. A separate structural track, [`GVN.Cyclic`][son-gvn-cyclic-thms],
  computes a congruence partition over one Loop Region to a certified coarsest
  stable fixed point ([`FixedPoint`][son-gvn-cyclic-fixedpoint-thms]) and
  checks single-use redirects and one shrinking deletion from those classes
  ([`Pass`][son-gvn-cyclic-pass-thms]).
  [`TwoBackedges.Family.Discovery.Return.Deletion`][son-gvn-cyclic-dead-header-thms]
  and its `Cleanup` extension check and repeat dead-header-write erasure after
  automatic return redirection in one two-backedge quad loop family. This
  track does not yet compose with the acyclic pass above, cover multi-use
  redirection, or iterate across a changed loop view.
  [Checker][son-gvn-thms] · [Discovery][son-gvn-discovery-thms] · [Elimination][son-gvn-elimination-thms] · [Pass theorems][son-gvn-pass-thms] · [Cyclic][son-gvn-cyclic-thms] · [Worked example][son-gvn] · [#3225][pr-gvn] · [#3290][pr-gvn-pass] · [#4895][pr-gvn-dead-header] · [#4934][pr-gvn-dead-header-cleanup]
- `Quads.Code.eval` executes one ordered block of pure assignments over a
  fully initialized typed register bank. `Code.lower` connects uses to the
  current definition before updating the destination. `rebind_same` and
  `rebind_other` specify the updates, and `Code.lower_run` proves exact
  agreement on one returned value. `Join.Program.lower_run` covers one
  acyclic join with two closed predecessors and a single continuation.
  The emitted γ selects the predecessor's typed outgoing bank in either
  Region order. `Loop.Program.lower_step` covers one tail-tested header
  with prior typed header allocation and a full-bank backedge.
  `lower_returnsAfter_iff` matches the exact completed-backedge count,
  including an exit on the first activation. General CFG construction and
  pruned Phi placement remain open.
  [Straight-line theorems][son-quads-thms] · [Join theorems][son-quad-join-thms] · [Loop theorems][son-quad-loop-thms] · [Worked example][son-quads] · [#3233][pr-quads] · [#3261][pr-quad-join] · [#3278][pr-quad-loop]
- `Memory.Graph` orders Loads and Stores through one current memory
  version over allocated, initialized cells of 64-bit words.
  `Graph.returns_iff_denote` equates explicit-edge execution and current-heap
  denotation on the returned word and final heap. A checked same-version
  load forwarding rewrite and an ordered RVSDG lowering preserve that
  observation for the linear profile. In `Memory.Diamond`, the taken arm
  publishes a word and heap at its control occurrence, then a common suffix
  receives both. `latch_publish_iff` requires the matching Region slot,
  and `Graph.returns_iff_denote` compares the return and entire final heap.
  Allocation, split state and memory motion remain open.
  [Linear theorems][son-memory-thms] · [Forwarding][son-memory-forwarding-thms] · [Linear RVSDG lowering][son-memory-rvsdg-thms] · [Diamond theorems][son-memory-diamond-thms] · [Linear worked example][son-memory] · [#3231][pr-memory] · [#3280][pr-memory-diamond]
- A separate, more specialized track checks guarded dispatch-family
  native loops (fixed i64 banks with ordered feedback rows, distinct
  from the `Loop.Graph` pipeline above) and emits both resized RTL.SSA
  and typed MLIR CF for them. `Producer.Exit.Inversion.returns_iff`,
  `cf_returns_iff`, `returns_exists_iff`/`rtl_oracle_iff`/`no_return_iff`
  and `region_returns_iff`/`region_no_return_iff` give forward/converse
  finite-return and all-budget-absence equivalences between the two
  backends and the canonical λSSA Region, for that checked profile only.
  [Guide and decision table][guarded-feedback-rtl] · [Theorems][son-guarded-exit-inversion-thms]

## Editions and source boundaries

| Work | Edition and full text used | SHA-256 of PDF |
| --- | --- | --- |
| Clifford Noel Click, Jr., *Combining Analyses, Combining Optimizations* | Rice University PhD dissertation, February 1995 on the title page, handle `1911/16807`. The deposit is a 151-page scan. Section references below use printed numbering. Appendix A begins on printed p. 119, PDF p. 130. [Rice record][thesis] · [Rice scan][thesis-pdf] | `30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c` |
| Cliff Click, *From Quads to Graphs: An Intermediate Representation’s Journey* | Rice University Center for Research on Parallel Computation, `CRPC-TR93366-S`, October 1993. The 29-page report includes the manuscript dated October 18, 1993. The live Rice link returned 404. [Archived Rice PDF, 2025-03-30][quads] | `8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b` |
| Cliff Click and Michael Paleczny, *A Simple Graph-Based Intermediate Representation* | ACM SIGPLAN Workshop on Intermediate Representations (IR ’95), pp. 35–49, also *SIGPLAN Notices* 30(3). Both ACM records identify the same paper. [Proceedings][ir] · [Notices][ir-notices] · [Oracle PDF][ir-pdf] | `9c12e5cd0ee54beb51436b25aec73c45855bb0eb5bafaa76ee4135edeadca17c` |
| Cliff Click, *Global Code Motion/Global Value Numbering* | PLDI ’95, pp. 246–257, also *SIGPLAN Notices* 30(6). The slash is ACM’s catalog punctuation. The linked UW course now serves an identity-provider page. [Proceedings][gcm] · [Notices][gcm-notices] · [Archived UW PDF, 2014-09-08][gcm-pdf] | `9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23` |
| Cliff Click and Keith D. Cooper, *Combining Analyses, Combining Optimizations* | ACM’s catalog title for the article in *TOPLAS* 17(2), March 1995, pp. 181–196. This is the coauthored article linked from Simple chapter 1. Use it alongside thesis chapter 3. [ACM][combining] · [Archived ACM PDF, 2025-09-16][combining-pdf] | `579ee1cc4e73d97b7741e0a8f4eceed0af8a6aee65d162b7114ad652abdc1a32` |
| Michael Paleczny, Christopher Vick and Cliff Click, *The Java HotSpot™ Server Compiler* | USENIX JVM ’01, April 2001. Its compiler overview cites the workshop paper and its GCM section cites Click’s scheduler. It supplies a historical industrial comparison. [USENIX proceedings PDF][hotspot] | `ad5091a200cf32752e2dc4150b506934ff7d460b4fe49076acd128e39219586e` |
| Matthias Braun et al., *Simple and Efficient Construction of Static Single Assignment Form* | CC 2013, LNCS 7791, pp. 102–122. Its SSA construction and related-work sections connect direct construction to Click–Paleczny and HotSpot. [Springer][braun] · [Authors’ PDF][braun-pdf] | `01f0b6d558096c27c1f37f4b451b8c4932dc200cee4e86d07357f0dacf21aa6a` |

The [organization reading list][org] points to the Rice dissertation and
calls out Appendix A. [Simple chapter 1][s01] adds the TOPLAS article and
two decks by Click. *How To SSA C2-Style* (`EasySSA.pdf`) illustrates
construction and explicitly drops minimality as a goal. *Sea of Nodes*
(`SeaOfNodes.pdf`) illustrates graph semantics, optimization and scheduling.
Use these as worked examples under the corresponding papers and Simple
chapters. The [REBASE 2026 deck and notes][rebase] give a newer walkthrough,
including the memory and SCCP examples. The SHA-256 values are
`e666c44f546c9ef563d0fba6c9d5b0fbbac73a394a793f01cfc34ed2f7a18be6`
for *How To SSA* and
`ab41d9a977843a13ca6e7cc71ae4b1516b4a8a160427425769ec3f28b66c175b`
for *Sea of Nodes*. [How To SSA PDF][easy] · [Sea of Nodes PDF][slides]

The report’s bibliography and the later papers identify two predecessor
algorithms relevant to the proof sequence. Cytron et al.’s *Efficiently
Computing Static Single Assignment Form and the Control Dependence Graph*
(TOPLAS 13(4), 1991) gives the dominance-frontier baseline. Wegman and
Zadeck’s *Constant Propagation with Conditional Branches* (TOPLAS 13(2), 1991)
gives the executable-edge and sparse-propagation baseline. Alpern, Wegman
and Zadeck’s *Detecting Equality of Variables in Programs* (POPL 1988) gives
the congruence-partition baseline for the thesis’s stronger algorithm.
Treat these as algorithm references for the relevant slice. Full-text
section coverage for these predecessor papers is outside this inventory.
[Cytron et al.][cytron] · [Wegman–Zadeck][wegman] · [Alpern et al.][alpern]

Use Braun et al. §§2.2–2.3 for demand-driven SSA and incomplete blocks.
Its §§3–4 separate redundant-Phi elimination and the assumptions for
minimality. Prove construction preserves behavior first. An extension
claiming pruned or minimal SSA needs the corresponding properties for
its own CFG class. [CC 2013 paper][braun-pdf]

Webb, Hayes and Utting’s *A Formal Semantics of the GraalVM Intermediate
Representation* (2021) and *Verifying Term Graph Optimizations using
Isabelle/HOL* (2023) give comparison points for executable graph semantics
and verified graph rewrites. Their venue records establish the scope of the
comparison. Matching Graal’s node semantics or transferring its Isabelle
proofs would require a separate correspondence. [Graal semantics][graal] ·
[Term graph optimizations][termgraphs]

## Original design and algorithms

The technical rows name the proof target independently of the implementation
in any one edition. Repeated concepts share one target. Preserve meaningful
differences, including where scheduling is allowed to speculate and which
analyses account for loop feedback.

### From Quads to Graphs

| Report sections | Lean obligation | Coverage on main |
| --- | --- | --- |
| §§1–2, introduction, quads and use-def information | Give ordered three-address execution a reference meaning. Show use-def lookup agrees with reaching values where defined. State the conservative assumptions of one-pass optimization at unresolved edges. | Partial. [`Quads.Code.eval` and `Code.lower`][son-quads-defs] cover ordered execution and reaching-value wiring in one initialized typed block. [`Code.lower_run`][son-quads-thms] proves returned-value agreement. Unresolved edges and optimization stay open. |
| §3, static single assignment | Track the current definition of each variable and construct predecessor-indexed join inputs. Show that SSA construction preserves the quad execution, including a loop where a provisional backedge definition is later resolved. | Partial. [`Quads.rebind_same` and `rebind_other`][son-quads-thms] specify current definitions in one block. [`PhiView.ofBlockArgs`][phi-view-defs] transposes already-admitted branch arguments. [`Join.Program.arm_results`][son-quad-join-thms] constructs typed incoming columns for two closed predecessors. [`Loop.Program.lower_step`][son-quad-loop-thms] closes the backedge for one tail-tested loop. General SSA construction stays open. |
| §4, control-flow dependence | Make a definition’s execution condition explicit. Show that removing a redundant φ or contracting a control path preserves predecessor identity and the selected values. | Partial. [`Diamond.Merge.slot` and `Graph.Returns`][son-diamond-defs] connect a taken projection to the right Phi operand. [`PhiElim.returns_iff`][son-phi-elim-thms] covers exact same-wire Phi elimination. General control contraction stays open. |
| §5, engineering concerns | State the invariants of replacement, inverse-use maintenance and deletion. Treat allocation strategy and object dispatch as implementation choices unless an implementation refinement exposes them. | Partial. [`GVN.redirectResult`][son-gvn-defs] redirects one selected result in the same table. [`GVN.Elimination.eliminate_sound`][son-gvn-elimination-thms] covers one checked pure producer deletion with typed routing. General graph edits and inverse-use maintenance stay open. |
| §6, two tiers to one | Encode the CFG as control nodes, Regions and Ifs. Prove agreement with block execution, including the shared incoming-edge choice for all Phis at a Region. Track which data nodes are pinned. | Partial. [`Diamond.Graph`][son-diamond-defs] fixes one If, Region and returned Phi. [`Loop.Graph`][son-loop-defs] latches a tuple at one loop Region. [`Diamond.LambdaSSA.returns_iff`][son-diamond-ssa-thms] covers the generated diamond CFG. [`Loop.LambdaSSA.Generic.lower_eval_iff`][son-loop-generic-ssa-thms] covers the generated single-loop CFG. General extraction and block-execution agreement stay open. |
| §7, types and pessimistic optimizations | Relate abstract type facts to concrete values, justify folding and identities on the admitted primitive semantics, and type multi-result producers and projections. | Partial. [`Diamond.Dataflow`][son-diamond-defs] types single-result producers. [`SeaOfNodes.MLIR.Op`][son-scalar-defs] interprets modular constants, add and multiply. Abstract facts, folds and source multi-result producers stay open. |
| §8, more engineering concerns | Give Start, execution alternatives, projections, memory and I/O states, and calls typed interfaces. Prove ordering and the selected results for each supported stateful primitive. | Partial. [`Memory.Graph` and `MemoryInput`][son-memory-defs] type one ordered Load/Store chain from Start to Return. I/O, calls and the general projection interface stay open. |
| §9, removing control information | Justify removing a computation’s control input under an explicit safety/speculation condition and reconstruct a legal execution order. Require guards for operations whose definedness depends on control. | Partial. [`GCM.checkPlacement`][son-gcm-defs] checks a supplied placement for pure total code. Removing control inputs, reconstructing a schedule and guarded speculation stay open. |
| §10, optimistic transformations | Define transfer functions for control and values, including loops. Prove sparse worklist convergence, agreement with the declared fixed point and sound use of the resulting facts. | Open. |
| §11, summary | Use the worked graphs as regression cases for the earlier obligations. | Open for the report’s worked graphs. The [scoped fixtures](#start-here) exercise their corresponding profiles. |

### A Simple Graph-Based Intermediate Representation

| Workshop sections | Lean obligation | Coverage on main |
| --- | --- | --- |
| §1, introduction | Specify the shared SSA graph invariant and relate the initial graph to a typed CFG. | Partial. [`Diamond.Dataflow` and `Graph`][son-diamond-defs] give the typed dependency and branch invariant for one diamond. [`Diamond.LambdaSSA.lower_hasType`][son-diamond-ssa-thms] types the generated CFG. General CFG correspondence stays open. |
| §§2.1–2.4, nodes, Regions, Phis, Ifs and projections | Type ordered ports and distinguish data and control. Give each incoming control occurrence its own index, including two transfers from the same block. Pair each Phi’s ordered inputs with those occurrences. Type projected results. | Partial. [`Diamond.Projection`, `Merge` and `Phi`][son-diamond-defs] tie the control occurrence to one typed Phi operand. [`PhiView.EdgeOcc` and `Table`][phi-view-defs] distinguish same-target λSSA branch occurrences. General producer and control shapes stay open. |
| §2.5, memory and I/O | Model memory and I/O as explicit state values. Show that independent components can be separated only with a sound independence relation and that their recombination preserves observations. | Partial. [`Memory.Graph.returns_iff_denote`][son-memory-thms] relates one explicit whole-memory chain to a threaded heap. [`Memory.Diamond.Graph.returns_iff_denote`][son-memory-diamond-thms] covers one occurrence-indexed whole-heap join. I/O, independence and split/recombined memory stay open. |
| §3, model of execution | Define control-token steps, branch selection and simultaneous Phi latching at joins and loop re-entry. Distinguish live graph cycles through merge/feedback from unsupported cycles among strict data dependencies. Relate node-level execution to ordered SSA execution. | Partial. [`Diamond.Graph.Returns`][son-diamond-defs] selects the predecessor operand. [`Loop.Graph.latch` and `step`][son-loop-defs] cover simultaneous feedback reads. [`Diamond.LambdaSSA.returns_iff`][son-diamond-ssa-thms] gives finite agreement for the scheduled diamond. [`Loop.LambdaSSA.Generic.follow_iff`][son-loop-generic-ssa-thms] relates finite loop continuation to counted source returns. General token steps and SSA agreement stay open. |
| §§4.1–4.5, implementation | Relate node identity to structural keys, retain ordered operand slots and prove use-def/def-use coherence through insert, replace and delete. Treat object layout and allocation speed as implementation details. | Partial. [`GVN.Producer.key`][son-gvn-defs] records the opcode, typed profile and ordered operand addresses. [`GVN.Elimination.eliminate_sound`][son-gvn-elimination-thms] covers checked removal of one exact duplicate. Insertion, general replacement and inverse-use coherence stay open. |
| §5.1, optimizing through a peephole | Justify abstract value computation, identities and hash-consing, with a precondition for each fold. Prove replacement preserves graph well-formedness and behavior. | Partial. [`GVN.checkRepresentative_sound` and `redirectResult_read`][son-gvn-thms] justify one checked result redirection. [`GVN.Pass.run_sound`][son-gvn-pass-thms] covers repeated checked replacement and deletion in one pure table. Abstract values, folds, algebraic identities and hash-consing stay open. |
| §§5.2–5.3 and §§6–7 | Treat benchmark results as historical evidence and the related-work comparison as context for the graph invariant. | Historical context. |

### Rice dissertation

| Dissertation chapters | Lean obligation | Coverage on main |
| --- | --- | --- |
| Ch. 1, introduction | Fix the source/target semantics, permitted optimization observations, and intermediate graph invariant. | Partial. [The three admitted profiles](#start-here) give typed graph boundaries and returned-value observations. [`Diamond.Institution.inst`][son-diamond-inst-thms] gives the native diamond equation contract. The general optimization contract stays open. |
| Ch. 2, optimistic assumption | Justify what the initial optimistic element says about unknown values and paths. Prove that iterating cyclic equations yields facts safe to use at the chosen fixed point. | Open. |
| §§3.2–3.5, framework, constant propagation and solving | Instantiate a monotone finite-height framework with primitive transfer functions and a concretization. Establish termination and greatest fixed point in the thesis’s order, or give the order-dual statement explicitly. | Open. |
| §§3.6–3.9, unreachable code, combined analyses and GVN | Prove value facts and executable-edge facts mutually sound, with Phi transfer over executable edges. State when the combined result improves separate analyses. Use the TOPLAS article’s §§2–4 for the framework and iteration, §§5–6 for the reachability/constant product and profitability, and §7 for adding value numbering. | Open. |
| §§4.1–4.5, efficient combined algorithm | Specify Hopcroft-style partition refinement, splitting and the effects of executable inputs and constants. Prove the optimized solver computes its specified partition and analysis facts. Keep the complexity bound as a separate theorem with a cost model. | Partial for the congruence-partition slice, open for the combination with executable inputs and constants. [`GVN.Cyclic.refine_eq_iff` and `checkStable_eq_true_iff`][son-gvn-cyclic-thms] give one synchronous partition-refinement round and a checked stability test over a finite typed producer view of one Loop Region. [`GVN.Cyclic.FixedPoint.normalize_stable` and `normalize_coarsest`][son-gvn-cyclic-fixedpoint-thms] iterate that round to a certified coarsest stable structural partition, with a strict-growth fuel bound in place of Hopcroft-style splitting. Combining this with executable-edge and constant facts, the complexity bound, and the execution (semantic) correspondence of the computed classes stay open. |
| §§4.6–4.11, identities and using the partition | Handle subtraction/comparison, leader/follower identities, and equal-input Phi/Max cases under explicit hypotheses. Prove the resulting equivalences before replacing uses and scheduling. Record any congruences the solver intentionally misses. | Partial. [`Diamond.PhiElim.eliminate_eq_some_iff`][son-phi-elim-thms] covers the equal-address Phi case in a pure diamond. [`GVN.Cyclic.Pass`][son-gvn-cyclic-pass-thms] enumerates single-use redirects from the partition above and checks one shrinking deletion on a supplied loop view, explicitly leaving view extraction, multi-use redirection and iteration across changed views out of scope. [`TwoBackedges.Family.Discovery.Return.Deletion`][son-gvn-cyclic-dead-header-thms] and its `Cleanup` extension check and repeat dead-header-write erasure after automatic return redirection in one two-backedge quad loop family. Algebraic identities beyond equal addresses, and partition-derived rewrites outside this one-view, single-use shape, stay open. |
| Ch. 5, experimental data | Preserve the link to the reported ILOC experiments and leave benchmark reproduction outside semantic correctness. | Historical context. |
| §§6.1–6.4, optimizing without the global schedule | Separate control removal and graph rewrites from CFG extraction, legal placement and schedule heuristics. Use the PLDI rows below for the shared scheduler proof. | Partial. [`GCM.checkPlacement`][son-gcm-defs] checks a candidate position. The PLDI rows below track the remaining scheduling and rewrite obligations. |
| §§7.1–7.3, parser design and peephole optimizer | Specify current bindings, incremental use-def edges, incomplete labels/loops, Phi insertion and the contract for each rewrite while parsing. Later pruning of redundant Phis needs its own theorem. | Open. |
| §§7.4–7.5 and Ch. 8 | Carry forward worked cases and limitations. The historical speedups and future directions serve as context. | Historical context and open source regressions. |
| App. A §§A.1–A.3, IR design and engineering | Reuse the report/workshop graph and rewrite invariants. Include abstract types and argument ordering in the interface. | Partial. [`Diamond.Dataflow`][son-diamond-defs] and [`Pure.Program`][son-pure-defs] give typed ordered wires. Abstract typing and graph edit invariants stay open. |
| App. A §§A.4–A.5, one-tier execution and engineering | Reuse control flow, Phi latching, If, Start and projections. Treat state and subroutine effects as explicit boundaries. | Partial. [`Diamond.Graph`][son-diamond-defs] and [`Loop.Graph.latch`][son-loop-defs] cover pure projection selection and latching. [`Memory.Graph`][son-memory-defs] covers one whole-memory chain. General state and subroutine effects stay open. |
| App. A §§A.6–A.7 | Retain the comparison with related representations. Require a translation theorem for any claimed equivalence. | The [scoped translations](#start-here) cover their stated profiles. Broader representation equivalence stays open. |

### Global Code Motion/Global Value Numbering

| PLDI sections | Lean obligation | Coverage on main |
| --- | --- | --- |
| §§1–1.2, motivation and representation | Define the floating/pinned distinction and admissible graph domain. Identify which conclusions hold for reducible CFGs and what requires different loop information. | Partial. [`GCM.Legal`][son-gcm-defs] describes one proposed placement of a pure total node over typed CF. Pinned nodes and the general graph domain stay open. |
| §2 and §2.1, GCM, dominators and loops | Recover reachable control and certify the dominator tree and loop information on the supported shape. Specify the handling of unreachable code and a reachable loop with no exit. | Partial. [`GCM.DominatorTree`][son-gcm-defs] supplies sound ancestry and reachability facts on structural paths. [`GCM.Dominance.Tree.Synthesis.synthesize?`][son-gcm-dominance-synthesis-thms] constructs a certified `DominatorTree` for any successor-closed finite block inventory; [`proposedAddress_prefix_iff`][son-gcm-dominance-synthesis-thms] proves its addresses are exact, not just sound, for every reachable pair, and [`synthesize?_isSome_iff`][son-gcm-dominance-synthesis-thms] characterizes success exactly by that closure. [`GCM.LoopForest`][son-gcm-loopforest-thms] discovers every dominating-backedge natural loop on the typed CFG, certifies disjoint-or-nested member sets, and derives each block's enclosing-loop depth. Dominator-tree construction beyond a successor-closed finite inventory, irreducible cycles with no dominating backedge, and exitless scheduling stay open. |
| §2.2, schedule early | Each floating node’s placement must be dominated by its operand definitions and permitted by its safety/control constraints. Pinned nodes retain their required placement. The paper’s footnote 6 allows faulting operations to move later under partial correctness. A profile that observes faults needs a stronger condition. | Partial. [`GCM.checkPlacement_sound`][son-gcm-thms] checks the operand constraint at a given cut. [`discoverPlacement_sound`][son-gcm-discovery-thms] finds an accepted cut in a finite inventory. [`GCM.EarlyPlacement.earlyBound?`][son-gcm-earlyplacement-thms] constructively computes the deepest operand-definition block (the entry for no operands); [`earlyBound?_spec`][son-gcm-earlyplacement-thms] proves it is dominated by, and dominates every reachable block dominated by, all operand definitions, and [`earlyBound?_isSome_iff`][son-gcm-earlyplacement-thms] characterizes refusal exactly (an invalid cut, or pairwise-incomparable operand blocks with no common reachable dominated block). Pinned and faulting operations stay open. |
| §2.3, schedule late | Compute the common dominator of uses, interpreting a Phi use on its corresponding incoming edge. Prove the feasible placement interval and that moving a computation does not introduce a trap or unwanted effect. | Partial. [`GCM.Use.phi_point?_eq_some_iff`][son-gcm-thms] resolves a Phi operand at the source terminator. [`checkPlacement_sound`][son-gcm-thms] checks availability for supplied uses. [`discoverPlacement_eq_none_iff_no_legal`][son-gcm-discovery-thms] excludes legal cuts in the supplied inventory with complete evidence. [`GCM.LatePlacement.lateBound?`][son-gcm-lateplacement-thms] constructively computes the common dominated bound of resolved use blocks over a finite inventory, with a Φ use counted on its incoming edge; [`lateBound?_spec`][son-gcm-lateplacement-thms] proves the matching universal property. [`EarlyPlacement.legal_iff_bounds`][son-gcm-earlyplacement-thms] composes both bounds into an exact rewrite of `Legal` for a successor-closed inventory. General motion soundness — that an actual move preserves program behavior, beyond placement legality — stays open. |
| §2.4, selecting a block | Prove legality for any chosen block in the interval, including intra-block order. Then verify the shallow-loop/deep-dominator choice independently of performance claims. | Partial. [`GCM.checkPlacement_sound`][son-gcm-thms] certifies an accepted cut, including local order. [`GCM.LoopPlacement.chooseLoopPlacement_sound`, `_minimal` and `_complete`][son-gcm-loopplacement-thms] select, among checker-accepted cuts in a supplied finite inventory, one of minimum caller-supplied loop depth with the deepest dominator address as tie-break. [`GCM.Corridor.acceptedCorridorCuts_eq`][son-gcm-corridor-thms] proves that restricting this search to the computed early/late corridor changes nothing; [`GCM.Corridor.choosePlacement`][son-gcm-corridor-thms] discovers that loop depth itself from [`LoopForest`][son-gcm-loopforest-thms] instead of taking it as a caller-supplied function, and [`chooseSynthesized?`][son-gcm-corridor-thms] composes the whole search with dominator-tree synthesis from a raw successor-closed CFG. [`GCM.LoopForest`][son-gcm-loopforest-thms]'s ranker gives the same minimum-depth, deepest-dominator selection directly over the discovered forest. [`GCM.LoopHoist.pickAndHoist?_run_eq`][son-gcm-loophoist-thms] additionally moves one invariant producer, or one bounded dependency slice, into a single self-backedge loop's existing preheader, with execution agreement at every fuel budget. Irreducible loops, pinned/faulting operations, and an executed, behavior-preserving move for the general case stay open. |
| §§3–3.2, value numbering | Prove representative substitution for equal keys and the stated algebraic identities, including worklist invalidation. Graph replacement can leave nodes without a legal old placement. Compose the replacement proof with schedule reconstruction. Treat stronger cyclic congruence discovery as the separate thesis chapter 4 obligation. | Partial. [`GVN.Key.matches`][son-gvn-defs] compares exact keys and [`GVN.redirectResult_read`][son-gvn-thms] preserves one selected result. [`GVN.Pass.run_sound` and `normalize_normal`][son-gvn-pass-thms] cover repeated deletion and exact-key normal form on acyclic pure tables. Algebraic identities, worklist invalidation and schedule reconstruction stay open. |
| §§4–5, experiments and conclusions | Use the examples as regressions and keep the ILOC comparisons empirical. | Open for the paper’s example regressions. Performance comparisons remain empirical. |

The HotSpot paper illustrates a richer instantiation. §§3–4 describe
ordered inputs, incremental graph construction and `Ideal`, `Value`,
`Identity` and GVN. §8 adds iterative passes and conditional constant
propagation. §§9–11 cover machine-node selection, scheduling and local
ordering. In particular, §10 accounts for load/store anti-dependence.
§§2, 5–7 and 16–18 supply JVM-specific runtime, deoptimization, exception
and numeric requirements for a future HotSpot profile. Click’s reply
identifies anti-dependence as a gap in the thesis scheduler. Use the
pinned Simple chapter 13 for the tutorial algorithm and its exact chapter
number. [HotSpot paper][hotspot] · [Click’s reply][reply] · [Simple 13][s13]

## Official Simple implementation

The primary executable reference is the Java tutorial at
`f0a6c6757a795b8e186de0076836a87acef59fa7`. The chapter README, node and
optimizer implementations, and tests at that commit define each fixture’s
profile. Use the chapter sources when the top-level synopsis lags the
chapter. For example, chapter 15 documents runtime array safety checks.
The Japanese READMEs, linear-history branch, graph viewer and printers
provide alternate presentations of the same work. The roadmap records
future features. The chapter 8 evaluator and chapter 13 scheduler are
concrete entry points for differential fixtures. [Java snapshot][simple] ·
[Chapter 15][s15] · [Roadmap][roadmap] · [Evaluator][evaluator] · [Scheduler][scheduler]

| Java chapters | Lean obligation or scope boundary | Coverage on main |
| --- | --- | --- |
| [1][s01]–[4][s04] | Start and Return, integer input and arithmetic, local binding updates, comparisons and folding. Use constants, an expression with sharing and a nonconstant argument as first fixtures. Specify the chapter’s arithmetic conventions before admitting division or any other non-total operation. | Partial. [`Pure.Program`][son-pure-defs] and [scalar `lower`][son-scalar-defs] cover shared typed producers and one return, with a modular constant/add/multiply instantiation. [`Quads.Code.lower`][son-quads-defs] covers typed assignment updates. [`Diamond.RTL.lower_returns_iff`][son-diamond-rtl-thms] covers 64-bit equality in its word diamond profile. Construction from Simple syntax and folding stay open. |
| [5][s05]–[6][s06] | Lower branch projections and current bindings to Region/Phi joins. Check dead input pruning changes the Region and every attached Phi in step. A diamond with different results on the two paths distinguishes the indices. | Partial. [`Diamond.Merge`, `Phi` and `Graph.lower`][son-diamond-defs] cover the two-path join and one Phi. [`Quads.Join.Program.lower_run`][son-quad-join-thms] covers current-binding construction for two closed predecessors. Dead-input pruning stays open. |
| [7][s07]–[8][s08] | Specify eager loop Phis, lazy creation, and the edge contributions of break and continue. Prove that graph evaluation uses the previous iteration’s values for a simultaneous Phi update. Include zero iterations, feedback, and a reachable loop with no finite return. | Partial. [`Loop.Graph.latch` and `evalBackedges`][son-loop-defs] cover one entry/backedge pair, a return after the first header evaluation with zero completed backedges, and old-value feedback. [`Graph.not_returns_of_backedge_invariant`][son-loop-thms] covers the stated no-return case. [`Quads.Loop.Program.lower_returnsAfter_iff`][son-quad-loop-thms] covers one provisional full-bank header. Lazy Phi construction, break and continue stay open. |
| [9][s09] | Prove equality for graph-aware node keys and local rules. For iterative peepholes prove that invalidation covers all necessary users, including registered distant dependencies. State convergence for the supported rules and worklist policy. | Partial. [`GVN.Producer.key`][son-gvn-defs] and [`GVN.checkRepresentative_sound`][son-gvn-thms] cover exact typed keys for ranked pure producers. [`GVN.Pass.normalize_normal`][son-gvn-pass-thms] covers bounded rescanning to an exact-key normal form. Local algebraic rules and distant-dependency invalidation stay open. |
| [10][s10]–[12][s12] | Begin with a whole-memory state and struct allocation, field initialization, loads, stores and null refinement. Add alias classes and lazy split/merge using `MemMerge`, `MemPhi` and `BulkMemPhi`. Prove projection and reassembly against whole memory, including joins and loop feedback. Extend the shape invariant for references and forward/recursive struct declarations. | Partial. [`Memory.Graph`][son-memory-defs] models total loads and stores on initialized fixed cells with final-heap observation. [`Memory.Diamond.latch_publish_iff`][son-memory-diamond-thms] covers occurrence-indexed selection of a whole heap. Allocation, initialization, null refinement, aliases, memory split/merge and loop feedback stay open at this cutoff. |
| [13][s13] | Instantiate the pure scheduling proof, then prove the memory-aware extension. The `Never` edge makes an exitless loop visible to a backward scheduler walk. Prove that the edge cannot take a return and that alias-filtered anti-dependences preserve load observations across and within blocks. Test an overwrite of the same field and a store to an independent field. | Partial. [`GCM.checkPlacement`][son-gcm-defs] covers one certified pure placement at a supplied cut. [`GCM.discoverPlacement_sound`][son-gcm-discovery-thms] searches a supplied block inventory. The scheduler, synthetic `Never` edge and memory anti-dependences stay open. |
| [14][s14]–[17b][s17b] | Specify truncation, range transfers and floating-point rounding, then array allocation, addressing and bounds-check behavior. Track constructor initialization and read-only reference permissions, including deep views. Lower syntax sugar by desugaring with the same observation. [17a][s17a] gives the permission boundary. | Open. |
| [18][s18] | Type function entry/exit, call/result projections, memory threading and known targets. Prove call/return simulation first. Give recursion and inlining separate simulation statements covering continuation and state. | Open. |
| [19][s19]–[22][s22] | Track machine-node selection (including memory), allocation/spills, encoding, target ABI and FFI as downstream correctness boundaries. Pin an ISA and ABI per later backend slice. The ISA emitters, ELF layout and native Hello World are outside the initial IR proof sequence. | Partial. [`Diamond.RTL.lower_returns_iff`][son-diamond-rtl-thms] gives a machine RTL.SSA return theorem for one pure word diamond. Allocation, encoding, ABI and FFI stay open. |
| [23][s23] | Prove the admitted cyclic type comparison/rewriting invariant, method lookup and final-field facts. Keep register allocator tuning with the backend. | Open. |
| [24a][s24a]–[24b][s24b] | Instantiate the sparse control/value solver intraprocedurally. Extend reachability across discovered call targets, recursion and unknown callers with conservative summaries. Keep the analysis theorem separate from rewriting on the result. | Open. |
| [25][s25] | Specify provisional SSA before types are complete. Prove that resolution and graph updates preserve binding, conversion and branch-fact obligations, and give a precise rejection condition for an unresolved graph. | Open. |
| [26][s26]–[27][s27] | Prove that private constructor state becomes observable only at publication. Track escape/exposure through memory, callbacks, known and unknown callers, and the Start/Stop boundary. | Open. |
| [28a][s28a]–[28b][s28b] | Specify lazy initialization order and the rejection rule for cycles that would observe unfinished state. Give separate compilation a linking and shared-state contract, including effects of unknown code. | Open. |
| [29][s29]–[31][s31] | Carry forward partial-object completion and privacy rules, stream I/O ordering, numeric defaults and intrinsic semantics where they change the observed IR. Diagnostics, text formatting, register-allocation tuning and graphics/audio demos stay outside the graph proof sequence unless used as boundary fixtures. | Open. |

### Ports and other implementations

| Official repository and pin | Evidence and use |
| --- | --- |
| [Simple-Go][go], `37cc338992bcaf4a8a83fd5fbef52a67dc088884` | Chapters 1–4 on disk. The README explicitly describes a non-exact port and adds graph/peephole directives. Compare early arithmetic and bindings on the common subset. Exclude the directives from source-language semantics. |
| [Simple-Rust][rust], `d75781d1c516805d3042e66ddbd48a9b34fc6878` | The README claims chapter-17 parity at [Java `fd5178dbf4174933798ecbfbfe06fe35de0337c4`][rust-baseline]. The tree has a graph evaluator, a scheduler and chapter tests. Use matching pre-split chapter cases for differential fixtures. |
| [Simple-Cpp][cpp], `49877551b4ee91c53d799523f15810470a16abbb` | README claims chapter-13 parity. The tree has directories through Chapter18, with evaluator and scheduling files in later directories. Parity beyond the README claim is unverified. Use chapter-13 scheduler and evaluator cases after checking the common profile. |

Compare port behavior by normalizing node IDs and comparing ordered
inputs and observations on matching fixtures. Record differences in
parsing, arithmetic, scheduling and memory as port-specific deltas.
A port result supplies regression evidence. Treat semantic parity as a
separate claim that needs a translation or an agreed common reference.
The organization’s `.github` repository is profile material. Current
HotSpot C2, Graal and V8 are separate implementation targets with distinct
opcodes, effects and runtime contracts. Their equivalence to Simple remains
outside this plan. [Official organization][org]

## Existing Lean results

| Evidence in Silmaril | Reuse and remaining gap |
| --- | --- |
| [λRTL CFG theorems][cfg-thms] and [forward CFG validation][cfg-validation] | `run_flatten` and `run_eq_toRegion` connect the forward block model with region execution. The validator covers coherent renamings and a guarded entry contraction. Reuse the proof pattern for control extraction. Sea of Nodes adds unordered floating nodes, predecessor-indexed Phis and cyclic control. |
| [SSA and λRTL with loops][ssa], [loop theorems][loop-thms] and [machine C-backend construction][machine-construct] | `Region.evalObs_eq_evalSSA_of_isSSA` gives lexical/store agreement in the loop model with its hypotheses. The machine construction gives maximal SSA by passing every register to each block, with a simulation in its own RTL setting. Demand-driven Phi placement remains open here. Its graph/RTL types belong to the Machine region. |
| [Forward λRTL CFG versioning][cfg-versioned] · [#3250][pr-versioned] | `versioned_isSSA` and `versioned_runSSA` give dominance-scoped SSA and preserve exit and payload for a generated flat versioned graph, under the forward CFG and lawful model assumptions. This result concerns λRTL CFGs. The [source-native quad slice][son-quads] covers one initialized typed block, with a separate [two-predecessor join][son-quad-join-thms]. General multi-block Sea of Nodes construction stays open. |
| [λSSA forwarding cycles][cycle-cuts] | `exists_bounded_cut` and `iterate_fold` cover finite all-recurrent forwarding tables. Use them as a model-specific comparison for exitless control. The [single-loop profile](#pure-single-loop) gives a separate source feedback theorem. The synthetic scheduling edge stays open. |
| [RVSDG graph and term theorems][rvsdg-thms], [acyclic λSSA lowering][rvsdg-acyclic] and [acyclic-body θ wrapper][rvsdg-theta] | `Graph.toGraph_toTerm` and `Term.toTerm_toGraph` cover numbered RVSDG graphs. The lowering and `denoteRegion_join` cover the generated typed single-entry/single-join acyclic grammar. The θ wrapper checks a specific single-loop shape. The source-native γ and θ lowerings above carry scoped interfaces and loop state for their fixed shapes. The [scheduled diamond](#pure-branch-diamond) also has a typed λSSA lowering. A general Region/Phi translation and control graph recovery stay open. |
| [RVSDG explicit state splice][rvsdg-splice] and [interprocedural RVSDG][rvsdg-calls] | The splice preserves finite exit, payload and exact final token in its partial model, with a witness for the component boundary. The interprocedural development provides typed function and state interfaces. Start with one SoN state token and an explicit interface mapping. Alias partitions, scheduling anti-dependence, and translation of arbitrary call graphs require new obligations. |
| [MLIR Arith theorems][mlir-thms], [scalar profile][mlir] and [MLIR language reference][mlir-ref] | `Block.toLambdaSSA_hasType` and `Block.toLambdaSSA_eval_iff` cover the pure single-block scalar profile. The source-native scalar lowering above targets the same Arith block boundary for flag-free bitvector constants, add and multiply. Multi-block SSACFG regions, typed block arguments, scoped regions with effects and MLIR graph regions require their own admission and preservation theorems. |
| [Guarded e-graph rebuild][egraph], [dataflow iteration][dataflow] and [checked pass contracts][compiler] | The e-graph has acyclic term witnesses and guarded merges. The iteration layer proves convergence of round-robin iteration to the least fixed point under its hypotheses. Checked passes show how to package admission and semantic preservation. A sparse worklist and SoN’s keys, facts and rewrites on control-aware cyclic graphs require separate proofs. |

## Proof sequence

The sequence gives the full milestones. The coverage columns above record
which parts have landed at a restricted profile.

Each slice should publish its admitted input profile, source anchors,
observable relation, definitions and theorem headers, and a small fixture
that exercises the distinguishing invariant. Record the exact upstream
chapter path and revision for executable fixtures. A fixture covers a
specific example. Mark an obligation covered once a public theorem proves
it at the stated profile. Record the first rejected extension alongside it.

1. **Graph invariant and pure execution.** Start with one function,
   Start/Return, ordered typed ports, total modular integer primitives, If
   projections, Region and simultaneous Phi. Begin with a diamond and
   acyclic strict data dependencies. State validity of IDs and ports,
   arity/type checks, inverse-use coherence if cached, and correspondence
   between incoming control slots and Phi operands. Define execution on
   admitted inputs and prove its determinism and invariance under coherent
   node renaming. Exercise both branches and reject a stale or misaligned
   Phi input. This covers the common structural target of Quads §§4–6,
   IR ’95 §§2–3, thesis App. A.2–A.4 and Simple 1–6.

2. **SSA construction and readback.** For a typed pure acyclic SSA fragment,
   prove a graph construction preserves finite exit and payload in both
   directions. Give checked readback for an explicitly scheduled graph and
   relate the two translations on the admitted image up to coherent
   renaming and discarded dead pure nodes. Include two occurrences from the
   same predecessor with different arguments. Then add one reducible
   single-entry loop, with a theorem for previous-activation Phi values and
   a separate statement relating absence of finite returns. Add eager and
   lazy construction only after the closed graph semantics is fixed.
   [Rice dissertation][thesis] · [Simple 7][s07] · [Simple 8][s08]

3. **Pure rewrites and scheduling.** Prove one peephole and equal-key
   substitution before iterative GVN. Compare a successful rewrite with a
   case where identical operands are insufficient because the primitive
   profile or control guard differs. In a scheduling PR, check CFG
   extraction, pinned placement, early/late bounds and Phi use sites.
   Prove schedule soundness against the graph semantics, then implement
   the loop-depth choice. Test a floating definition used on a Phi edge
   and a pinned operation that would be unsafe to hoist. An exitless
   loop must keep its observable behavior even if the scheduler uses
   synthetic control internally. [PLDI paper][gcm] · [Simple 9][s09] ·
   [Simple 13][s13]

4. **Restricted RVSDG and MLIR bridges.** On the pure slice, use the same
   typed λSSA observations on both sides. Start with the generated
   acyclic grammar for γ and the pure scalar single-block MLIR profile.
   Prove correspondence for both arms of a diamond and for shared
   arithmetic values. Add θ through the existing loop wrapper after the
   loop slice. Require an explicit decomposition or a certified
   recognizer for reverse translation from a larger graph. [Acyclic λSSA
   lowering][rvsdg-acyclic] · [θ wrapper][rvsdg-theta] · [MLIR scalar
   profile][mlir]

5. **State and scheduling.** Relate one ordered graph memory value to a
   reference heap and observe the returned value and final heap. Add a
   typed state mapping for the RVSDG token boundary. In later PRs, prove
   split/merge and alias disjointness, then load/store motion with the
   anti-dependence constraints. Use same-field, disjoint-field and
   memory-Phi cases to distinguish the required edges. Extend observations
   to traps, calls and I/O with the relevant contracts. [Simple 10][s10] ·
   [Simple 11][s11] · [Simple 13][s13] · [RVSDG state splice][rvsdg-splice]

6. **Optimistic and interprocedural analysis.** Prove a finite,
   intraprocedural SCCP solution for the admitted primitive lattice and
   executable edges. Then prove pruning and folding sound from the
   solution, including a loop where reachability changes a Phi fact.
   Develop combined congruence refinement, call-target discovery, and
   private/escaping state as later slices. [TOPLAS article][combining] ·
   [Rice dissertation][thesis] · [Simple 24a][s24a] · [Simple 24b][s24b]

Put the IR and its semantics under the SSA region, subject to the allowed
imports in [regions.toml][regions]. Use `Defs.lean`/`Thms.lean` and the
matching proof modules. Take other topics through their public headers.
Prove the first slices in the existing SSA dependency direction. Put a
bridge that needs machine semantics on the side allowed to import SSA.
Each proof PR can add a targeted `make check CHECK_TARGETS=+…` command and
fixture, following the [repository instructions][agents].

For the first slice, equality of finite typed return observations is
sufficient on the admitted pure acyclic fragment. Later steps need to state
what a trap, divergence, blocking, an external effect or a rejected graph
means in each model. In particular, absence of a finite return in a
`Part` model can identify neither the cause nor an external trace.
General irreducible control flow, arbitrary effectful RVSDG recovery,
MLIR dialect-specific undefined behavior, Java deoptimization and backend
validation stay open at the boundaries identified above.

[coverage-cutoff]: https://github.com/hiloopai/silmaril-lean/commit/6e351345b6f5497ed986813c6abda35742b83ea5
[son-diamond-rvsdg-inst-thms]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/Institution/ToRVSDG/Thms.lean
[son-diamond-mlir-inst-thms]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/MLIR/Institution/Thms.lean
[son-diamond-mlir-inst-regression]: ../../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/MLIR/Institution/Regression.lean
[son-phi-elim-thms]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/PhiElim/Thms.lean
[son-diamond-rtl-thms]: ../../../Silmaril/Machine/SeaOfNodes/Diamond/RTL/Thms.lean
[son-loop-generic-ssa-thms]: ../../../Silmaril/SSA/SeaOfNodes/Loop/LambdaSSA/Generic/Thms.lean
[son-loop-generic-ssa-regression]: ../../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/LambdaSSA/Generic/Regression.lean
[son-gcm-discovery-thms]: ../../../Silmaril/SSA/SeaOfNodes/GCM/Discovery/Thms.lean
[son-gvn-discovery-thms]: ../../../Silmaril/SSA/SeaOfNodes/GVN/Discovery/Thms.lean
[son-gvn-elimination-thms]: ../../../Silmaril/SSA/SeaOfNodes/GVN/Elimination/Thms.lean
[son-gvn-pass-thms]: ../../../Silmaril/SSA/SeaOfNodes/GVN/Pass/Thms.lean
[son-quad-join-thms]: ../../../Silmaril/SSA/SeaOfNodes/Quads/Join/Thms.lean
[son-quad-loop-thms]: ../../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Thms.lean
[son-memory-forwarding-thms]: ../../../Silmaril/SSA/SeaOfNodes/Memory/Forwarding/Thms.lean
[son-memory-rvsdg-thms]: ../../../Silmaril/SSA/SeaOfNodes/Memory/RVSDG/Thms.lean
[son-memory-diamond-thms]: ../../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/Thms.lean
[pr-diamond-rvsdg-inst]: https://github.com/hiloopai/silmaril-lean/pull/3302
[pr-diamond-mlir-inst]: https://github.com/hiloopai/silmaril-lean/pull/3266
[pr-phi-elim]: https://github.com/hiloopai/silmaril-lean/pull/3293
[pr-diamond-rtl]: https://github.com/hiloopai/silmaril-lean/pull/3272
[pr-loop-generic-ssa]: https://github.com/hiloopai/silmaril-lean/pull/3279
[pr-gcm-discovery]: https://github.com/hiloopai/silmaril-lean/pull/3294
[pr-gvn-pass]: https://github.com/hiloopai/silmaril-lean/pull/3290
[pr-quad-join]: https://github.com/hiloopai/silmaril-lean/pull/3261
[pr-quad-loop]: https://github.com/hiloopai/silmaril-lean/pull/3278
[pr-memory-diamond]: https://github.com/hiloopai/silmaril-lean/pull/3280

[thesis]: https://hdl.handle.net/1911/16807
[thesis-pdf]: https://repository.rice.edu/server/api/core/bitstreams/c5ea1ab7-e6c6-41e7-8e06-3cd5b80aeccd/content
[quads]: https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf
[ir]: https://doi.org/10.1145/202529.202534
[ir-notices]: https://doi.org/10.1145/202530.202534
[ir-pdf]: https://www.oracle.com/technetwork/java/javase/tech/c2-ir95-150110.pdf
[gcm]: https://doi.org/10.1145/207110.207154
[gcm-notices]: https://doi.org/10.1145/223428.207154
[gcm-pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[combining]: https://doi.org/10.1145/201059.201061
[combining-pdf]: https://web.archive.org/web/20250916211010id_/https://dl.acm.org/doi/pdf/10.1145/201059.201061
[hotspot]: https://www.usenix.org/legacy/event/jvm01/full_papers/paleczny/paleczny.pdf
[braun]: https://doi.org/10.1007/978-3-642-37051-9_6
[braun-pdf]: https://pp.ipd.kit.edu/uploads/publikationen/braun13cc.pdf
[cytron]: https://doi.org/10.1145/115372.115320
[wegman]: https://doi.org/10.1145/103135.103136
[alpern]: https://doi.org/10.1145/73560.73561
[graal]: https://doi.org/10.1007/978-3-030-88885-5_8
[termgraphs]: https://doi.org/10.1145/3573105.3575673
[org]: https://github.com/SeaOfNodes/.github/blob/89ceafeec69c412f7bc4798e8145924c9f956060/profile/README.md
[easy]: https://www.dropbox.com/scl/fi/0ww4sgl3ynep9hhe3i4xn/EasySSA.pdf?rlkey=2cp78hzxke62flkmyneiebzoz&dl=1
[slides]: https://www.dropbox.com/scl/fi/cxykfvlzsmlcatyg6rlbt/SeaOfNodes.pdf?rlkey=z6o7y3rwr6atrejilcze6r8x0&e=1&dl=1
[simple]: https://github.com/SeaOfNodes/Simple/tree/f0a6c6757a795b8e186de0076836a87acef59fa7
[roadmap]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/docs/roadmap.md
[reply]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/ASimpleReply.md#complex-schedule
[rebase]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/docs/2026_REBASE/README.md
[evaluator]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java
[scheduler]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter13/src/main/java/com/seaofnodes/simple/GlobalCodeMotion.java
[go]: https://github.com/SeaOfNodes/Simple-Go/tree/37cc338992bcaf4a8a83fd5fbef52a67dc088884
[rust]: https://github.com/SeaOfNodes/Simple-Rust/tree/d75781d1c516805d3042e66ddbd48a9b34fc6878
[rust-baseline]: https://github.com/SeaOfNodes/Simple/tree/fd5178dbf4174933798ecbfbfe06fe35de0337c4
[cpp]: https://github.com/SeaOfNodes/Simple-Cpp/tree/49877551b4ee91c53d799523f15810470a16abbb
[son-pure]: sea-of-nodes-pure.md
[son-pure-defs]: ../../../Silmaril/SSA/SeaOfNodes/Pure/Defs.lean
[son-pure-thms]: ../../../Silmaril/SSA/SeaOfNodes/Pure/Thms.lean
[son-scalar]: sea-of-nodes-mlir.md
[son-scalar-defs]: ../../../Silmaril/SSA/SeaOfNodes/MLIR/Defs.lean
[son-scalar-thms]: ../../../Silmaril/SSA/SeaOfNodes/MLIR/Thms.lean
[son-diamond-defs]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/Defs.lean
[son-diamond-thms]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/Thms.lean
[son-diamond-inst]: control-flow/sea-of-nodes-diamond-institution.md
[son-diamond-inst-defs]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/Institution/Defs.lean
[son-diamond-inst-thms]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/Institution/Thms.lean
[son-diamond-ssa]: control-flow/sea-of-nodes-diamond-lambdassa.md
[son-diamond-ssa-defs]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/LambdaSSA/Defs.lean
[son-diamond-ssa-thms]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/LambdaSSA/Thms.lean
[son-diamond-mlir]: control-flow/sea-of-nodes-diamond-mlir.md
[son-diamond-mlir-defs]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/MLIR/Defs.lean
[son-diamond-mlir-thms]: ../../../Silmaril/SSA/SeaOfNodes/Diamond/MLIR/Thms.lean
[son-loop-defs]: ../../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean
[son-loop-thms]: ../../../Silmaril/SSA/SeaOfNodes/Loop/Thms.lean
[son-theta-defs]: ../../../Silmaril/SSA/SeaOfNodes/Loop/Theta/Defs.lean
[son-theta-thms]: ../../../Silmaril/SSA/SeaOfNodes/Loop/Theta/Thms.lean
[son-theta-regression]: ../../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/Theta/Regression.lean
[son-gcm]: optimization/sea-of-nodes-gcm-legality.md
[son-gcm-defs]: ../../../Silmaril/SSA/SeaOfNodes/GCM/Defs.lean
[son-gcm-thms]: ../../../Silmaril/SSA/SeaOfNodes/GCM/Thms.lean
[son-gcm-loopforest-thms]: ../../../Silmaril/SSA/SeaOfNodes/GCM/LoopForest/Thms.lean
[son-gcm-loophoist-thms]: ../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Thms.lean
[son-gcm-earlyplacement-thms]: ../../../Silmaril/SSA/SeaOfNodes/GCM/EarlyPlacement/Thms.lean
[son-gcm-lateplacement-thms]: ../../../Silmaril/SSA/SeaOfNodes/GCM/LatePlacement/Thms.lean
[son-gcm-dominance-synthesis-thms]: ../../../Silmaril/SSA/SeaOfNodes/GCM/Dominance/Tree/Synthesis/Thms.lean
[son-gcm-loopplacement-thms]: ../../../Silmaril/SSA/SeaOfNodes/GCM/LoopPlacement/Thms.lean
[son-gcm-corridor-thms]: ../../../Silmaril/SSA/SeaOfNodes/GCM/Corridor/Thms.lean
[son-gvn]: optimization/sea-of-nodes-gvn.md
[son-gvn-defs]: ../../../Silmaril/SSA/SeaOfNodes/GVN/Defs.lean
[son-gvn-thms]: ../../../Silmaril/SSA/SeaOfNodes/GVN/Thms.lean
[son-gvn-cyclic-thms]: ../../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Thms.lean
[son-gvn-cyclic-fixedpoint-thms]: ../../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/FixedPoint/Thms.lean
[son-gvn-cyclic-pass-thms]: ../../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Pass/Thms.lean
[son-gvn-cyclic-dead-header-thms]: ../../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Discovery/Return/Deletion/Thms.lean
[son-quads]: control-flow/sea-of-nodes-quads.md
[son-quads-defs]: ../../../Silmaril/SSA/SeaOfNodes/Quads/Defs.lean
[son-quads-thms]: ../../../Silmaril/SSA/SeaOfNodes/Quads/Thms.lean
[son-memory]: memory/sea-of-nodes-memory.md
[son-memory-defs]: ../../../Silmaril/SSA/SeaOfNodes/Memory/Defs.lean
[son-memory-thms]: ../../../Silmaril/SSA/SeaOfNodes/Memory/Thms.lean
[phi-view]: ../ssa-phi-view.md
[phi-view-defs]: ../../../Silmaril/SSA/PhiView/Defs.lean
[phi-view-thms]: ../../../Silmaril/SSA/PhiView/Thms.lean
[rvsdg-mlir-graph]: ../rvsdg/mlir/rvsdg-mlir-graph.md
[rvsdg-mlir-graph-thms]: ../../../Silmaril/SSA/RVSDG/MLIR/Graph/Thms.lean
[rvsdg-mlir-feedback]: ../rvsdg/mlir/rvsdg-mlir-feedback.md
[rvsdg-mlir-feedback-thms]: ../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Thms.lean
[rvsdg-mlir-regionless]: ../rvsdg/mlir/rvsdg-mlir-regionless.md
[rvsdg-mlir-regionless-thms]: ../../../Silmaril/SSA/RVSDG/MLIR/Regionless/Thms.lean
[cfg-versioned]: ../../../Silmaril/SSA/LambdaRTL/CFG/Version/Flat/Thms.lean
[pr-pure]: https://github.com/hiloopai/silmaril-lean/pull/3188
[pr-scalar]: https://github.com/hiloopai/silmaril-lean/pull/3175
[pr-diamond]: https://github.com/hiloopai/silmaril-lean/pull/3135
[pr-diamond-inst]: https://github.com/hiloopai/silmaril-lean/pull/3237
[pr-diamond-ssa]: https://github.com/hiloopai/silmaril-lean/pull/3211
[pr-diamond-mlir]: https://github.com/hiloopai/silmaril-lean/pull/3189
[pr-diamond-eq]: https://github.com/hiloopai/silmaril-lean/pull/3215
[pr-loop]: https://github.com/hiloopai/silmaril-lean/pull/3192
[pr-theta]: https://github.com/hiloopai/silmaril-lean/pull/3210
[pr-gamma]: https://github.com/hiloopai/silmaril-lean/pull/3162
[pr-feedback]: https://github.com/hiloopai/silmaril-lean/pull/3235
[pr-regionless]: https://github.com/hiloopai/silmaril-lean/pull/3133
[pr-phi-view]: https://github.com/hiloopai/silmaril-lean/pull/3186
[pr-placement]: https://github.com/hiloopai/silmaril-lean/pull/3200
[pr-gvn]: https://github.com/hiloopai/silmaril-lean/pull/3225
[pr-gcm-compact-exit-phi]: https://github.com/hiloopai/silmaril-lean/pull/4918
[pr-gvn-dead-header]: https://github.com/hiloopai/silmaril-lean/pull/4895
[pr-gvn-dead-header-cleanup]: https://github.com/hiloopai/silmaril-lean/pull/4934
[pr-quads]: https://github.com/hiloopai/silmaril-lean/pull/3233
[pr-memory]: https://github.com/hiloopai/silmaril-lean/pull/3231
[pr-versioned]: https://github.com/hiloopai/silmaril-lean/pull/3250
[cfg-thms]: ../../../Silmaril/SSA/LambdaRTL/CFG/Thms.lean
[cfg-validation]: ../cfg-validation.md
[ssa]: ../ssa.md
[loop-thms]: ../../../Silmaril/SSA/LambdaRTL/Loop/Thms.lean
[machine-construct]: ../../../Silmaril/Machine/CBackend/RTL/Construct/Defs.lean
[cycle-cuts]: ../../../Silmaril/SSA/Isotope/LambdaSSA/Rewrite/Theory/Closure/Paper/WithConstructorSequencing/UnitSumSquare/Cycles/Automatic/Thms.lean
[rvsdg-thms]: ../../../Silmaril/SSA/RVSDG/Thms.lean
[rvsdg-acyclic]: ../rvsdg/lambdassa/rvsdg-lambdassa-acyclic.md
[rvsdg-theta]: ../rvsdg/lambdassa/rvsdg-lambdassa-acyclic-theta.md
[rvsdg-splice]: ../rvsdg/composition/rvsdg-numbered-splice.md
[rvsdg-calls]: ../rvsdg/interprocedural/rvsdg-interprocedural.md
[mlir-thms]: ../../../Silmaril/SSA/MLIR/Arith/Thms.lean
[mlir]: ../mlir.md
[mlir-ref]: https://mlir.llvm.org/docs/LangRef/
[egraph]: ../../guarded-egraph.md
[dataflow]: ../../../Silmaril/Calculi/Dataflow/Thms.lean
[compiler]: ../compilers.md
[regions]: ../../../regions.toml
[agents]: ../../../AGENTS.md
[s01]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter01/README.md
[s04]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter04/README.md
[s05]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter05/README.md
[s06]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter06/README.md
[s07]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter07/README.md
[s08]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/README.md
[s09]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter09/README.md
[s10]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md
[s11]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter11/README.md
[s12]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter12/README.md
[s13]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter13/README.md
[s14]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter14/README.md
[s15]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter15/README.md
[s17a]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter17a/README.md
[s17b]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter17b/README.md
[s18]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter18/README.md
[s19]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter19/README.md
[s22]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter22/README.md
[s23]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter23/README.md
[s24a]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter24a/README.md
[s24b]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter24b/README.md
[s25]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter25/README.md
[s26]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter26/README.md
[s27]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter27/README.md
[s28a]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter28a/README.md
[s28b]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter28b/README.md
[s29]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter29/README.md
[s31]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter31/README.md

[guarded-feedback-rtl]: ../sea-of-nodes-guarded-feedback-rows-rtl.md
[son-guarded-exit-inversion-thms]: ../../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Native/Preheader/Table/Width/Dispatch/Family/MLIR/Prefix/Producer/Exit/Inversion/Thms.lean
