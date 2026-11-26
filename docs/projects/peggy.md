# Program Expression Graphs and Peggy

The typed PEG core represents finite **Program Expression Graphs** with
sharing, branching and loop feedback. Peggy is the optimizer that uses PEGs
and adds equivalences to build E-PEGs. The current library covers graph
construction, scope and structural guards. The
[guarded Figure 11 denotation](peg-semantics.md) interprets graphs with
well-founded demands. The [checked Egg bridge](peggy-egg.md) proves
equality of native observations for ranked loop-free PEGs. The
[cyclic E-PEG certificate kernel](peggy-epeg.md) checks finite class and
candidate admission conditions and uses semantic evidence for merges
and extraction. The [finite saturation algorithm](peggy-saturation.md)
closes a supplied table of ground obligations and checks a cyclic
selection with structural row evidence.

Ross Tate, Michael Stepp, Zachary Tatlock and Sorin Lerner, *Equality
Saturation: A New Approach to Optimization*, LMCS 7(1:10), 2011,
arXiv:1012.1802v3. The versioned PDF has SHA-256
`5bb3630c9a2a4766c5614b19148e865ee0797c693607b2cdd700b27c38df0b94`.
Locators below use PDF page numbers. [Paper](https://arxiv.org/pdf/1012.1802v3) ·
[Journal](https://lmcs.episciences.org/1016)

## Library boundary

| Header | Interface |
| --- | --- |
| [PEG.Defs](../../Silmaril/SSA/PEG/Defs.lean) | `InstructionSet` indexes primitives by ordered operand types and one result type. `Label` fixes the profiles of parameter, φ, θ, eval and pass nodes. A `Graph` numbers vertices independently of dependency order and uses typed references for operands and roots. The same reference can occur multiple times. A loop parent table distinguishes siblings at the same depth. |
| [PEG.Builder](../../Silmaril/SSA/PEG/Builder.lean) | Construct a table directly with `Node.ofLabel`, or use `RawGraph.check` to check numeric references, operand and root arities, and declared result sorts. Raw labels already carry their instruction profiles and typed parameter slots. The checker permits forward references and feedback and examines every row, including unreachable ones. |
| [PEG.Scope](../../Silmaril/SSA/PEG/Scope.lean) | Walks track dependency roles. `PaperWellFormed` models the three printed clauses in the ancestry order of a finite loop forest. `WellFormed` strengthens the third clause. These are certificate predicates on the whole graph. |
| [PEG.Thms](../../Silmaril/SSA/PEG/Thms.lean) | Checked wiring round trip, preservation of operand slots and edge roles under relabelling, and preservation and reflection of structural admission under opcode maps, vertex/loop reindexing and output changes. Walk lemmas let a client prove reachability invariants with local edge facts or rule out cycles by a strict rank. |

The graph indices bound all references and loop identities. Types and
numbering are distinct from structure. Graph admission uses `WellFormed`
in addition to acceptance by the wiring checker. The graph core leaves
instruction meaning to an interpretation. The guarded denotation uses
well-founded demands on node/iteration-index pairs. An arbitrary sampled
index and the monotonization prefix both contribute evaluation demands.
[Semantics](peg-semantics.md)

## The printed loop guard

Definition 5.1 on p. 23 requires a θ **node** of a strictly enclosing loop on
every cycle through eval or pass. To witness the presence of a θ on a cycle,
the cycle may take either its initial or its feedback edge. The separate
first clause still requires a feedback edge somewhere on every cycle.
`OuterFeedbackCycles` requires that the enclosing θ contributes its
feedback edge to the cycle. `WellFormed.toPaper` checks the implication
from the stronger guard to the printed one.

Consider two ordered loop identifiers `o < l`, with nullary count
instructions for 0 and 1, and the graph

```
A = θ_o(E, 0)
E = eval_l(B, 1)
B = θ_l(0, A)
```

The only simple cycle takes A's initial edge, E's first edge and B's feedback
edge. In particular, the paths from the outer θ to the inner θ cross the
inner eval's first edge. The outer θ occurs on the cycle without decreasing
the outer iteration index. The Lean fixture proves all three printed
clauses for this graph, and proves that the stronger guard rejects it.

With Fig. 11's equations, at outer index 0 let A be any fixed defined count
`k` for all inner indices. Let A be 0 at positive outer indices. B is 0 at
inner index 0 and equals A at the immediately preceding inner index
otherwise. In eval at 1 the only earlier prefix value checked is B at
inner index 0, which is defined. Thus E equals A. The fixture proves the
specialized equations for every pair of indices and exhibits two different
solutions at `(0, 0)`. This is a counterexample to Theorem 1 under the
literal printed hypotheses, already for a two-element total order. The
[guarded denotation](peg-semantics.md) proves that the stronger structural
guard makes the evaluation demands well founded. [Definition 5.1 and Fig. 11](https://arxiv.org/pdf/1012.1802v3#page=23) ·
[Lean fixture](../../tests/ssa/PEG.lean)

## Follow-up roadmap

1. **PEG invariants and rule schemas**. Extend the
   [guarded semantics](peg-semantics.md) with alpha and parameter transport,
   sound syntactic invariance, and reusable rule schemas with proofs of
   their conditions for bottom, overflow and partial operations. For
   example, deleting `φ(c,a,a)` needs a defined guard when `a` is defined.
2. **Dialect institution**. Add `Silmaril.SSA.Peggy.Dialect` and
   `.Institution`. Dialect arrows map symbols forward at fixed profiles.
   Sentences compare typed open graphs at a shared boundary and loop frame.
   Start with discrete models. Reducts precompose symbol interpretations,
   so evaluation after relabelling must equal evaluation in the reduct.
   Prove identity, composition and
   `M ⊨ map f e ↔ reduct f M ⊨ e` using the
   [institution builders](../../Silmaril/Logic/Inst/Builders/Core/Defs.lean).
   Typed program substitution for instruction lowerings needs its own
   interpretation and strictness laws.
3. **SIMPLE and reversion**. Add `Silmaril.SSA.PEG.Simple`,
   `.Simple.Translate`, `.CFGLike` and `.Simple.Revert`.
   Formalize Fig. 15/17 and Theorem 2 as preservation of successful source
   returns. Dropped divergence or faults require a threaded observation
   token and a separate adequacy theorem. Correct the printed depth
   direction of Fig. 19's Type-Eval-Pass in a documented comparison.
   Prove admitted reversion typed and observation-preserving. Keep demands
   for earlier samples or prove prefix definedness. Stage loop extraction,
   branch extraction and sequencing before fusion, MustEval and LICM.
   The authors' Coq `preserveFunctioner` is a proof guide for their
   structured SIMPLER syntax. Its published evaluator samples eval's
   chosen index directly, so correspondence with Fig. 11 needs a proof.
   [Coq sources](https://cseweb.ucsd.edu/groups/progsys/peg-coq-proof/)
4. **E-PEGs and optimization**. The [E-PEG certificate kernel](peggy-epeg.md)
   proves stream equality for same-label congruence and merges with
   independently justified laws. It checks the demand rank and root
   classes of a proposed extraction. The
   [finite worklist](peggy-saturation.md) proves least closure and
   order independence for a fixed table of ground reasons. It derives
   candidate equations for same-label rewiring. The
   [cyclic optimizer](peggy-cyclic-optimizer.md) discovers guarded θ
   self-feedback and checks the compacted candidate on a one-loop profile.
   Extend rule matching and validation, node extension, and reversion. The
   [acyclic bridge](peggy-egg.md) reuses sorted Egg replay. The full
   node-generating form of §4 remains a separate proof obligation. Use an independent graph and
   CFG-like check on extracted representatives. The displayed Boolean
   constraints in §8.3 also admit invalid selections, such as a θ
   initializer selecting its own class. Prove reversion correctness
   separately from any cost-minimality claim. Prove validation by
   composition with adequate frontends at the chosen observation.
5. **IR bridges**. Put `Bridge.Egg`, `Bridge.MLIR` and `Bridge.RVSDG`
   under `Silmaril.SSA.Peggy`. The [Egg bridge](peggy-egg.md) checks acyclic
   unfolding and equality of ordered Figure 11 observations. Start the
   MLIR and RVSDG bridges with pure total acyclic PEGs and regionless MLIR/ordered
   RVSDG values. For structured RVSDG loops, align θ body iterations, exit
   polarity, and PEG pass/eval.
   Compose typed λSSA and the pure Sea of Nodes diamond through RVSDG.
   Use typed, coherently versioned λRTL forward CFGs with an explicit
   exit/store observation. Put machine RTL and Wasm adapters in their own
   regions with their memory, oracle, trapping and divergence hypotheses.
   Use comorphisms for forward sentence translations and model pullbacks
   with naturality and exact satisfaction. A morphism with the same
   signature direction needs sentences backward and models forward.
   A one-way compiler theorem supplies simulation or refinement. Exact
   satisfaction and consequence reflection require separate proofs,
   with model expansiveness for reflection. [RVSDG–MLIR model bridge](rvsdg-mlir-regionless.md) ·
   [SSA and machine boundaries](ssa.md)
6. **Paper view and Java profile**. Add a leaf under
   `Silmaril.Papers.TateSteppTatlockLerner2011` once the reusable theorems
   exist. Register proved institutional edges in the logic graph. Develop
   Java call, heap and exception semantics and a checked partial heap
   linearizer independently. General CFG conversion uses the paper's
   separate reference [50]. Historical reproduction needs pinned Peggy,
   Soot, solver, JVM, benchmarks and machine.

The first two steps depend on the core. SIMPLE and the institution can proceed
independently once the relevant semantic profile is proved. Merge replay can
precede reversion. End-to-end optimization needs both, with matched
observations. SSA may import Prelude, Semantics and Logic under
[regions.toml](../../regions.toml). The
[Formats e-graph snapshot](../guarded-egraph.md) is an architecture reference
from a different region. Sharing executable code with it would require
an independently reviewed promotion of its format-independent core.

## Paper coverage

| Source | Target and current status |
| --- | --- |
| §§1–3, Figs. 1–9 | Planned equality replay and admissible extraction for strength reduction, nested loops, loop motion, CFG restructuring, peeling and branch hoisting. General cross-level fusion, interchange and unrolling are research extensions. |
| §4, Fig. 10 | Planned optimization pipeline, extension and monotonicity (4.1–4.3), uniqueness of reachable normal forms (4.4), and budgeted runs. |
| §5, Figs. 11–12 | Typed structure, role-sensitive graph predicates, the literal-guard counterexample and the guarded denotation are checked. Parameter substitution, Def. 5.2 invariance and verified rule schemas are follow-ups. |
| §6, Figs. 13–18 | Planned typed SIMPLE frontend, factorial translation, context lemmas, Theorem 2 and the completion-token extension with discarded-divergence controls. |
| §7, Figs. 19–34 | Planned CFG-like witness, loop/branch extraction, scheduling and parallel copies, loop and branch fusion, MustEval and guarded LICM. |
| §8, Figs. 35–37 | Planned parameterized Peggy, checked Java heap/exception/call profile, local linearization failure, Rete/worklist refinement and independently checked PB extraction. |
| §9, Figs. 38–39 | Empirical reproduction. The paper reports 84% full saturation among compiled methods and 98% validation across 3,416 methods. Tests of the listed transforms and proofs of certificate soundness are separate deliverables. |
| Appendix A | Planned coverage per rule family, classified as proved, guarded, conditional on a stated model contract, or refuted under the specified semantics. Include arithmetic, code patterns, array/field/effect rules, inlining, vectors, list and wrapper laws, outlining and specialized redirection. |

## Check the core

```sh
lake build --wfail +Silmaril.SSA.PEG.Thms PEGCoreTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEG.lean
lake env leanchecker Silmaril.SSA.PEG.Thms
scripts/check-layout.sh
```

`PEGCoreTests` is part of `make check`. The fixture checks repeated operand
and root references, rejects invalid wiring, checks a dialect symbol
identification and a simultaneous loop/vertex permutation, and checks both
versions of the loop guard through the public headers.
