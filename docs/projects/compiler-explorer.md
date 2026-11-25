# A verified compiler explorer: problems, mappings, comorphisms

## Open the explorer

From this repository, `gh pr checkout 1067` selects the working branch. Use the default database
location for the verified quickstart:

```sh
make compiler-explorer-check
make compiler-explorer-serve
```

Open <http://127.0.0.1:8765/?problem=compiles-to%2Fstraight%2FO2%2Fadd3>. The first command
rebuilds `.lake/compiler-explorer/explorer.sqlite` with exporter evidence for the exact manifest
and model bytes from this checkout. After switching revisions or changing a fixture, stop the
viewer, run both commands again, then reload. To browse without building Lean, skip the first
command: the viewer shows **not loaded** where no exact evidence is available and preserves only
matching evidence. C, typed Ail and Core are separate selections; the Ail pane shows the evaluated
frontend result, while Core has its own checked elaboration equality. Stop the server with Ctrl-C.

On a generated Pages site, click **Compiler → Open the source ↔ target viewer**; on a clean
checkout with the project libraries built, `make pages` writes `_site/`. Serve it locally with
the same Range-aware server as the Pages browser tests:

```sh
python3 -I tools/silmaril-project/tests/explore/pages_server.py --root _site --port 8000 \
  --log .lake/pages-preview-requests.jsonl
```

Open <http://127.0.0.1:8000/compiler/> and stop the server with Ctrl-C. Plain `python3 -m
http.server` does not provide the Range responses the main explorer needs to open a large
`project.sqlite` automatically when following C or ELF tab links. A generated site is not a
deployment; use the viewer, `project.sqlite`, and artifact catalog from the same checkout.
The generated viewer only imports project rows with matching shape and arguments. A database
without the expected row says **evidence unavailable**; the wrong row shape or arguments says
**incompatible evidence**. Neither is a theorem rejection or a refutation. Rebuild the site and
database together to refresh those rows, or use the standalone quickstart to run the exact Lean
exporter. The standalone local API can still use that site's artifact catalog with
`cexplorer.py serve … --viewer http://127.0.0.1:8000/` without importing its evidence.

A compiler explorer puts a source program beside the target code a compiler made from it and
links fragments of the two. This page describes a vertical slice that keeps navigation links
separate from Lean statements with statuses decided from the Lean build:

* a **generic** Lean API (`Silmaril.Compiler.Explorer`): compilation problems over relational
  semantics with a backward refinement statement, segment mappings, segment disciplines, and the
  relations that the repository's institution semi-comorphisms generate;
* a **deterministic specialisation** (`Silmaril.Compiler.Explorer.Det`): machines
  `τ → Option τ`, the cut-point simulation of [compiles-to](compiles-to.md), and the theorem that
  connects them to the generic statement;
* the **C/x86-64 instance** (`Silmaril.Project.Shapes.CompilesTo.Explorer`) over the existing
  segment proofs, with problem shapes for `sil project`;
* the exporter `cexplorer-export`, the database and read-only API
  (`tools/compiler-explorer/cexplorer.py`) and the page (`tools/compiler-explorer/ui/`);
* fixtures in `examples/compiler-explorer/`. Compiled builds: the compiles-to objects and four
  staged programs. A decompiled block. An imported pair.

```mermaid
flowchart LR
  C["source (sha256)"] -->|"compiled: gcc 13.3.0, pinned image, receipt"| T["target (sha256)"]
  T -->|"decompiled: SemLift + WordC, receipt"| C
  C -.->|"debug info / decompiler block: navigation only"| T
  M["manifest: artifacts, derivation, models, ABI, relation, comorphism, fragments, edges, obligations"]
  M -->|"cexplorer-export, run by `verify`"| E["evidence"]
  P[("sil project database: rows, statuses")] -->|"`project` adapter: shape + arguments"| DB
  M --> DB[("explorer database")]
  E --> DB
  DB -->|"GET only"| UI["page"]
```

## The generic layer

| notion | Lean | meaning |
| --- | --- | --- |
| problem | `Problem σ τ R T` | source and target semantics (`Source`: relational steps, wrong states, final states with results), the entry relation (the ABI for code), the result relation |
| translation | `Problem.Refines` | from related entries with a safe source (no undefined behaviour, every run finite), the target is safe and finite, never stuck before a final state, and each target result is related to the result of some source run |
| non-vacuity | `Problem.Inhabited` | some related entry has a safe source |
| vertical composition | `Problem.comp`, `Problem.Refines.comp` | C → IR → machine; refinements compose when the middle semantics agree |
| mapping | `Mapping` | program points: the states at each point on each side, and the relation there (data) |
| coverage | `Mapping.Covers L` | no states are related at a point outside `L` |
| edge validity | `SegmentDiscipline` | a discipline says when an edge is valid and proves that valid edges compose into `Refines`; `all_of_listed` and `refines_of_listed` add coverage |
| relation refinement | `Mapping.RefinesAt G K` | the mapping's relation implies `G` at the points `K` |
| generated relations | `Gen.Agrees`, `Gen.Witnessed`, `Generator` | from a `Silmaril.Inst.SemiComorphism` and readings of states as models: entry, result and point relations |

**Direction.** `P.Refines` is a *backward* statement over **all** target runs, so it reads the
same for deterministic, nondeterministic and interleaving targets: the target's behaviours are
among the source's. `M.RefinesAt G K` says that the mapping's relation is at least as strong as
`G`. `Problem.Refines.mono`: a stronger entry relation and a weaker result relation keep a
refinement.

**Undefined behaviour, divergence, I/O, concurrency.**
* Source undefined behaviour permits every target behaviour. A divergent source run is not
  covered: `Source.Safe` includes termination.
* Source nondeterminism is handled because the target's result must be the result of *some*
  source run.
* I/O is what the result relation observes. There is no event trace.
* Concurrency fits the generic problem as an interleaving `Source`. No concurrent instance and no
  nondeterministic segment discipline exist yet. Replacing the x86 model with a multithreaded one
  needs that discipline, not a new problem type.

### Comorphisms, and what is generated

Relations come from the repository's **semi-comorphisms** (`Silmaril.Inst.SemiComorphism`,
`docs/projects/logic-inst.md`). They translate signatures and sentences forwards and models
backwards, with the satisfaction condition on a class of sentences, in the directions that hold.
States are not models: a reading maps a state to a model at a signature. Two generated relations
are defined:

* `Gen.Agrees f S readS readT Ψ s x`: each observed sentence holds of the source reading exactly
  when its translation holds of the target reading. Through the satisfaction condition this is
  agreement between the source reading and the model translation of the target reading
  (`Gen.agrees_iff_reduct`). Generated relations compose along `f ≫ˢ g` (`Gen.agrees_comp`).
* `Gen.Witnessed f S readS readT fam obs s x`: for each observed family, some instance holds on
  both sides. For value observations this means each observed object has a value that both sides
  hold (`Gen.witnessed_of_reduct`).

A `Generator` (one semi-comorphism, the entry, result and per-point signatures, the readings)
generates both kinds of relation:
* the compilation relations, as `Generator.problem`'s entry and result;
* the segment relations, as `Generator.mapping`'s point relation (a control relation and
  agreement).

`Generator.mapping_refines` is the specification of that construction, not a correctness result.
A mapping chosen by hand, such as the C instance's, is related to a generated relation only by a
separate refinement theorem.

`obsInst O V` is the institution of value observations: one signature, sentences `o = v`, models
the relations `O → V → Prop`. `obsSemi loc` is the semi-comorphism of an observable map `loc`.
Its satisfaction condition holds both ways on every sentence, and with one signature naturality
is trivial. It is the signature part of a debugger's location map, not a translation of
programs. No comorphism in the repository translates C states to x86 states (models are
valuations here, not states), so none is claimed.

## The deterministic specialisation

`DetProblem` is the earlier problem shape: a machine `τ → Option τ` whose return and result are
read relative to its entry state. Its fields are as follows.
* `DetProblem.Valid`: the machine reaches its **first** return (`DetProblem.Step` stops there).
* `DetProblem.toProblem`: the generic reading. Target states are (entry, current) pairs, and the
  machine stops at the first return.
* `DetProblem.refines_of_valid`: validity gives `Problem.Refines`. Determinism makes the one run
  the only run.
* `DetMapping` with `EdgeValid k := Corr.Segment k`.
* `DetMapping.refines_of_segments`: valid edges of a mapping that starts at the entry and relates
  no return give the refinement.
* `Det.discipline`: all of this as a `SegmentDiscipline`.

`Det.Counterexample.edges_not_enough` is a mapping whose one listed edge is valid and whose
points are not covered, with neither `Valid` nor `Refines`. Individually valid links prove
neither the mapping nor the translation.

## The C/x86-64 instance

`FnData.compilation I k0` is the deterministic problem of a function. Its source is the Cerberus
Core run of the procedure. Its target is the model `I` running the function's bytes. Its entry is
the System V call. Its result is the System V return: callee-saved registers restored, writes
only in the frame, and the value in `rax`.

| theorem | statement |
| --- | --- |
| `FnData.compilation_refines_of_segments` | every proved segment gives `(F.compilation I k0).toProblem.Refines`, for every caller continuation |
| `FnData.compilation_inhabited` | not vacuous: for the empty caller continuation, a canonical Core entry that is safe and a System V entry the placement admits are related |
| `FnData.refines_dwarf` | for every function, the mapping refines the relation generated by the location semi-comorphism `dwarf = obsSemi (o ↦ (o.off, o.size))` |

`readCore` reads a Core state as a valuation of C objects: the object's symbol is bound to an
allocation whose `int` slot holds `n` (`Locals.Slot`). `readFrame` reads a machine state as a
valuation of frame slots (`DW_OP_fbreg`, frame base the CFA). The refinement goes from the
verified Core library's invariant (`StateMem.Inv`) to Core's own reading of the object. The
theorem says less than it might seem to:
* The slot offsets are the `FnData`'s. `tools/c-tv` read them from DWARF with an unverified
  reader, and no statement says they are the object's DWARF locations.
* It is close to the definition of the relation, because `ObjectsAgree` is part of it.
* It gives *a* common value, not equality of every read: a slot fixes four bytes, not an integer.

## Segment relations in the page

There are two kinds of link, never mixed:

* **Navigation links**: the line table read by `tools/c-tv`, the `.loc` directives of `gcc -S`
  (as Compiler Explorer reads them), or a decompiler's input block. They say where code came
  from, and carry no obligation.
* **Semantic links**: the program points of a Lean mapping. The source fragment is the
  statement's lines (`PointOf F k line`, proved). The target fragment is where the segment starts,
  laid out up to the next point. The proof is about the run, which may jump.

| phenomenon | where |
| --- | --- |
| one line, several discontiguous instruction ranges | `msort.c -O2`, line 8 (inside the inlined `merge`) |
| one line, copies in several functions (duplication) | `lisp.c -O2`: `cons` and `mk` inlined into `read` and `eval` |
| a call with no code of its own (inlining, elimination) | `msort.c -O2`, line 24 (`merge(…)`) |
| instructions from another file | `lisp.c -O2`: `putchar` from `bits/stdio.h` |
| generated code (prologue, argument spills) | `-O0`: attributed to the opening brace |
| no statement-level point | every `-O2` object: c-tv's reason is shown on the link |
| uncovered source, uncovered target | the page's footer; the decompiled block excludes `ret` |

**Fragments** are sets of ranges in one artifact's coordinate space, identified by
`sha256(artifact sha256 : space : ranges)`.

## Directions and provenance

| direction | what is checked on ingest | fixture |
| --- | --- | --- |
| compiled | the compiler's receipt read the source bytes and wrote the target bytes, in the recorded image | `examples/compiles-to`, `programs/` |
| decompiled | the decompiler's receipt read the target bytes and wrote the source bytes | `decompiled/scale`: gcc 13.3.0 `-O2` of `scale.c`, decompiled by `SemLift.propose`, `SemLift.check` (which accepts the proposal) and `WordC.regenerate` into `wc_scale` |
| imported | nothing is derived; an origin may only be recorded as a claim | `imported/sha256-compress`: `xc_sha256.c` and the clang `-O2` assembly of `apps/sha256-cli` |

The decompiled fixture has one stated obligation, `decompilation`:
`Silmaril.Compiler.Explorer.DecompiledBlock "scale" bytes 1 inputs source`
(`Silmaril.Compiler.Explorer.Decompiled`). It says three things:
* the proposer's summary of the block is accepted by `SemLift.check`;
* its `rax` expression lowers to a term that prints as exactly the text of `scale.dec.c`;
* from every state where the block is loaded and entered, the machine reaches a state whose
  `rax` is the C0 value of that term's typed Ail (`WordC.checked_output_c0`, through the generic
  `decompiledBlock_of`).

`CompilesToExamples.Explorer.Decompiled.scale` proves it for the five bytes, by kernel evaluation.
Its statement is built from the fixture's own data:
* the source artifact's text, as a Lean string literal;
* the block's bytes. On ingest, the database reads the object's `.text` section from the ELF file
  and checks that the bytes are there at the receipt's range. That is a tool check, not the
  kernel's.

What is not stated, and why:
* The C text is *printed from* the term. It is not parsed or elaborated back, so no Cerberus or
  C0 reading of the text itself is involved.
* `ret` and the System V convention lie outside the block.
* C0 is the repository's C subset interpreter, not Cerberus.

So the translation, ABI, mapping and refinement questions stay unsupported for this problem. The imported assembly has a functional contract against a SHA-256
specification (`Sha256O2.sha256_compress_O2`, [sha256sum](sha256sum.md)). That contract is not a
statement about the C source beside it.

## Evidence, statuses and trust

A status comes from one of three origins. Only the first two can make an obligation proved.

| origin | how | counts as proved |
| --- | --- | --- |
| `exporter-run` | `cexplorer.py verify` runs `cexplorer-export` on the manifest. The exporter needs a theorem whose type is the obligation's statement (up to reducible unfolding), with the standard axioms. | yes |
| `sil-project` | `cexplorer.py project DB project.sqlite` reads the obligation's row. The row must be an instance of the kind's shape (`ROW_SHAPES`) with the manifest's arguments, have a THM status at tier `kernel`, and its theorem must use the standard axioms. | yes |
| `file` | `cexplorer.py evidence` records an exporter file someone handed in | no: shown as **claimed** |

| status | meaning |
| --- | --- |
| proved | as above, for this manifest version |
| unbound | proved, but the artifact obligation (the function's bytes are the registered object's code) is not proved |
| claimed | a handed-in exporter file says kernel |
| open | stated, no proof named or the row is open |
| unchecked | a proof is named, no result recorded |
| rejected | the named proof is missing, not a theorem, about another statement, or has other axioms; or the row is of another shape or function |
| stale | proved for another version of the problem only; evidence never moves between versions |
| unsupported | not stated: no model covers it (with the reason) |

**What the checks do.**
* Ingest re-reads and re-hashes every artifact. Symbolic links out of the repository are
  refused.
* Statements are templates per obligation kind, over Lean names that must be identifiers. The
  model and comorphism names must be the context's, and the target value must read the
  registered target artifact.
* A compiled problem needs a receipt about its exact bytes.
* Tests are stored apart from evidence, and an execution test never proves an obligation.

**What each link rests on.** Each line below is shown in the page.
* Kernel:
  - every obligation shown proved;
  - the binding of the function's bytes to the registered object (artifact obligation).
* Not checked by the kernel:
  - Evaluation (`#guard`): C text → typed Ail.
  - Unverified: the line table and slot offsets read by `tools/c-tv`.
  - Recorded only: receipts (compiler, version, image digest, hashes).
  - Trusted: the semantics themselves (the Lean port of Cerberus Core, `Silmaril.X86.Open.isa`).
  - Replay boundary: the exporter reads theorem types from `.olean` files. `replay.sh` (run by
    `make compiler-explorer-check`) re-runs the toolchain's `leanchecker` on the evidence modules:
    - each module's own declarations go through the kernel again, on top of imports loaded from
      their `.olean` files;
    - the imports themselves are not replayed (no `--fresh`, which would include Mathlib);
    - it is the same kernel as the build, not an independent checker.

    The script runs one `leanchecker` process per module, with bounded parallelism. The exporter
    reuses an environment only for manifests with the same module list, while retaining separate
    snapshots, render checks and verdicts for each manifest.

**Conditional and unconditional.**
* The translation holds from every related entry whose Core state is safe: no Core run from it
  reaches undefined behaviour, and every Core run from it is finite. From any other entry it says
  nothing.
* `c.compiles_to` (every Core entry, through `Task.<f>_safe`) remains open.
* Non-vacuity is shown for one entry.
* "ABI" means that an entry state exists for every argument tuple. Every execution's return-side
  ABI is part of the translation.

## Database

The schema is at version 6 (`schema_migrations`). Migrations 2–5 record evidence origin,
project rows, refutations and declaration locations, and judgments without a translation
direction. Migration 6 records the exporter run's model-artifact binding and declaration
locations. Tests migrate a version-1 database with its data.

The tables:
* `artifacts`: bytes by SHA-256, insert-only.
* `problem_versions`: one per manifest, with direction, derivation, models, ABI, relation,
  comorphism and a context hash.
* `fragments`, `edges`, `edge_ends`: the many-to-many mapping.
* `obligations`, `evidence`, `tests`.
* `rejections`: every refused manifest, evidence file or project database, with the reason.

The server opens the database read-only and answers GET only. It has no endpoint that compiles
or runs anything, and it sets a restrictive Content-Security-Policy. The page inserts every text
with `textContent`.

## `sil project` and the Pages explorer

The explorer's obligations of the compiles-to builds are rows of the project
(`silmaril/compiler-explorer.toml`, group `silmaril.compiler_explorer.all`, a child of
`silmaril.all`). They are instances of six shapes, `silmaril.shapes.compiler_explorer.c.*` (including `code`, the binding of the function to its object), and
are solved in `CompilesToExamples.Explorer.Rows`. `sil project dump`, `sqlite` and `explore`
therefore record their statuses and show them on the published explorer like every other row.

The adapter boundary is the project database schema `silmaril.project-db.v0.1`:
* `problems.name` is the row;
* `edges(kind = 'instance', parent → child)` gives the shape;
* `instance_args(problem, pos, term)` gives the arguments;
* `statuses(problem, status = 'THM', tier = 'kernel', via)` gives the solving theorem;
* `answer_axioms(decl, axiom)` gives its axioms.

The adapter refuses another schema. `make pages` builds the same two-pane viewer at `compiler/`
and links it from the main explorer's Compiler and Corpus tabs. `pages.py` ingests committed
manifests, applies the exact project-row adapter, and writes static problem JSON. Missing
rows remain missing; no exporter run or interactive compile service is supplied. These are
existing fixtures, not source-to-target proofs for every corpus function.

## Files first: problem forms, stages, environments

The primary problem is about **text files** (`Silmaril.Compiler.Explorer.Text`):
* `Files`: a map from names to bytes.
* `IncludeEnv`: the files a preprocessor may read, the search order, the predefined macros and
  the options.
* `RelProblem`: an arbitrary relation between a source and a target. `RelProblem.Segments`
  relates chosen fragments with separate membership relations, with no execution or coverage
  requirement. A morphism maps the pair and preserves the relation; it transports proofs
  forward and refutations backward. Identity and composition obey the usual laws.
  `RelProblem.Refines` is pointwise implication (reflexive and transitive).
* `Verdict`: proved, refuted or unknown.
* `Stage`: a named partial function with a trust tag (`verified`, `evaluated`, `trusted`).
  - `Stage.comp` composes stages.
  - `Stage.validated R` says that every successful output is related to its input by `R`.
    Validation composes; it does not establish that a stage succeeds.
  - `Stage.pullback` interprets any relation through independent source and target stages;
    refining that relation refines its pullback.

A relation may have **no operational semantics** and still have a Lean statement. When there
is only a receipt, the presentation uses `Semantics.none`. The `programs/*` problems are of that kind:
"gcc compiled this C to this assembly", recorded by a receipt and tested by one run. The page
labels them "relation · no semantics" and shows no semantic question for them. No comorphism is
fabricated for them.

`Reading` is the semantic specialisation: parse each side with a stage and relate the parses by
a compilation `Problem`. `Reading.toRel` is the relation that induces on files. A manifest
records its form as `semantic`, `relation` or `judgment`. Stage views, segment-link mode, each
side's model, and the comorphism are presented independently. Switching a view never changes
the theorem. Choosing a different model or comorphism for a new problem requires a new manifest
and new evidence, not a client-side toggle that carries evidence forward.

**Stages and their exact outputs.** Each side of a problem can show its source or a stage's
output (the "show" selector).

| problem | source side | target side |
| --- | --- | --- |
| compiles-to | C text, typed Ail (`typed-ail.sexp`), or model Core (`core.sexp`) for supported functions | raw ELF bytes; `objdump`; Lean decoder for supported functions (`decoded.txt`) |
| C ⇒ C | C text, typed Ail, or Core | C text, typed Ail, or Core (independent of the source selector) |
| restricted typing | C text | extracted operand types; separate frontend diagnostic |

The Ail and Core views indent their own stored S-expressions for reading and mark the result
as display-only. **Exact text** switches back to the selected stage's original serialization;
its artifact download always returns the original bytes. The pane names that stage's input,
output and model and links to its evidence and Lean definitions when available. Fragment links
are hidden unless both panes show their primary representations: C or listing positions are
not Ail or Core positions. If a fixture has no bound Ail or Core artifact, it offers no such view.

The trust of each stage:

| stage | trust | checked by |
| --- | --- | --- |
| C text → typed Ail (Lean frontend) | evaluated | `#guard` (compiled evaluation) |
| typed Ail → Core | verified for these inputs | `ElabAil ail = .ok core` (`elab_eq`, kernel; independently on both C ⇒ C sides) |
| `objdump` | trusted | nothing: a receipt only |
| Lean decoder | verified | obligation `decoding`, `decodesAs` (kernel) |

`fixtures.py stages` materializes the two standalone artifacts from the captured probe payloads.
Before recording evidence, `verify` separately compares their bytes, and the C and decoder
views, against renderings of the actual Lean declarations. This is a compiled rendering/identity
check, not a kernel proof about a printer. A Core equality proves neither the evaluation that
produced typed Ail nor a compilation relation. Without exact renderer binding and evidence, a
generated or freshly ingested view shows the stage as unchecked. `decodesAs` proves the
listing value for the function's code; the separate object-binding obligation links that code to
ELF bytes. `objdump` instructions are not proved correct by either check.

**Preprocessor environment** (`fixtures.py env`). It records:
* the main file under its build working-directory path, by SHA-256;
* observed headers (`gcc -M`), by path, SHA-256 and size, for each program and optimization profile;
* ordered active include directives (`gcc -E -dI`), paired with enter/return line markers and
  cross-checked against the ordered opened headers and depths (`-H`);
* include search order (`gcc -E -v`), predefined macros (`gcc -dM -E`), and their probe flags;
* the actual build command and pinned image.

The table uses the operand spelling inside quotes or brackets and labels **direct** (from the
main file), **indirect** (from a header), and **implicit** (no source directive). Open a name
for its resolved path, including-file position, and ordered occurrences; open a fingerprint
for the full digest. Repeats group for display only, retaining the identities of their parent
file entries; aliases and the same spelling resolving to different paths stay separate. A
source line that matches the emitted operand confirms a literal spelling. `-dI` can report a
macro-expanded operand; if not matched, the original spelling is not claimed. An emitted
directive with no file entry is shown as **not entered**: the resolved bytes and reason (guard,
once-only behavior, etc.) are not emitted by this probe. Inactive conditional branches do not
appear. A fixture without a dependency probe does not establish that it has no headers.

`fixtures.py include-map MANIFEST OUT` materializes the observed filename → byte map as
`files_hex` in JSON, reading headers from the pinned image and refusing mismatched size or
SHA-256. The receipt binds the probe flags and main-file hash. This is a trusted observation,
not a complete preprocessor trace, a formal preprocessor, or a verified general C parser.

**Extension point:** the occurrence trace and its parent indices can feed a Lean
`Includes(Name, Name*)` judgment or graph viewer later. Spelling, path, entered occurrence,
and content hash are different projections, not interchangeable node keys. A later model can ask
whether a given file tree and search list realize the graph, or whether any compatible tree and
search list exist. Neither compatibility claim follows from today's trace.

**Debug information → problems.** Each compiles-to problem lists the facts c-tv extracted from
the object's DWARF with `gimli`, which is not verified. There are three kinds of fact:
* line ranges, used by navigation links only;
* point placements, used by the segment, mapping and translation statements;
* frame slots, used by the location relation and the segment statements.

Each fact links to the obligations that depend on it. The view supplies the input ELF and
recorded `correspondence.json` bytes, compiler profile and function. A wrong offset can change
the statement or the relation it proves; proving a statement about the chosen offsets does not
validate the extractor. Facts are shown as "extracted", never as checked.

### Compact signed-int view

For `add3` and `max2`, choose **Compact C (signed int)** in the source selector. This is a
separate projection of the exact typed Ail, not an intermediate input to Core elaboration.
`Exact text` shows the canonical `compact-c-i32-v1` S-expression. Download the source-origin
sidecar from the stage card: its IDs are zero-based preorder occurrences in the compact tree.
The sidecar stores the Ail location and, on a `let`, the name of the new slot. Parameters
occupy the initial slots. These coordinates are not C lines, DWARF offsets or Core program
points; the explorer disables primary fragment links for both compact displays.

The compact tree represents an unqualified LP64 signed-`int` leaf function: nonnegative
decimal `int` literals, reads from initialized slots, checked addition, signed `>`, and
initialized locals before a return or a terminal `if`. It refuses other statements and types,
including uninitialized locals, assignments, loops, calls and pointers. There is no memory,
aliasing, global state or I/O in the model. The function checks argument count, signed range
and slot scope; signed addition overflow stops with UB, including in initialization.
Evaluation reads left to right without side effects. Only the chosen branch runs.

The evidence has four distinct scopes:

- **Extraction.** The badge checks equality of the projection and binds both exact byte
  streams. `project_sound` shows that every successful recognizer result is scoped and
  structurally corresponds to the sole original Ail function body.
- **Generic C0 semantics.** `ExprProjection.eval_eq` preserves expression results and stops.
  `FunctionProjects.activation` extends this compositionally to declarations, branches and
  returns for the original body. It starts after argument setup, with related initialized
  in-range parameter slots and the matching C0 body, local types and return type. For fuel
  at least `body.fuel + 2`, it gives the same in-range return without observable effects on
  globals or output, or the same signed overflow stop. No other stop or exhaustion occurs
  in that model under those hypotheses. This does not prove that `C0.prepare` or `callFn`
  establish those hypotheses for every accepted program.
- **Elaboration.** The existing exact Ail → Core equalities bind each original typed Ail
  program to its Core result; the compact tree is not an input to that elaborator.
- **Concrete Core behavior.** `add3_agrees` and `max2_agrees` compare compact and C0
  returns to a forced Core run on `add3(1,2,3)` and `max2(1,2)` respectively. To generalize
  this would require a relation between initialized slots and Core object state, showing
  that all admissible executions of the elaborated body preserve returns/effects and
  safe termination on compact success, with a separate account of overflow and stops.
  Neither elaboration equality nor the closed runs supply that result.

C text → Ail remains a compiled frontend evaluation, not a parser theorem.

**Design and provenance.** Earlier MiniC work uses named state and checked arithmetic,
and separates shape recognition of elaborated Core from closed validation. This view
adapts those ideas, not that language or implementation. It projects directly from typed
Ail and reuses C0's integer domain and stop model; a second named-state interpreter or
the unsigned wrapping WordC representation would not provide that bridge. Dense slots
and a separate origin table remove repeated metadata without conflating node identity
with storage identity. Arena allocation and interning are deferred: the example trees
are small, and sharing repeated metadata in larger programs needs separate measurements.

```sh
lake build Silmaril.Compiler.C.Compact.Codec
for item in straight branch; do
  dir=examples/compiles-to/$item
  lake env lean --run tools/compiler-explorer/compact_fixture.lean \
    "$dir/typed-ail.sexp" "$dir/compact.sexp" "$dir/compact-origins.sexp"
done
python3 -I tools/compiler-explorer/fixtures.py manifests
make compiler-explorer-check
```

`node tools/compiler-explorer/compact_sizes.mjs` counts expanded wire lists, semantic
constructor occurrences, and exact and formatted UTF-8 bytes. For `add3`, exact Ail/Core
files are 6,101/21,231 bytes and compact tree + origins are 99 + 735 bytes. For `max2` they
are 4,024/17,927 and 85 + 573 bytes. This removes repeated metadata and narrows scope;
it does not measure shared heap objects or compress the full Ail or Core AST. `sum_to`
is 8,664/36,729 Ail/Core bytes; the `callee`/`caller` unit is 4,867/18,619. Both elaborate
but have no compact projection. For these baselines, run `compact_baseline.lean` on
`examples/compiles-to/loop/loop.c` or a caller/callee source and pass the output directory to
`compact_sizes.mjs`. `compact_fixture.lean bench <typed-ail.sexp> <calls>` compares
warm evaluator calls with checked equal returns, not parser, elaborator or native build times.

## More general problems, and negative results

**C ⇒ C translations** (`Silmaril.Project.Shapes.CompilesTo.Translate`).
`CanonicalRefines F G`: from the canonical entries, wherever the source is safe, every outcome
the target halts with is one the source halts with. `CanonicalEquivalent` is refinement in both
directions. This is inclusion of terminating outcomes, not a target progress or liveness theorem.

`CanonicalRefines.refuted_of_ends` refutes a translation from two evaluated runs on the same
arguments. The source's forced run is its only run (`Forced.terminal_unique`). The target's run
reaches an outcome the source cannot reach. The fixture
(`examples/compiler-explorer/c2c/translations.c`, `CompilesToExamples.Explorer.C2C`) has these
translations of `add3`:

| translation | `add3(1, 2, 3)` | status |
| --- | --- | --- |
| `add3_reassoc` (reassociated) | 6 | open: different intermediate signed overflow is possible |
| `add3_double` (returns twice the sum) | 12 | **disproved** |
| `add3_operand` (`s + a` for `s + c`) | 4 | **disproved** |
| `add3_drop` (drops `c`) | 3 | **disproved** |
| `add3_op` (`s - c`) | no checked run | open |

"Disproved" means a theorem of the statement's negation, checked by the kernel and recorded as
`refuted`. "Open" means unknown. A failed check of a named proof is "rejected". The three are
never conflated.

**A type error under a restricted judgment** (`Silmaril.Project.Shapes.C.AdditionFragment`).
This judgment is the constraint of C11 §6.5.6¶2 on the operand types of `+`, over Cerberus's
`Ctype`. It is the only typing judgment stated here; struct completeness is not modelled.

`examples/compiler-explorer/typeerror/addp.c` adds two `int *`.
`addp_parses` kernel-checks that a small source recognizer extracts two `int *` operands from the
exact source literal, and `addp_type_error` proves that the recognized source does not satisfy
the additive constraint. `addp_int_accepted` checks a pointer-plus-integer counterpart under
the same judgment. The recognizer does not preprocess, parse arbitrary C or check the rest of
the program. The general frontend's "typing not yet ported" message is a separate evaluated
artifact and supplies no proof.

## The page

* **Highlighting.** C, assembly and Core S-expressions are highlighted. Highlighting produces
  tokens, which are inserted as text spans, never as HTML; the tests check that every character
  survives and that markup stays literal.
* **Questions.** Each question is a status badge, a short title, an info button (hover shows the
  text as a tooltip; click or keyboard toggles it, with `aria-expanded`) and links. Linked code
  lines can be focused and activated with Enter or Space.
* **Statuses.** "proved", "disproved" and "open" (unknown) have distinct styles. "unsupported"
  means no statement. A relation with no semantics shows no questions at all.
* **Links.** Every obligation, including individual edges and points, is reachable from the
  questions panel. Proofs and exact model definitions link to their Lean files and lines at the
  clean commit recorded by `verify`:
  - the silmaril explorer's routes on main: `#/problem/<row>`, `#/artifact/<registered name>`,
    and `#/source/<decl>` for a row's solving theorem;
  - immutable exact-byte downloads, including artifacts with no Lean evidence;
  - the C (`#/c-artifact/<sha>`) and ELF (`#/elf-artifact/<sha>`) tabs on sites generated by
    `make pages`. Both verify the full SHA-256 in the browser. ELF sections are labeled as
    unverified; this route neither needs nor extends the pinned-file ELF theorems.

  The server checks the deployed catalog at startup and only emits C/ELF links for a matching
  SHA-256, size, media kind and path. `--viewer URL` can point it at a locally served Pages build.
  Before the updated site is deployed the public Pages site will not advertise these routes.
  The C-program (#900) and Assembly (#890/#851) features remain separate.

## Blocks on one side, fragments on the other

The usual shape is **target block ↔ source fragments** (or the reverse for another problem).
It is an arbitrary `RelProblem.Segments` relation: choose a block or region model's membership
on one side and artifact byte ranges on the other. Neither side has to use the other's model.
Zero, one, or many associations are allowed; fragment ranges may be discontiguous and shared
by multiple blocks. There is no implicit totality, instruction correspondence, same execution
model, or graph isomorphism. The API's optional `extra.blocks` records the modeled side; a
navigation edge does not acquire an operational interpretation by being listed there.

The `add3 -O2` example instantiates `Silmaril.Machine.Region.X86.Candidate` and `propose`
from [#1048](https://github.com/hiloopai/silmaril-lean/pull/1048), on the existing checked decoded
listing, not on `objdump`. `CompilesToExamples.Explorer.add3Block_shape` checks the selected
entry and instruction starts at the compilation model's placement `0x401000`, and the
candidate's `Top` exit allowance (`ret`). `verify` also byte-compares the displayed placement
with a rendering of the candidate's entry. The ET_REL symbol's section-relative range `[0,6)`
and file slice have a different coordinate system from that modeled placement. A content
address combines the ELF hash, section and exact ranges, symbol, model placement and named
model/decoder. The opposite side records source bytes and the exact parse-stage input and output
when present. The generated ELF tab can open that block's exact bytes and return to its
source-fragment associations. There is no supported full ELF CFG graph route on main.

| Layer | Claim in the example |
| --- | --- |
| File bytes and decoder | Separate existing `ObjectFn` and `decodesAs` obligations, with their individual evidence statuses. The certificate adapter requires the selected symbol to fill `.text`; smaller slices need their own symbol-offset binding. The ELF browser checks the raw artifact hash; its locator is not a Lean loader. |
| Block membership and boundary | A chosen contiguous candidate with exact instruction starts and `Top` allowance; no recovery or local `Valid` claim. |
| CFG adjacency and coverage | Not certified or used to justify the associations. A candidate or valid local region does not prove graph coverage. |
| Local semantic validity | [#1048's `jump_valid`](https://github.com/hiloopai/silmaril-lean/blob/8300ad003/Silmaril/Machine/Region/Examples/Thms.lean) is a separate checked `EB 00` loaded-byte fixture, at entry zero and exit two under its declared state assumptions. It is not a certificate for `add3` or for ELF placement. |
| Source attribution | Three DWARF navigation links to exact C byte fragments; the extraction is unverified. No C CFG is assumed or built. |
| Cross-side correctness | The existing `add3` function-entry segment and conditional compilation refinement are separate questions in the Semantic view. They do not certify the DWARF links. |

When both sides have interpreted models, compare each admitted boundary and its observations
using a declared relation: specify inputs, exits, faults/divergence, observations, invariants and
placement assumptions, then ask for inclusion of corresponding behaviours, or inclusion both
ways for equivalence. The existing `Problem.Refines`, `SegmentDiscipline`, and semi-comorphism
specialization can express such a claim; `RelProblem.Refines` remains available without
execution. Region ↔ region is an optional later instantiation, not a prerequisite or a shipping
graph-equivalence feature. The proposed placement/fetch and first-return adapters in open
[#1070](https://github.com/hiloopai/silmaril-lean/pull/1070) are not dependencies. An end-to-end
bridge would need the exact ELF/load context, code-preservation and fetch/decode agreement,
CFG and exit coverage (including returns), and an explicit cross-side observation theorem.

## Fixtures and results

`tools/compiler-explorer/check.sh` (`make compiler-explorer-check`) writes the statuses and
compares them with `examples/compiler-explorer/expected-status.txt`:

| problem | translation | non-vacuity | ABI entry | mapping | links | location refinement |
| --- | --- | --- | --- | --- | --- | --- |
| `straight.c -O0 add3` | proved | proved | proved | proved | 5/5 | proved |
| `straight.c -O2 add3` | proved | proved | proved | proved | 1/1 | proved |
| `branch.c -O0 max2` | proved | proved | proved | proved | 5/5 | proved |
| `branch.c -O2 max2` | open | proved | proved | open | 0/1 | proved |
| `loop.c sum_to` | unsupported: the elaborator has no `while` | | | | | |
| `hello`, `msort`, `fft`, `lisp` | unsupported (execution tests against expected output: passed) | | | | debug info only | |
| `decompiled/scale` | unsupported; the `decompilation` obligation (block → C0) is proved | | | | the decompiled block | |
| `imported/sha256-compress` | unsupported | | | | none | |

The other obligations are proved for every row with statements: the C-to-Core points, the
elaboration, the binding of the function's bytes to the registered object, and the
canonical-entry row. Safety from every Core entry is open everywhere.

## Acceptance

| requirement | state |
| --- | --- |
| generic problem and segment relations, independent of determinism | done: `Problem`, `Mapping`, `SegmentDiscipline`; determinism is `Det` |
| comorphism-generated compilation and segment relations, separate refinement theorem | done on `SemiComorphism` (`Generator`, `Agrees`, `Witnessed`); `FnData.refines_dwarf` |
| refinement direction, UB, divergence, nondeterminism, concurrency | stated (above, `Defs`) |
| per-edge vs whole mapping, coverage, counterexample | done (`Det.Counterexample.edges_not_enough`) |
| non-vacuity | done for the C instance (`compilation_inhabited`) |
| CI | done: `make check` runs the database and view tests, and `compiler-explorer-check` when `cexplorer-export` or `CompilesToExamples` is in scope; a broken proof fails it |
| `sil project` | shapes, rows and database adapter; static fixture viewer and integration route are published on Pages; whole-corpus manifests/segment mappings remain incomplete |
| decompiled and imported directions | done, with fixtures; the decompiled block's machine → C0 obligation is proved (bound to the object's bytes by a tool check, to the C text by printing); no whole-function decompilation theorem |
| kernel replay | `leanchecker` on the evidence modules in `make compiler-explorer-check` (imports from `.olean`, same kernel) |
| syntax highlighting (C, assembly, Core) | done, as text tokens (tested for escaping) |
| jump to Lean source, explorer routes, artifact files | Lean definitions and evidence; exact C and ELF routes tested on generated site, public links after Pages deployment |
| toggle source / trusted stage output | checked artifact renderings; raw ELF, objdump and Lean decoder are distinct |
| short questions, hover and keyboard info | done |
| text-file and segment problems, stages, morphisms, optional semantics | relation and refinement API; receipt-only examples; observed include bytes materializable, no verified C preprocessor |
| C ⇒ C translations, equivalence | canonical outcome inclusion and equivalence stated; three translations disproved; reassociation and subtraction variant open |
| type error under a named judgment | exact source → operand types and rejection of the additive constraint, checked for the restricted grammar |
| DWARF → problem mapping | exact extract linked to its object and dependents; extractor itself unverified |
| nondeterministic segment discipline, concurrent target | not done |
| interactive compilation (choose compiler, flags, source; compile on demand) | not done: a remaining goal. It needs a sandboxed compile service (resource limits, no network, pinned images, receipts written by the service) with an API the database can trust; the repository has none, and this page must not run compilers itself |

## Build

```sh
tools/compiler-explorer/check.sh                 # or: make compiler-explorer-check
python3 -I tools/compiler-explorer/cexplorer.py serve .lake/compiler-explorer/explorer.sqlite
python3 -I tools/compiler-explorer/fixtures.py build|listings|decompile   # Docker (and Lean)
python3 -I tools/compiler-explorer/fixtures.py manifests|rows             # deterministic
```


## Kernel replay driver

`replay.sh` keeps the nine evidence targets and their descendants, discovers that
set once, then runs each selected module in an isolated process with at most four
workers (`LEAN_REPLAY_JOBS=1` selects serial execution). A discovery failure, empty
selection, missing module, kernel error, timeout or signalled worker fails the check.

The executable-only `tools/compiler-explorer/Replay.lean` calls the pinned
[LeanChecker.replayFromImports](https://github.com/leanprover/lean4/blob/67dafde474fbaf278d6d7f822068549bf6e532fa/src/LeanChecker.lean#L17)
operation directly. It uses the stock normal-mode target-prefix selection, search
path and kernel operation: declarations in each target are replayed from its loaded
imports; imported declarations are not themselves replayed (`--fresh` is a separate
stronger check). No import-only or cached-success path replaces kernel replay.
The driver intentionally omits `module` because the pinned `LeanChecker` is a legacy
module; this is an explicit compatibility exception for this leaf only, which no
library imports. No proof or axiom policy exception applies.

The stock CLI scans every installed olean for each target. The driver resolves those
paths once; workers call the same kernel operation without repeating discovery.
Separate processes also avoid the pinned multi-target CLI crash observed in CI.
`tests/test_replay.py` compares stock and driver selection and outcomes on positive,
unknown, corrupt and malformed-proof fixtures, including the normal-mode import
boundary. Scheduler tests cover bounded concurrency, discovery failure and worker
failure/signals. Run the equivalence checks with the pinned toolchain:

```sh
lake env python3 -I tools/compiler-explorer/tests/test_replay.py
```
