# Design

Silmaril is a reusable Lean library, organized around independently reviewable
formalization topics. Every released topic should include its definitions,
theorems, dependencies, scholarly sources and instructions for checking it.
Exploratory notes, paper assets and agent traces are outside the library.

One root Lake project builds the shared library and its executables. The
[Wasm toolkit](projects/wasm.md) is the first tool family; the
[project index](projects/README.md) distinguishes shipped code from future ports.
Policies below describe the intended library shape, not evidence that every
proposed API or automated check has shipped.

## Library and tools

- `Silmaril/`: language models, shared compiler machinery, codecs and proofs.
- `tools/`: thin executable drivers and native integration checks.
- `scripts/sil`: the tool-family dispatcher, staged as `build/bin/sil`.
- `docs/projects/`: a guide to each major development and its contracts.
- `build/bin/`: generated standalone commands and the dispatcher.

The included Wasm development retains its implementation namespaces as a
reviewed exception to the header and region layout below. Reusable APIs are
factored into definitions, theorem statements and proof modules incrementally.
This preserves executable behavior and theorem assumptions while reducing what
an API reader must review. The root build checks every included library module.

Lake owns the Lean dependency graph and native compilation. A thin Makefile
stages binaries and invokes release checks. Another build system can orchestrate
Lake later if non-Lean components justify it; the first release has one build
graph and one dependency lockfile.

## The square

Each repository has the same three layers. Imports run upward:

```
headers (Defs, Thms)  ←  Proofs  ←  Raw
```

- **Headers** are what a person audits: definitions, and the statements of the
  theorems we claim. They live at `Silmaril/<Region>/<Topic>/Defs.lean` and
  `Thms.lean`.
  - Splitting definitions from statements is forced by the import direction:
    proofs need the definitions, and the theorem headers need the proofs.
  - A `Thms` header restates each theorem and points at its proof, which it
    imports with a plain (non-`public`) import. In the module system, theorem
    bodies and non-public imports are not part of a module's interface, so
    downstream modules see only the statements. Proof changes also do not
    rebuild them.
  - A statement that is only definitionally equal to the proof's type is fine:
    the header's declared type is what the kernel checks.
- **Proofs** are good, non-trivial proofs. They are semi-stable, and only reached
  through the headers.
- **Raw** is agent output: valid but unrefined, and never an API. Refining moves a
  proof down to `Proofs`; the raw version is deleted or kept as a reference.
- Proofs of about three lines or fewer stay inline in headers. A separate
  `Proofs` declaration is for real work.

**Rules.** No module imports another topic's `Proofs` or `Raw`. A region imports
only the regions in its `deps` ([`regions.toml`](../regions.toml)). Views are
leaves. CI builds with warnings as errors and runs `scripts/check-layout.sh`, which
checks some textual layout restrictions. It does not yet enforce the full region
DAG, every same-topic restriction, or transitive axiom policy. Review those
properties explicitly until their checks are implemented.

## Regions

Regions are the core subprojects, small enough that an agent working on one
needs only that region's files plus the headers of the regions it depends on.
The intended region map and dependencies are recorded in `regions.toml`:

```
Prelude
└ Semantics
  ├ Logic ─ Computability
  ├ Numeric ─ Science
  │ └ Crypto ─ Formats
  └ SSA (Semantics, Logic)
    ├ Calculi (+ Formats)
    ├ GPU (+ Numeric) ─ Languages (+ Formats)
    └ Machine (+ Numeric, Crypto, Formats)
      └ Wasm (+ Logic)
```

**Initial implementation order:**
1. A small shared transformation-contract API with a worked client. Keep total,
   invariant-preserving optimizations distinct from partial heterogeneous compiler
   passes, and prove adapters where their semantic obligations agree.
2. Refine the Wasm toolkit's shared interfaces: reproducible fixtures, exact
   theorem assumptions, and separate executable and proof-root build instructions
   accompany its current package. Broader input and optimization coverage remain
   explicit development targets.
3. Expand the semantic and compiler interfaces, SSA and Elgot developments, logics,
   instruction sets and other topics through small reviewed additions.

Each topic is cleaned, cited and deduplicated while it is added. Research and
library development may proceed in parallel; a broad source freeze is not needed.
Compatibility scaffolding and migration records are not part of the library.

## Views

Views re-export or restate. They hold no non-trivial proofs, and nothing imports
them.

- **`Papers/<Key>/`**:
  - `Defs.lean`: the paper's definitions, re-exported, or stated in the paper's
    own form when they originate there;
  - `Relations.lean`: how those definitions relate to the general library
    versions;
  - `Thms.lean`: the paper's results under its numbering, each restated and
    pointing at the library proof.
- **`Standards/<Key>/`**: the same, for RFCs, ISA manuals and the Wasm
  specification.
- **`Thesis/<Chapter>/`**: imbrem/thesis, following the text as it is written. The
  thesis repository will eventually depend on this one.

The same theorem may be re-exported from several views; that is the point.

## Proof obligations and policy (stage 0)

Everything here is a convention, with no new Lean metaprogramming. Each later
stage only automates what the previous one does by hand.

- **Main is strict:**
  - no `sorry`, no new `axiom`, and no warnings;
  - axioms limited to the standard three, plus the exceptions in
    [`policy.toml`](../policy.toml).
- **Open goals on branches** are `sorry`'d theorems in a `Task` namespace. The
  *proof front* of a theorem is the set of `Task.*` declarations it depends on.
- **Before merging,** each `Task.x` is either proved, or *frozen*: it becomes
  `def Task.x : Prop := …`, and every theorem that used it is restated as
  `theorem foo_of (h : Task.x) : …`. Freezing is the deduction theorem: a proof
  that assumed `Task.x` becomes a theorem with `Task.x` as a hypothesis.

**Later stages:**
1. Script freeze and unfreeze.
2. A `task` tactic that turns the current goal into a standalone `Task`
   statement.
3. `@[proves X]` lookup, so headers find their proofs, and policy attributes in
   the source.

## Data

[`data/`](../data/README.md): JSON and CSV dumps with source manifests. These
are processed in Rust on covalence; SQLite is a build output.

## Citations and claims

Cite public scholarly sources using author, title, version, stable URL or DOI,
exact artifact SHA-256, and relevant section/theorem/page locators. The hash
identifies the artifact variant; a converted PDF and its original PostScript
must not be presented as the same bytes. Do not distribute papers or include
private acquisition paths, catalogues or provenance records.

State what the theorem establishes, including invariants, host/profile policies,
resource assumptions and supported observations. Mark planned results as plans.
A tested fixture is not a general correctness theorem, and building an executable
does not check a separately imported proof root.

## Tooling and release gates

The implemented checks are the Lake build and the textual layout script. Full
region-dependency enforcement, transitive axiom auditing and independent checker
exports remain planned tooling. Do not describe those policies as already
automatically enforced.

Each substantial example needs a reproducible clone/build recipe, a guide to its
main definitions and theorems, and accurately reported checks. Publish draft PRs
early; make them ready for CI once their scope is reviewable. Release only after
the required checks pass. Code and documentation must be understandable and
verifiable using this repository and its public dependencies.
