# AGENTS.md

Working rules for agents in silmaril-lean. The design is in [docs/design.md](docs/design.md).

## Where work happens
- **Keep the library reviewable.** Exploratory work, agent traces, research notes
  and paper assets stay outside this repository. Public scholarly citations and
  exact artifact hashes belong here; bundled papers do not.
- **This repository gets reviewed promotions.** Clean, reusable developments
  arrive as pull requests, each with a reviewable scope.
- Each contribution must be self-contained: public dependencies, build commands
  and references, with no private repository links or migration records.

## Layout and imports
- **Headers:** `Silmaril/<Region>/<Topic>/Defs.lean` and `Thms.lean`.
  - Keep definitions and statements readable: these files are what people audit.
  - Proofs of at most about three lines may stay inline.
  - Longer proofs go to `Silmaril/Proofs/<Region>/<Topic>/…`. The header restates
    the theorem and points at that proof (`theorem foo : stmt := Proofs.….foo`),
    imported with a plain (non-`public`) import.
- **Raw:** `Silmaril/Raw/…` holds valid but unrefined proofs. Only the same
  topic's `Proofs` and `Thms` may import it. It is never an API.
- **No reaching into other topics' internals:** never import another topic's
  `Proofs` or `Raw` modules; use its `Thms` header.
- **Regions:** a region imports only the regions listed in its `deps` in
  [regions.toml](regions.toml). Change that file deliberately, in its own commit.
- **Views** (`Papers`, `Standards`, `Thesis`) re-export or restate, contain no
  non-trivial proofs, and are imported by nothing.
- **Courses** are self-contained leaf views: their proofs may stay inline when
  that helps readers follow the course. No library region imports `Courses`.
- Use the module system (`module`, `public import`) everywhere.

## Executables and existing implementation modules
- One root Lake project builds the library and tools. Shared compiler, semantics,
  numeric and codec APIs belong in `Silmaril/`; executable drivers belong in
  `tools/`. `sil` groups commands by project and preserves standalone tool names.
- The included Wasm and logic proof closures retain their implementation module names.
  Lambda calculi use the `Calculi` region; their retained implementation modules are
  being refined into headers and proof modules incrementally. This
  is an explicit exception to the header layout and intended region map above;
  it does not assert that the existing imports already satisfy that map. Refine
  public headers in small reviewed changes, preserving functionality and theorem
  assumptions rather than renaming the whole closure at once.
- Runtime and proof entry points are in `tools/binaryen-lean/release-manifest.json`.
  Keep proof imports out of executable runtime closures. Document pure-function
  contracts, guards, profiles and observation models.
- Run `make check` for the library, native tools, proof roots and regressions.
  A library-only build does not exercise the executable tests.

## Main stays strict
- **Nothing incomplete on main:** no `sorry`, no new `axiom`, and no warnings
  (CI builds with `--wfail`).
- **Axioms:** only `propext`, `Classical.choice` and `Quot.sound`, unless
  [policy.toml](policy.toml) lists an exception with a reason. `native_decide` is
  not allowed.
- **Open goals on branches:** use `sorry`'d theorems in a `Task` namespace. Before
  merging, prove them, or turn them into `def Task.x : Prop := …` with the
  theorem stated conditionally (`theorem foo_of (h : Task.x) : …`).

## Pull requests
- **Open them as drafts** (`gh pr create --draft`), then mark them ready
  (`gh pr ready`) when they are reviewable. Do one cheap targeted build of the
  touched modules first; CI runs the full build.
- **Report checks accurately:** say which passed, which are pending and which
  failed. Never imply something compiled without building it.
- **Toolchain:** follow the Lean, Mathlib and CSLib versions CSLib uses. Pin
  dependencies by exact SHA, and make bumps separate pull requests.
