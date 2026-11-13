# Native-procedure and axiom trust in the project database

`sil project trust-dump` writes **trust lines** for a set of modules: the core trust framework's
policy, procedures, uses and per-theorem axioms. `sil project check|sqlite --trust PATH` checks
them and adds the trust tables to the project database. The explorer shows them in the
**Trust** tab.

The core framework is `Silmaril.Prelude.Trust` (#125, `docs/trust.md`). It owns the policy, the
procedures (`native_decider`), the trust sets, the profiles, `edge_decide`, `#trust_uses` and
`trust_audit`. This tool does not define a policy of its own. It stores the core's facts,
**recomputes** each module's effective sets with the core's rules (and fails when the producer's
differ), and applies the core's audit to every theorem.

## What a result means, and does not

- **No trust dump → unknown.** Without `--trust`, `meta.trust.status = absent` and use is
  *unaudited*. That is not a clean result.
- **Native means not kernel-only.** A theorem whose axioms include
  `<decl>._native.edge.<procedure>.ax_i_j` trusts the Lean compiler, the runtime and the compiled
  code the run reaches. A kernel run of the same procedure adds no axiom. The explorer shows,
  per module, how many theorems have native runs.
- **Report-only is not enforcement.** Without `--strict-trust`, violations are warnings and rows
  of `trust_violations`, and each run says `trust policy: NOT enforced (report only)`.
  `--strict-trust` (or `make project-trust-check TRUST=…`) fails, and writes no database, on:
  - any violation;
  - a covered module whose recorded digests are not all `consistent`;
  - an undescribed import under the roots;
  - a missing dump.
- **Passing is policy validation, not an audit of everything.** Every run prints
  `trust coverage: complete|partial` (also `meta.trust.coverage`). Explicit `excluded` or
  `unsupported` modules make it `partial`, and a strict pass then says `not a full audit`.
  Nothing is labelled fully audited or paranoid.
- **Digest consistency ≠ freshness.** `consistent` means that the recorded digests still match
  (module sources, described imports, inputs: `lean-toolchain`, `lake-manifest.json`,
  `policy.toml`), and nothing more.
- **Origin.** The header says `origin = lean` for a producer run and `fixture` for hand-written
  lines. The value is self-declared. The explorer flags anything that is not `lean`.

## The trust lines

The file has one JSON object per line. Every line carries a `schema` and a `kind`, and each
schema carries only certain kinds. The conversion to the database is explicit, per schema.
Unknown schemas, kinds and fields are rejected, so producer and tool upgrade **in lockstep**:
there is no forward compatibility.

- **`silmaril.trust.v1`** (the core's provenance schema, written by `#trust_dump`; see
  `docs/trust.md` in #125): `procedure`, `use`, `set` (with the core's `resolved`, checked against
  ours), `scope` (with `policy_file`, `policy_pin`), `declared_procedure` and `audit` (checked
  against the adapter's `decl` line).
- **`silmaril.trust-adapter.v0.1`** (what `sil project trust-dump` adds; also every line of a
  core before v1): `header`, `input`, `policy`, `set` (the policy file's sets, such as `standard`,
  which `#trust_dump` omits), `module`, `effective`, `decl`, `excluded`. With the legacy API it
  also carries `procedure`, `use`, `set` and `scope`.

| kind | from | fields |
|---|---|---|
| `header` | adapter | `core_api` (`v1`, `legacy`), `toolchain`, `profile`, `ceiling` (the audit's), `producer`, `origin`, `roots` |
| `input` | `trust-dump` | `path`, `sha256` (`lean-toolchain`, `lake-manifest.json`, `policy.toml`) |
| `policy` | adapter (`policyExt`) | `file`, `pin` (FNV-1a) |
| `scope` | core | `module`, `max`, `default`, `deps`, `axioms` (null inherits), `policy_file`, `policy_pin` |
| `set` | core / adapter | `name`, `all`, `members`, `includes`, `resolved` / `origin` |
| `procedure` | core | `name`, `function`, `kernel_fallback`, `module`, `format`, `sound`, `native_function`, `native_eq`, `doc` |
| `declared_procedure` | core | `name`, `constant`, `native` / `kernel` (`{check, sound}` or null), `format`, `doc` |
| `use` | core | `decl`, `module`, `procedure`, `mode`, `profile` (the elaboration's), `axiom` |
| `module` | adapter (`env.header`), `trust-dump` | `name`, `imports`, `source`, `source_sha256` |
| `effective` | adapter (`effective`, `allowed`) | `module`, `max`, `default`, `deps`, `axioms`, `allowed`, `trace` (or `error`) |
| `decl` | adapter (`axiomReport`) | `decl`, `module`, `own_native`, `dep_native`, `plain_native`, `axioms`, `native_axioms` |
| `audit` | core (`trust_audit`) | `decl`, `module`, `profile`, `own_native`, `dep_native`, `native_axioms`, `axioms` |
| `excluded` | `trust-dump --exclude M=REASON` | `module`, `coverage` (`excluded`, `unsupported`), `reason` |

### Checks (fail closed)

These are errors, and no database is written:

- **Lines:** a malformed line, a missing or extra header, a wrong schema, or a duplicate.
- **Uses:**
  - a use of an unknown procedure;
  - a native use of a procedure without a native side, or whose axiom is not a native run of
    that procedure.

A kernel run is never an error: it adds no axiom. Each kernel run records which kernel checker
it used (`kernel_side`):

- `fallback`: the kernel evaluates the native function;
- `declared`: the declared kernel checker of a `ProcDecl`;
- `unregistered`: a kernel checker that the registry does not name. This is the legacy
  `elf_leaf` of #127. The run is kernel-checked, but its identity cannot be audited.
- **Sets and scopes:**
  - an unknown or cyclic set include, or `all`/`none` redeclared;
  - an unknown set in a scope, or a duplicate scope;
  - a scope whose `max` exceeds its parent's.
- **Producer agreement:**
  - a set whose core `resolved` differs from ours, or a core `audit` line that differs from the
    adapter's `decl` line;
  - more than one policy file or pin;
  - a module without an `effective` line, or with sets that differ from the recomputed ones
    (`max`, `default` cut to `max`, `deps`, `axioms`, and `allowed` for the profile and ceiling);
  - a theorem whose `own_native`, `dep_native` or `plain_native` split differs from its native
    axiom names.

### The audit (as `trust_audit`)

Per theorem, in a covered module:

| class | rule | violation |
|---|---|---|
| `own_native` (`edge` axiom owned by the theorem) | procedure ∈ `allowed` | `own-native-not-allowed` |
| `dep_native` (inherited through another theorem) | procedure ∈ `deps` | `dep-native-outside-deps` |
| `plain_native` (`decide +native`, `bv_decide`) | never allowed | `unregistered-native` |
| `other` axiom | axiom ∈ `axioms` | `axiom-outside-set` |

Axioms come from `collectAxioms`, so they are already transitive: an inherited native run
appears as `dep_native` in every theorem that uses it. A theorem is audited against the
header's profile and ceiling (the artifact's), not against the profile it was elaborated under.
A theorem built under `local` that runs a procedure outside `default` is therefore a violation
in a `default` dump, and its `use` line still shows `local`.

**Dependency coverage.** Every theorem in a covered module is audited, with all its axioms,
including those inherited from modules outside the roots. A module outside the roots
(`external`) has no theorems or uses listed. An `excluded` module is described (imports,
digests) but its theorems are not audited, and coverage becomes `partial`.

## Tables and views (`silmaril.project-db.v0.2`)

| table | content |
|---|---|
| `trust_inputs` | recorded and current digests (`match`, `changed`, `missing`) |
| `trust_procedures` | `native_decider`s (function, `kernel_fallback`, separate native function and its equation, format checker) and declared procedures (native and kernel checker, each with its soundness theorem) |
| `trust_sets`, `trust_set_members` | sets (`builtin` `all`/`none`, `policy`, `trust_set`), members (`name`) and includes (`set`) |
| `trust_scopes` | `[[native.scope]]` rows (`NULL` inherits) |
| `trust_modules` | source digest and status, freshness, coverage (`covered`, `excluded`, `unsupported`, `undescribed`, `external`), policy trace |
| `trust_imports` | direct import edges |
| `trust_module_policy` | effective `max`, `default`, `deps`, `axioms`, `allowed` per module (`*` = all) |
| `trust_uses` | recorded runs (`edge_decide`, `edge_pair`, `sil_check`): mode, `kernel_side`, elaboration profile, native axiom |
| `trust_decls`, `trust_decl_axioms` | audited theorems and their axioms by class and procedure |

The views are:

- `trust_set_closure` (recursive) and `trust_module_deps` (recursive);
- `trust_coverage_gaps` (transitive imports that are not covered or external);
- `trust_module_native` (per module and procedure, theorems with own or inherited native runs);
- `trust_violations`.

`meta` gains these `trust.*` keys: `status`, `enforcement`, `coverage`, `schema`, `sha256`,
`producer`, `origin`, `toolchain`, `profile`, `ceiling`, `roots`, `policy_file` and
`policy_pin`. The database is regenerated, never migrated in place.

## The producer (`sil project trust-dump`)

```
sil project trust-dump --module M [--module …] [--root Silmaril] [--exclude M=REASON] [--core-api v1|legacy] [--no-build]
sil project sqlite --dump … --trust .lake/silmaril/trust.jsonl [--strict-trust]
```

The command works in four steps:

1. It writes `.lake/silmaril/TrustDump.lean`, which imports the modules.
2. It runs `lake build --wfail` and `lake env lean` on that file.
3. It completes the lines: the producer, the inputs, each module's source digest and the
   exclusions.
4. It appends the core's lines unchanged.

The driver for the core API is detected (`--core-api` overrides it):

- **v1** (#125 from `4ec6aa13`): the core's `#trust_dump`, plus an adapter. The adapter reads
  `policyExt`, `effective`, `allowed`, `axiomReport`, `hex64`, `profile`, `ceiling` and
  `Members`, which are not part of the core's declared stable interface.
- **legacy** (#125 at `28418c29`, which #127 merges): the driver also reads `procExt`, `setExt`,
  `useExt`, `allEntries`, `procJson` and `useJson`.

### Real producer output (origin `lean`)

Each case's README says how it was produced. The cases do not vendor the sources, so their
digests read `missing` and the modules `stale`.

| case | core / branch | targets | result |
|---|---|---|---|
| `trust-core-bytes` | #125 `91f7e0de` (v1) | `Prelude.Bytes.Examples`, `Data.IncludeBytes.KernelExamples`, `Prelude.Bytes.Checker.Thms` | 20 modules, 205 theorems, 5 uses (3 native), **0 violations**; `--strict-trust` passes in the build directory |
| `trust-core-profile-tests` | #125 `91f7e0de` (v1) | `Prelude.Trust.Examples` (profile tests) | **6 violations**: native runs under `local`, a named set, the paired and the declared forms, audited at `default` |
| `trust-elf-staged` | #127 `9ad00a40` (legacy) | `Elf.Staged.Example.Thms`, roots `Silmaril.Elf.Staged` | 10 modules, 102 theorems, 36 uses (1 native `elf.layout`, 35 kernel runs with an `unregistered` kernel side), **0 violations** |

#127's profile tests (`Elf.Staged.Example.Profiles`) give 2 violations (`loader_local`,
`main_local`) when they are dumped on their own. They are not committed.

### Fixtures (hand-written, origin `fixture`)

- `trust-fixture-elf`: ELF leaves with registered kernel fallbacks, a shape that neither #127
  nor #125 has. The real ELF data is `trust-elf-staged`.
- `trust-fixture-violations`: one violation of each class, and a stale source.
- `trust-fixture-invalid`: the fail-closed errors.
- `trust-strict-complete`, `trust-strict-partial`, `trust-strict-gaps`, `trust-strict-violations`:
  `--strict-trust`.

## Mapping from the earlier contract, and gaps

The earlier proposal (`silmaril.trust-dump.v0.1`, never produced by any tool) is replaced.

| earlier | core (#125) | here |
|---|---|---|
| procedure + implementations (backend, profile, checker, soundness, planned) | `native_decider name := fn [with_kernel_fallback]`: one function; native run or kernel fallback | `trust_procedures` with `kernel_fallback`. There is no `planned` status: an unregistered capability is absent. The soundness lemma is the caller's. |
| sets of `(procedure, backend, profile)` grants | sets of names (procedures or axioms), `includes`, `all`/`none` | `trust_sets`, `trust_set_members` |
| root / region / prefix / module scopes with `allow`, `max` | module-prefix scopes with `max`, `default`, `deps`, `axioms` | `trust_scopes`. There are no regions: `regions.toml` is not consulted. |
| `allow` bounds own and transitive uses | `allowed` (profile ∩ ceiling) bounds own native runs; `deps` bounds inherited ones (not bounded by `max`); `axioms` bounds other axioms | `trust_module_policy`, audit as above |
| uses with backend and axioms | `edge_decide` uses (mode, profile, axiom); axioms per theorem from `collectAxioms` | `trust_uses`, `trust_decl_axioms` |
| `decls` optional | `axiomReport` per theorem | always present from the driver |

These gaps and hooks were reported to the core:

1. **A richer stable dump.** `#trust_dump` covers procedures, declared procedures, uses,
   `trust_set`s and scopes. The adapter still reads internals for the header (toolchain,
   profile, ceiling), the policy file's own sets (`standard`, which `#trust_dump` omits), module
   imports, effective sets and per-theorem axiom reports. A stable hook for these would remove
   the adapter.
2. **Audit profile vs elaboration profile.** Both are recorded: the use's `profile` and the
   header's audit `profile`/`ceiling`. Violations are judged at the audit profile, deliberately.
3. **Procedure identity.** `edge_decide` binds a procedure by the goal's head function. Each
   leaf needs its own named closed wrapper. Head identity alone must not grant arbitrary nested
   native computation inside the arguments.
4. **Legacy ELF kernel runs.** The legacy `elf_leaf` records kernel runs under procedures without
   a registered kernel side (`kernel_side = unregistered`). Moving #127 to `ProcDecl`/`sil_check`
   on the v1 core would register them.
5. **`deps` is not bounded by `max`.** At the root, `deps = all`, so a module may inherit any
   native procedure through imported theorems, even one outside its own `max`. This is a
   **potential design hole**, relayed to the core: bound `deps` by an inherited dependency
   maximum, or document a separate dependency ceiling. The database reproduces the current rule
   and does not call it intended.
6. **Exclusions.** The core's `scripts/trust-profile-exclude.txt` covers profile builds, not
   audits. Audit exclusions are given explicitly (`--exclude M=REASON`) and make coverage
   partial.
