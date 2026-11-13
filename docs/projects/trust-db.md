# Native-procedure and axiom trust in the project database

`sil project trust-dump` writes **trust lines** for a set of modules. They hold the core trust
framework's registry, policy, uses and per-declaration audits. `sil project check|sqlite
--trust PATH` checks the lines and adds the trust tables to the project database. The explorer
shows them in the **Trust** tab.

The core framework is `Silmaril.Prelude.Trust` (#125, `docs/trust.md`). It owns the policy, the
procedures (`native_decider`, `native_tactic`, `ProcDecl`), the trust sets, the profiles,
`edge_decide`/`edge_pair`/`sil_check`, and the audit (`auditLine`, `trust_audit`). This tool
does not define a policy of its own. It does three things:

- it stores the core's lines;
- it **recomputes** each module's effective sets, each set's resolution and each declaration's
  violations, and fails when they differ from the core's;
- it reports coverage, digests and enforcement honestly.

Refs used: core #125 at `3c731fc1`, ELF #127 at `449a063e` (which merges #125 at `3c731fc1`).

## What a result means, and does not

- **No trust dump → unknown.** Without `--trust`, `meta.trust.status = absent`: unaudited, not
  clean.
- **Native means not kernel-only.** A declaration whose axioms include a native run
  (`<decl>._native.edge.<procedure>.ax_i_j`, or a registered native tactic's
  `<decl>._native.<tag>.ax_n`) trusts the Lean compiler, the runtime and the code the run
  reaches. The registered checker's own dependencies are part of that code: a review of the
  checker covers its closure. Registration names the procedure. It does **not** by itself
  prevent arbitrary nested computation, and it is not proof against a malicious metaprogram.
  Uses are recorded by instrumentation (`recordUse`) that is itself trusted and reviewed. The
  core verifies a native axiom only if a recorded use produced exactly that axiom and the axiom
  mentions the procedure's evaluated function; otherwise the axiom is `unverified_native`. An
  LRAT/`bv_decide` registration needs the exact statement.
- **Report-only is not enforcement.** Without `--strict-trust`, violations are warnings and rows
  of `trust_violations`, and each run says `trust policy: NOT enforced (report only)`.
  `--strict-trust` (or `make project-trust-check TRUST=…`) fails, and writes no database, on:
  - any violation;
  - a covered module whose recorded digests are not all `consistent`;
  - an undescribed import under the roots;
  - a missing dump.
- **Passing is policy validation, not an audit of everything.** Every run prints `trust
  coverage: complete|partial` (also in `meta.trust.coverage`). `excluded` or `unsupported`
  modules make it `partial`, and a strict pass then says `not a full audit`. Nothing is labelled
  fully audited or paranoid.
- **Digest consistency ≠ freshness.** `consistent` means only that the recorded digests still
  match (module sources, described imports, `lean-toolchain`, `lake-manifest.json`,
  `policy.toml`).
- **Origin.** The header says `origin = lean` for a producer run and `fixture` for hand-written
  lines. The value is self-declared. The explorer flags anything that is not `lean`, and a test
  checks every case's origin.

## The trust lines

The file has one JSON object per line, each with a `schema` and a `kind`. Each schema may carry
only its own kinds, and each line is converted explicitly into the strict database schema:

- **Unknown schemas and kinds** are rejected.
- **Core fields:** the core may add fields within `silmaril.trust.v1`. A field outside
  `CORE_FIELDS` is dropped and recorded in `meta.trust.ignored_core_fields`, never given a
  meaning. It is a warning in report-only mode and an **error** under `--strict-trust`.
- **Adapter fields:** they must all be known, so `trust-dump` and the reader upgrade together.

**`silmaril.trust.v1`** (the core's; `docs/trust.md`):

| kind | fields | stored as |
|---|---|---|
| `procedure` | `name`, `function`, `kernel_fallback`, `module`, `format`, `sound`, `native_function`, `native_eq`, `axiom_pattern`, `components`, `toolchain`, `fallback_coverage`, `doc` | `trust_procedures` (`native_decider`, or `native_tactic` when `axiom_pattern` is set) |
| `declared_procedure` | `name`, `constant`, `native`, `kernel` (`{check, sound}` or null), `format`, `doc` | `trust_procedures` (`declared`) |
| `use` | `decl`, `module`, `procedure`, `mode`, `profile` (the elaboration's), `axiom` | `trust_uses` (with `kernel_side`) |
| `set` | `name`, `all`, `members`, `includes`, `resolved` | `trust_sets`, `trust_set_members`; `resolved` is checked |
| `scope` | `module`, `max`, `default`, `deps`, `axioms`, `policy_file`, `policy_pin` | `trust_scopes`; one file and pin is required |
| `module` | `module`, `imports`, `profile`, `ceiling`, `max`, `default`, `deps`, `axioms`, `allowed`, `scopes` (or `policy_error`) | `trust_modules`, `trust_imports`, `trust_module_policy`; the sets are checked |
| `audit` | `decl`, `module`, `profile`, `own_native`, `dep_native`, `unverified_native`, `native_axioms`, `axioms`, `elaborated_profiles`, `violations` | `trust_decls`, `trust_decl_axioms`, `trust_audit_messages`; the split and the count of violations are checked |

**`silmaril.trust-adapter.v0.2`** (added by `trust-dump`):

| kind | fields |
|---|---|
| `header` | `core_api` (`v1-hooks`), `toolchain`, `producer`, `origin`, `roots` (and optionally `profile`, `ceiling`) |
| `input` | `path`, `sha256` |
| `source` | `module`, `path`, `sha256` |
| `set` | the policy file's own sets (`standard`), which the core's lines omit; `origin = policy` |
| `excluded` | `module`, `coverage` (`excluded`, `unsupported`), `reason` (from `--exclude M=REASON`) |

### Checks (fail closed)

These are errors, and no database is written:

- **Lines:** a malformed line, a missing or extra header, an unsupported schema or kind, a
  duplicate, or more than one policy file or pin.
- **Uses and audits:**
  - a use of an unknown procedure;
  - a native use of a procedure without a native side, or whose axiom is not a native run of
    that procedure;
  - an audit outside a described module, or two different audits of one declaration (identical
    repeats of realized constants are merged and counted).
- **Sets and scopes:**
  - an unknown or cyclic set include, or `all`/`none` redeclared;
  - an unknown set in a scope, or a duplicate scope;
  - a scope above its parent's `max`.
- **Producer agreement:**
  - effective sets (`max`, `default` cut to `max`, `deps`, `axioms`, and `allowed` for the
    profile and ceiling) that differ from the recomputed ones;
  - a set `resolved` that differs;
  - an `own_native`/`dep_native` split that differs from the native axiom names;
  - a core violation count that differs from the recomputed one for some declaration.

A kernel run is never an error, because it adds no axiom. Its `kernel_side` records which kernel
checker ran:

- `fallback`: the kernel evaluates the native function;
- `declared`: the `ProcDecl`'s kernel checker;
- `unregistered`: a checker the registry does not name. None occur at the refs above.

### Verified native runs

A native axiom's name (`._native.edge.<p>.`) or a native tactic's tag (`axiom_pattern`) only
**classifies** the axiom. The tool counts it as a run of `p` only if a recorded native `use` of
`p` produced exactly that axiom. Otherwise the axiom is `unverified_native`, and if the core's
audit called it verified, the dump is refused. The tool cannot see axiom statements. It relies
on the core for the other half of verification: that the statement mentions the evaluated
function (`verifiedNative`). It never trusts a regex, a tag or registry metadata alone. Binding
`bv_decide` to the real checked `verifyBVExpr` statement is the core's and the LRAT work's job.

### The audit (as the core's `auditLine`)

Every declaration is judged at the dump's profile and ceiling, that is, the artifact's. A
declaration elaborated under `local` that ran a procedure outside `default` is a violation in a
`default` dump. Its `elaborated_profiles` still show `local`.

| class | rule | violation |
|---|---|---|
| `own_native` (verified, owned by the declaration) | procedure ∈ `allowed` | `own-native-not-allowed` |
| `dep_native` (verified, inherited) | procedure ∈ `deps` | `dep-native-outside-deps` |
| `unverified_native` (name or tag match only) | never | `unverified-native` |
| `plain_native` (unregistered `decide +native`, `bv_decide`, …) | never | `unregistered-native` |
| `other` axiom | axiom ∈ `axioms` | `axiom-outside-set` |

**Dependency audit coverage.** Every theorem and definition of a covered module is audited with
all its axioms (`collectAxioms`, transitive). Native runs inherited from modules outside the
roots are therefore audited too, as `dep_native`. A definition exported without its body is
opaque to importers and contributes no axioms. Modules outside the roots (`external`) have no
uses or declarations listed. An `excluded` module is described (imports, digests) but its
declarations are not audited, and coverage becomes `partial`.

## Tables and views (`silmaril.project-db.v0.2`)

| table | content |
|---|---|
| `trust_inputs` | recorded and current digests |
| `trust_procedures` | `native_decider`, `native_tactic` and `declared` procedures with their checkers, soundness theorems, native function and equation, axiom pattern, components, toolchain and fallback coverage |
| `trust_sets`, `trust_set_members` | sets (`builtin` `all`/`none`, `policy`, `trust_set`), member names and includes |
| `trust_scopes` | `[[native.scope]]` rows (`NULL` inherits) |
| `trust_modules` | source digest and status, freshness, coverage (`covered`, `excluded`, `unsupported`, `undescribed`, `external`), scope chain |
| `trust_imports` | direct import edges |
| `trust_module_policy` | effective `max`, `default`, `deps`, `axioms`, `allowed` (`*` = all) |
| `trust_uses` | recorded runs: mode, `kernel_side`, elaboration profile, native axiom |
| `trust_decls`, `trust_decl_axioms`, `trust_audit_messages` | audited declarations (audit profile, elaboration profiles), axioms by class and procedure, the core's messages verbatim |

The views are:

- `trust_set_closure` and `trust_module_deps` (both recursive);
- `trust_coverage_gaps`;
- `trust_module_native` (own, inherited, unverified and plain native runs per module and
  procedure);
- `trust_violations`.

`meta` gains these `trust.*` keys: `status`, `enforcement`, `coverage`, `core_api`, `sha256`,
`producer`, `origin`, `toolchain`, `profile`, `ceiling`, `roots`, `policy_file` and
`policy_pin`. The database is regenerated, never migrated in place.

## The producer (`sil project trust-dump`)

```
sil project trust-dump --module M [--module …] [--root Silmaril] [--exclude M=REASON] [--no-build]
sil project sqlite --dump … --trust .lake/silmaril/trust.jsonl [--strict-trust]
```

The command works in four steps:

1. It writes `.lake/silmaril/TrustDump.lean` (`tools/silmaril-project/src/project/trust/Driver.lean`).
   The driver calls the core's stable hooks (`dumpLines`, `allDecls'`, and `moduleLine` and
   `auditLine` over `declsOf`) for every module under the roots. That is what `#trust_dump path
   M₁ …` does, but with the module list computed.
2. It runs `lake build --wfail` and `lake env lean` on the driver.
3. It adds the adapter lines: the header, inputs, sources, exclusions and the policy file's
   sets. Only the policy file's sets need a non-stable read (`policyExt`).
4. It appends the core lines unchanged.

It requires #125 at `ba1b5f84` or later (`moduleLine`, `auditLine`).

### Real producer output (origin `lean`)

Each case's README gives its commit and command. The cases do not vendor the sources, so their
digests read `missing` and the modules `stale`.

| case | ref | targets | result |
|---|---|---|---|
| `trust-core-bytes` | #125 `3c731fc1` | `Prelude.Bytes.Examples`, `Data.IncludeBytes.KernelExamples`, `Data.IncludeBytes.KernelImportExamples`, `Prelude.Bytes.Checker.Thms` | 21 modules, 551 declarations, 5 uses (3 native), **0 violations**; strict passes in the build package |
| `trust-core-profile-tests` | #125 `3c731fc1` | `Prelude.Trust.Examples` | **7 violations** (6 native runs outside `default`, 1 unverified native axiom), as the core's audit lists them |
| `trust-elf-staged` | #127 `449a063e` | `Elf.Staged.Example.Thms`, roots `Silmaril.Elf.Staged` | 12 procedures, 299 declarations, 36 uses (1 native `elf.layout`, 35 kernel runs of declared kernel sides), **0 violations** |
| `trust-elf-profile-tests` | #127 `449a063e` | `Elf.Staged.Example.Profiles` | **2 violations** (`loader_local`, `main_local`), as expected |

`trust-elf-excluded` is the same #127 checkout, dumped with both example modules and
`--exclude Silmaril.Elf.Staged.Example.Profiles=…`. It has 299 declarations audited, 8 listed
but not audited, 0 violations, and **partial** coverage.

### Strict validation (in the build checkouts, with sources and inputs present)

| dump | `--strict-trust` |
|---|---|
| bytes normal targets (#125 `3c731fc1`) | **passes**; complete coverage, 21 modules with consistent digests |
| bytes and `Prelude.Trust.Examples` with `--exclude` | **passes**; partial coverage, "not a full audit" |
| `Prelude.Trust.Examples` | **fails**: 7 violations |
| ELF `Example.Thms` (#127 `449a063e`) | **passes**; complete coverage, 10 modules with consistent digests |
| ELF and `Example.Profiles` with `--exclude` | **passes**; partial coverage, "not a full audit" |
| ELF `Example.Profiles` | **fails**: 2 violations |

In this repository the committed cases do not vendor their sources, so a strict run on them
fails on digests. That is the intended behaviour.

### Fixtures (hand-written, origin `fixture`)

- `trust-fixture-elf`: ELF leaves with kernel fallbacks, a shape the real #127 does not have
  (it declares its kernel sides).
- `trust-fixture-violations`: one violation of each class, and a stale source.
- `trust-fixture-invalid`: the fail-closed errors.
- `trust-strict-complete`, `trust-strict-partial`, `trust-strict-gaps`, `trust-strict-violations`:
  `--strict-trust`.

## Remaining gaps

1. **The policy file's sets** (`standard`) are not in the core's lines. The adapter reads them
   from `policyExt`.
2. **`declsOf` repeats realized constants** (`eq_def`, `match_1.congr_eq_*`) in every module that
   realizes them. The repeats are merged here when identical.
3. **Root `deps = all`.** Child scopes cannot escalate `deps` or `axioms` (#125 `ba1b5f84`). The
   root still accepts any inherited native procedure: a broad dependency envelope, separate from
   `max`. The database shows the actual `deps` of every module. It does not present the envelope
   as bounded.
4. **Trust in the instrumentation.** Recorded uses and a constant occurring in an axiom's
   statement do not defend against a malicious metaprogram. The guarantee rests on reviewed
   instrumentation and reviewed checker closures, and an LRAT registration needs the exact
   statement.
5. **No CI producer run.** The Rust CI job has no Lean, so the real cases are regenerated by
   hand (see their READMEs) and checked as goldens.
