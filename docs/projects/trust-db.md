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

Refs used: core #125 at its head `cbcd896c` (which includes the frozen export `792e7ed6` and the
exact-head audit `0b2a82e0`), and ELF #127 at its head
`67503c32` (which merges `34ec436e`).

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

## Canonical format

The project database has **one** input: the core's frozen trust export,
**`silmaril.trust-core.v1`**. It is one JSON document, written by `#trust_export`
(`Silmaril.Prelude.Trust.Export`), either through `sil project trust-dump` or through the core's
`scripts/trust-export.sh`. The database owns the converter (`trust::core_doc`), which is
explicit:

- **Unknown fields are an error**, because the shape is frozen.
- **Every field is mapped:**

| export | database |
|---|---|
| `toolchain`, `producer` (`tool`, `profile`, `ceiling`, `main_module`) | `meta.trust.*`; the audit's profile and ceiling. The origin is `lean` when `tool` is the core's exporter, else `fixture`. |
| `inputs` (`policy`, `regions`, `lean-toolchain`, exclusions SHA-256, `policy_pin`) | `trust_inputs`, compared with the files present; every policy's `origin.pin` must equal `policy_pin` |
| `procedures`: `decider` (native backend, optional paired `function`/`equation`, kernel backend iff fallback), `tactic` (`evaluated_constant`, `axiom_pattern`, `components`, `toolchain`, `fallback_coverage`), `declared` (`constant`, native/kernel `{check, sound}`), `named` (`implemented: false`) | `trust_procedures` (`native_decider`, `native_tactic`, `declared`, `named` with `implemented = 0`) |
| `sets` (`all`, `members` `{kind: procedure \| set, name}`, `doc`) | `trust_sets`, `trust_set_members` |
| `unresolved` (`{set, name}`) | must equal exactly the set members that name a `named` procedure; such members are never granted |
| `policies` (`scope` `root` / `region` / `module-prefix`, `name`, `allow` = the `default` set, `max`, `deps`, `axioms`, each `[set]` or null, `origin`) | `trust_scopes`; a list of more than one set is an error |
| `modules` (`name`, `region`, `source`, `source_sha256`, `imports`) | `trust_modules`, `trust_imports` |
| `uses` (`backend`, `profile`, `axiom`, `verified`) | `trust_uses`; a native use with `verified = false`, or whose axiom is not a native run of its procedure, is kept with `axiom_matches = 0`, flagged, never authorizing |
| `declarations` (`axioms`, `native_axioms`, `own_native`, `dep_native`, `unverified_native`, `violations`) | `trust_decls`, `trust_decl_axioms`, `trust_audit_messages`; for every declaration, the recomputed violations must be the export's, as normalized (category, subject) identities with multiplicity |
| `excluded` (`module`, `coverage`, `profile`, `reason`) | `excluded` coverage with its reason |

The export omits two things, and the converter handles each explicitly:

- **The policy file's own sets** (`standard`). They are read from `policy.toml` **only if** its
  SHA-256 equals `inputs.policy_toml_sha256`; otherwise the run fails.
- **Effective sets per module.** They are recomputed with the core's rules (`max` within the
  parent's, `default` cut to `max`, and so on). They are checked through the per-declaration
  violation identities above.

**Policy model, unchanged from the core.** The four policy roles stay distinct. `allowed` (the
profile's set within `max`) bounds a declaration's own native runs; `deps` bounds the native
runs it inherits; `axioms` bounds its other axioms; `max` bounds children. Nothing is collapsed
into one "allow" applied transitively, and no equivalence to such a policy is claimed. Scopes
keep the export's kind (`root`, `region`, `module-prefix`). Their order is deterministic: a
scope applies to its module and everything under it, scopes are applied outermost first by
name depth, and two scopes for one module are an error.

**Uses.** The core records a use's profile as one tag: `profile`, or `profile≤ceiling` when a
ceiling other than `local` was in force. The converter splits it into `trust_uses.profile` and
`trust_uses.ceiling`. The audit's own profile and ceiling are `meta.trust.profile` and
`meta.trust.ceiling`.

**Soundness references** are the export's: a decider's or tactic's `sound`, and a declared
procedure's `{check, sound}` pairs. None is invented. A procedure without a registered
soundness theorem (`bytes.wf`, or a native tactic without one in its wrapper's registration) has
none.

**Future optional fields.** The shape is frozen, and unknown fields are an error. If the core
adds provenance fields (for example per-use provenance, or inherited axioms as
`{axiom, procedure, from_decl}`), the converter will read them in a new, explicitly versioned
mapping. They will not be accepted silently.

**Coverage.** A module that has no declaration in the export is `unaudited`: either it was not
listed for audit (`trust-dump --root`/`--exclude`), or it declares no theorem or definition. The
export does not record which modules were listed, so this is conservative and makes coverage
partial.

**Refused by name, never reinterpreted:**

- the earlier JSON-lines input (`silmaril.trust.v1` lines with `silmaril.trust-adapter.v0.2`),
  now retired. The test case `trust-lines-rejected` holds real lines that are refused;
- `silmaril.trust-dump.v0.1`, a proposal no producer wrote;
- any other schema.

### Checks (fail closed)

These are errors, and no database is written:

- **Document:** anything but a `silmaril.trust-core.v1` document of the frozen shape, a
  duplicate, a policy pin other than `inputs.policy_pin`, an unreadable `policy.toml` or one
  whose digest differs, or `unresolved` members other than those of `named` procedures.
- **Uses and audits:**
  - a use of an unknown procedure, or of a `named` (unimplemented) procedure;
  - a native use of a procedure without a native side;
  - a declaration outside a described module, or two different audits of one declaration
    (repeats of realized constants that differ only in the listing module are merged and
    counted).
- **Sets and scopes:**
  - an unknown or cyclic set include, or `all`/`none` redeclared;
  - an unknown set in a scope, or a duplicate scope;
  - a scope above its parent's `max`.
- **Producer agreement:**
  - an `own_native`/`dep_native` split that differs from the native axiom names;
  - a declaration whose recomputed violations differ from the core's, compared as normalized
    (category, subject) identities with multiplicity (`own-native-not-allowed` and the procedure,
    `axiom-outside-set` and the axiom, and so on); a core message of no known form is itself an
    error. This compares what the two audits conclude, not that they reason alike: agreement is
    not a proof of semantic equivalence.

A native use the core did not verify (`verified = false`), or whose axiom is not a native run of
its procedure, is not an error of the document. It is kept with `axiom_matches = 0`, reported,
and authorizes nothing. It is an error under `--strict-trust` unless its module is not audited.

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
`default` dump. The use's `profile` still shows `local`.

| class | rule | violation |
|---|---|---|
| `own_native` (verified, owned by the declaration) | procedure ∈ `allowed` | `own-native-not-allowed` |
| `dep_native` (verified, inherited) | procedure ∈ `deps` | `dep-native-outside-deps` |
| `unverified_native` (name or tag match only) | never | `unverified-native` |
| `plain_native` (unregistered `decide +native`, `bv_decide`, …) | never | `unregistered-native` |
| `other` axiom | axiom ∈ `axioms` | `axiom-outside-set` |

**Dependency audit coverage.** Every theorem and definition of a covered module is audited with
all its axioms (`collectAxioms`, transitive). Native runs inherited from modules outside the
audit are therefore audited too, as `dep_native`. A definition exported without its body is
opaque to importers and contributes no axioms. Modules outside `Silmaril` are `external`. An
`unaudited` or `excluded` module is described (imports, digests) but its declarations are not
audited, and coverage becomes `partial`.

## Tables and views (`silmaril.project-db.v0.2`)

| table | content |
|---|---|
| `trust_inputs` | recorded and current digests |
| `trust_procedures` | `native_decider`, `native_tactic`, `declared` and `named` (`implemented = 0`) procedures with their checkers, soundness theorems, native function and equation, axiom pattern, components, toolchain and fallback coverage |
| `trust_sets`, `trust_set_members` | sets (`builtin` `all`/`none`, `policy`, `trust_set`), member names and includes |
| `trust_scopes` | `[[native.scope]]` rows with the export's scope kind (`NULL` inherits) |
| `trust_modules` | source digest and status, freshness, region, coverage (`covered`, `unaudited`, `excluded`, `unsupported`, `undescribed`, `external`), scope chain |
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

`meta` gains these `trust.*` keys: `status`, `enforcement`, `coverage`, `core_api` (`silmaril.trust-core.v1`), `sha256`,
`producer`, `origin`, `toolchain`, `profile`, `ceiling`, `roots`, `policy_file` and
`policy_pin`. The database is regenerated, never migrated in place.

## The producer (`sil project trust-dump`)

```
sil project trust-dump --module M [--module …] [--root R] [--exclude M=REASON] [--no-build]
sil project sqlite --dump … --trust .lake/silmaril/trust-core.json [--strict-trust]
```

The command works in two stages:

1. It imports the modules and lists every `Silmaril` module they reach.
2. It writes and elaborates `#trust_export "<out>" M₁ …` for the reached modules under the roots
   (default: all), except the excluded ones.

The export is written unchanged. The command needs #125 at `792e7ed6` or later.
`scripts/trust-export.sh` writes the same document for the modules it is given.

### Exclusions sidecar

The export has no field for why a module is not audited. `trust-dump --exclude M=REASON` writes
the reasons next to the export, in `<export>.exclusions.json` (`silmaril.trust-exclusions.v0.1`:
`export_sha256`, `exclusions` `[{module, reason}]`). This is database-owned metadata and needs no
core API. `--trust` reads it when it is present. It is refused if:

- its `export_sha256` is not the SHA-256 of the export being read;
- a reason is empty or a module is listed twice;
- the export audits a module it excludes.

Each listed module gets `excluded` coverage, and its reason is stored in `trust_modules.reason`.
The sidecar itself is recorded in `trust_inputs` with its digest.

### Real producer output

Each case's README gives the commit and command. The sources are not vendored, so a case's
modules read `stale` in this repository. `policy.toml` is vendored, so the converter can read
`standard`.

| case | ref | result |
|---|---|---|
| `trust-core-bytes` | #125 `cbcd896c` | 556 declarations, **0 violations**; partial (3 modules declare nothing) |
| `trust-core-profile-tests` | same | **9 violations** (6 native outside `default`, 3 unverified); 2 flagged forged use records |
| `trust-elf-staged` | #127 `67503c32` | 299 declarations, **0 violations**; partial (only `Silmaril.Elf.Staged` listed) |
| `trust-elf-profile-tests` | same | **2 violations** |
| `trust-elf-excluded` | same | `Example.Profiles` excluded with a reason (digest-bound sidecar): `excluded` coverage, reason in the DB, partial |
| `trust-lines-rejected` | #125 `d5d8f78c` | the retired JSON-lines input, refused by name |

### Strict validation (in the build checkouts, sources present)

| export | `--strict-trust` |
|---|---|
| bytes normal targets | **passes** on partial coverage ("not a full audit") |
| bytes and `Prelude.Trust.Examples`, the latter excluded | **passes** on partial coverage |
| `Prelude.Trust.Examples` | **fails**: 9 violations and 3 flagged use records |
| ELF `Example.Thms` | **passes** on partial coverage |
| ELF and `Example.Profiles`, the latter excluded | **passes** on partial coverage |
| ELF `Example.Profiles` | **fails**: 2 violations |

### Fixtures (hand-written `silmaril.trust-core.v1` documents; `producer.tool` says fixture)

- `trust-fixture-elf`: a clean export.
- `trust-fixture-violations`: one violation of each class, a forged use record, and a stale
  source.
- `trust-fixture-invalid`: the fail-closed errors.
- `trust-strict-complete`, `-partial`, `-gaps`, `-violations`: `--strict-trust`.

## Remaining gaps

1. **The export omits the policy file's own sets** (`standard`) **and the effective sets.** The
   converter reads `standard` from a digest-checked `policy.toml` and recomputes the effective
   sets.
2. **Realized constants** (`eq_def`, `match_1.congr_eq_*`) appear once per module that lists them,
   each under the listing module and not the defining one. Repeats that are identical apart from
   the module are merged.
3. **The export does not record which modules were listed for audit.** A module with no
   declarations is therefore reported `unaudited`, and coverage is partial even when every
   module was listed.
4. **Root `deps = all`.** Child scopes cannot escalate `deps` or `axioms` (#125 `ba1b5f84`). The
   root still accepts any inherited native procedure: a broad dependency envelope, separate from
   `max`. The database shows the actual `deps` of every module. It does not present the envelope
   as bounded.
5. **Trust in the instrumentation.** Recorded uses and a constant occurring in an axiom's
   statement do not defend against a malicious metaprogram. The guarantee rests on reviewed
   instrumentation and reviewed checker closures, and an LRAT registration needs the exact
   statement.
6. **No CI producer run.** The Rust CI job has no Lean, so the real cases are regenerated by
   hand (see their READMEs) and checked as goldens.
