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

## The trust lines (`silmaril.trust-lines.v0.1`)

The file has one JSON object per line, each with a `kind`. Unknown kinds and fields are
rejected, so producer and tool upgrade **in lockstep**, with no forward compatibility.

| kind | from (core API) | fields |
|---|---|---|
| `header` | driver; `profile`, `ceiling` | `schema`, `toolchain`, `profile`, `ceiling`, `producer`, `origin`, `roots` |
| `input` | `trust-dump` | `path`, `sha256` |
| `policy` | `policyExt` | `file`, `pin` (FNV-1a) |
| `scope` | `Policy.scopes` | `module`, `max`, `default`, `deps`, `axioms` (null inherits) |
| `set` | `Policy.sets`, `setExt` | `name`, `all`, `origin`, `members`, `includes` |
| `procedure` | `procJson` | `name`, `function`, `kernel_fallback`, `module`, `doc` |
| `use` | `useJson` | `decl`, `module`, `procedure`, `mode`, `profile`, `axiom` |
| `module` | `env.header`; `trust-dump` | `name`, `imports`, `source`, `source_sha256` |
| `effective` | `effective`, `allowed` | `module`, `max`, `default`, `deps`, `axioms`, `allowed`, `trace` (or `error`) |
| `decl` | `axiomReport` | `decl`, `module`, `own_native`, `dep_native`, `plain_native`, `axioms`, `native_axioms` |
| `excluded` | (by hand) | `module`, `coverage` (`excluded`, `unsupported`), `reason` |

### Checks (fail closed)

These are errors, and no database is written:

- **Lines:** a malformed line, a missing or extra header, a wrong schema, or a duplicate.
- **Uses:**
  - a use of an unknown procedure;
  - a native use whose axiom is not a native run of that procedure;
  - a kernel use of a procedure without a kernel fallback.
- **Sets and scopes:**
  - an unknown or cyclic set include, or `all`/`none` redeclared;
  - an unknown set in a scope, or a duplicate scope;
  - a scope whose `max` exceeds its parent's.
- **Producer agreement:**
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
appears as `dep_native` in every theorem that uses it.

## Tables and views (`silmaril.project-db.v0.2`)

| table | content |
|---|---|
| `trust_inputs` | recorded and current digests (`match`, `changed`, `missing`) |
| `trust_procedures` | `native_decider`s: function, module, `kernel_fallback`, doc |
| `trust_sets`, `trust_set_members` | sets (`builtin` `all`/`none`, `policy`, `trust_set`), members (`name`) and includes (`set`) |
| `trust_scopes` | `[[native.scope]]` rows (`NULL` inherits) |
| `trust_modules` | source digest and status, freshness, coverage (`covered`, `excluded`, `unsupported`, `undescribed`, `external`), policy trace |
| `trust_imports` | direct import edges |
| `trust_module_policy` | effective `max`, `default`, `deps`, `axioms`, `allowed` per module (`*` = all) |
| `trust_uses` | recorded `edge_decide` runs (mode, profile, native axiom) |
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
sil project trust-dump --module Silmaril.Prelude.Bytes.Examples [--module …] [--root Silmaril] [--no-build]
sil project sqlite --dump … --trust .lake/silmaril/trust.jsonl [--strict-trust]
```

The command works in three steps:

1. It writes `.lake/silmaril/TrustDump.lean`, which imports the modules and walks the core API
   (`tools/silmaril-project/src/project/trust/Driver.lean`).
2. It runs `lake build --wfail` and `lake env lean` on that file.
3. It adds the producer, the inputs and each module's source digest.

The driver uses core internals that #125 does not yet declare stable: `policyExt`, `setExt`,
`procExt`, `useExt`, `allEntries`, `effective`, `allowed`, `axiomReport`, `procJson`,
`useJson`, `hex64`, `profile` and `ceiling`. The hooks requested from the core are listed below.

### Real roundtrip (bytes)

`tests/project/trust-core-bytes` is **producer output** (origin `lean`). It covers the bytes
and trust modules of #125 at `28418c29`:

- 17 modules, 6 procedures, 8 uses (5 native) and 192 theorems;
- every effective set agrees with the recomputed one;
- 3 violations: the examples that run `test.evenSum` under the `local` and `toys` profiles,
  which the core's own `trust_audit` rejects in the default profile.

The case's README says how the file was produced. The case does not vendor the sources, so
its digests read `missing`/`stale`.

### Fixtures (hand-written, origin `fixture`)

- `trust-fixture-elf`: the ELF leaves of #123 as **hypothetical** `native_decider`s
  (`elf.layout`, `body`, `loader`, `rela`, `tiles`, `tiles.x86`, `symbols.byName`,
  `symbols.byAddr`), with kernel runs in the default profile. Nothing in #123 or #125 registers
  them yet.
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

1. **A stable dump hook.** `#trust_uses` prints only procedures and uses. Wanted: a declared
   `#trust_dump` (or a stable `Silmaril.Trust.dumpLines`) that emits every line kind above. The
   driver could then stop reading the extensions directly.
2. **Effective sets per profile.** The dump fixes one profile and ceiling (the driver's options).
   A use records the profile it ran under, but the audit uses the dump's. Theorems that are
   deliberately elaborated under `local` or a set profile show up as violations at `default`.
3. **Binding a procedure to its proposition.** `edge_decide` picks the procedure by the goal's
   head function. A generic runner shared by several leaves (for example `Leaf.native` for
   every ELF leaf) would let a goal be decided under the wrong name. Each ELF leaf should get its
   own closed `Bool` function before it is registered.
4. **ELF.** #123's `Staged.Leaf` record is not registered with `native_decider`. ELF has no real
   roundtrip until it is, and the ELF modules need Mathlib to build.
5. **`deps` is not bounded by `max`.** That is the core's rule (`deps = all` at the root). The
   database reproduces it as is.
6. **Exclusions.** The core's `scripts/trust-profile-exclude.txt` lists modules skipped by
   profile builds. These are not audit exclusions, so this tool does not read them; `excluded`
   lines are written by hand.
