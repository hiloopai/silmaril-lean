# Decision-procedure and axiom trust in the project database

`sil project sqlite --trust PATH` (and `sil project check --trust PATH`) reads a **trust dump**,
checks it, and adds the trust tables to the project database. The explorer shows them in the
**Trust** tab. This is the project/database side only. The library side (the procedure
registry macros, named sets, region and module policy files, native profiles and the emission
of direct uses) is separate work. Until it emits trust dumps, the inputs here are
hand-written fixtures (`tools/silmaril-project/tests/project/trust-*`).

## Status: what this does and does not claim

- **No trust dump → unknown.** Without `--trust`, the trust tables are empty, `meta` has
  `trust.status = absent`, and `check` prints that use is *unaudited*. That is not a clean
  result. The default policy (the standard axioms) is a default, not evidence.
- **A registered capability is not a supported implementation.** A procedure with no
  implementation (`wasm.interp` in the fixtures) is *registered only*: no set can grant it and
  no use can name it. Capabilities that are not even registered (a symbol trie, DWARF line and
  DIE tables, `.eh_frame` bounds; see `Silmaril.Elf.Staged.Leaf`) do not appear at all. An implementation with `status = planned` (the native
  fast mode of the ELF leaves, `bytes.eq` on `ByteArray`, `bv_decide`'s native evaluation and its
  normalization-only kernel fallback) is not supported either: a set
  may grant it ahead of time, but a use of it is an `unsupported` violation.
- **Native means trusted computation.** A native implementation trusts the compiled code path
  (the Lean compiler, the runtime and any native code), however narrow its envelope. The trust
  dump records the axioms Lean reported for each use, whatever the toolchain calls them. No
  axiom name is hard-coded, and no axiom is authorized by a name pattern.
- **Digest consistency ≠ freshness.** `freshness = consistent` means that every recorded
  digest still matches: the module source, the sources of its described imports (transitively),
  the listed inputs (policy files) and `lean-toolchain`. It does not prove that the dump is
  current: elaboration options and undescribed imports are not covered.

### Native axioms: recorded, not authorized

A native evaluation adds a fresh axiom. For `bv_decide` this axiom is
`<decl>._native.bv_decide.ax_<n>`, stating one closed `verifyBVExpr e cert = true` (#107). This
tool **records** that axiom on the use that produced it (`trust_use_axioms`). It **does not
authorize anything by the axiom's name or shape.** Authorization comes only from the policy
granting the use's `(procedure, backend, profile)`. The producer binds each axiom to its use
and registry entry: it checks the statement (#107's `isBvDecideNativeStatement`, not the
name-only `isBvDecideNativeAxiom`), the evaluated constant and the toolchain. That binding is
the core framework's job. With `decls`, any axiom that no use accounts for is reported as
`unattributed-axiom`.

The `lean.std.bv_decide.verifyBVExpr` entry in the fixtures follows #107 (`c7a65e9c`):

- **native, `planned`:** the checker `Std.Tactic.BVDecide.Reflect.verifyBVExpr` with
  `unsat_of_verifyBVExpr_eq_true`. The natively evaluated surface is all of `verifyBVExpr`:
  bitblasting, AIG to CNF, relabelling, and the LRAT parser and checker.
- **kernel `normalization`, `planned`:** `kernelFallback` covers normalization only. A goal
  that needs SAT returns `.needsSat`, which is unsupported. There is no kernel-checked SAT
  route.

Both entries stay `planned` until #107 and the core framework land.

## The trust dump (`silmaril.trust-dump.v0.1`)

This is the contract proposed to the core work. Fields not listed here are rejected.

```jsonc
{
  "schema": "silmaril.trust-dump.v0.1",
  "toolchain": "leanprover/lean4:…",          // compared with ./lean-toolchain
  "producer": "tool/version",
  "inputs": [{ "path": "policy/trust.toml", "sha256": "…" }],    // policy files etc.
  "procedures": [{ "name": "elf.layout", "kind": "decision", "proposition": "LayoutIs F L",
                   "statement": "Silmaril.Elf.Staged.Leaf.layout", "doc": "…" }],
  "implementations": [{ "procedure": "elf.layout", "backend": "kernel" | "native",
                        "profile": "paranoid", "checker": "…", "soundness": "…",
                        "status": "supported" | "planned",
                        "surface": "what is trusted beyond the kernel", "doc": "…" }],
  "sets": [{ "name": "kernel.elf.staged", "members": [
              { "set": "kernel.bytes" },
              { "procedure": "elf.layout", "backend": "kernel", "profile": "paranoid" }] }],
  "policies": [{ "scope": "root" | "region" | "prefix" | "module", "name": "Silmaril.Elf.Staged.*",
                 "allow": ["standard", "kernel.elf.staged"], "max": ["…"], "origin": "file:line" }],
  "modules": [{ "name": "…", "region": "Formats", "source": "Silmaril/…/X.lean",
                "source_sha256": "…", "imports": ["…"] }],          // direct imports only
  "uses": [{ "module": "…", "decl": "…", "procedure": "…", "backend": "axiom" | "kernel" | "native",
             "profile": "…", "axioms": ["…"] }],                     // direct uses only
  "decls": [{ "module": "…", "decl": "…", "axioms": ["…"] }],        // optional
  "excluded": [{ "module": "…", "coverage": "excluded" | "unsupported", "reason": "…" }]
}
```

- A procedure's identity does not depend on its backend. Its implementations are
  `(procedure, backend, profile)`, and each one is a **checker/soundness pair** targeting the
  procedure's one proposition `P c`. For example, each ELF leaf (`Silmaril.Elf.Staged.Leaf`,
  #123) has a kernel pair (`Leaf.kernel`, the checker over `pageRead` on 4 KiB literals, with
  `Leaf.of_kernel`) and a native pair (`Leaf.native`, over `fastRead` on a `ByteArray`, with
  `Leaf.of_native`). A `supported` implementation must name both `checker` and `soundness`.
- `proposition` is descriptive text. `statement` (optional) names the Lean declaration that
  fixes the statement (for an ELF leaf, the `Leaf` whose `P` it is). The tool never compares
  proposition text, and equal text is not taken as proof of the same statement.
- A use records the backend and profile **actually** used and the axioms Lean reported for that
  proof (`axioms`), so a native use carries its per-computation native axioms, whatever the
  toolchain names them. Until the core API exists, the ELF side emits a temporary
  `Staged.Leaf` record per checked leaf. Each leaf maps to one `uses` entry
  `{module, decl, procedure: "elf.<stage>", backend, profile, axioms}`.
- A set member `{procedure}` grants one backend: `axiom` for an axiom, `kernel` by default for
  a decision procedure. With no `profile`, it grants every profile of that backend.
- The built-ins are the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) as
  procedures, the set `standard`, and a root policy `allow = max = [standard]` when the dump
  has none. A dump may restate them, but only with the same content.

### Policy resolution

For a module, the chain is: the root, then its region, then every matching `prefix` policy
`A.B.*` (shortest first), then the `module` policy. A scope may restate `allow` and `max`, and
what it omits is inherited. Each restated set must lie within the previous effective `max`. When
a scope restates only `max`, the inherited `allow` must still lie within it. Two policies for the
same scope are an error. In this first slice, the effective `allow` bounds a module's own uses
**and** its imports' uses, transitively. There is no separate dependency role yet.
`trust_module_policy` keeps the resolved sets and the scope that declared each one, so a
dependency role can be added there later.

### Report-only vs enforcement

Without `--strict-trust`, nothing is enforced. Violations are warnings and rows of
`trust_violations`, the database is written so they can be inspected, and every run prints
`trust policy: NOT enforced (report only)` and records `meta.trust.enforcement = report-only`.
**A passing run without `--strict-trust` is not a policy check.** For CI, use
`--strict-trust` (or `make project-trust-check TRUST=…`). It exits non-zero, writes no
database, and records `enforcement = strict` when it passes. The strict mode is not yet in
`make check`, because the library does not emit a trust dump yet.

### `--strict-trust`

`sil project check|sqlite --strict-trust` turns violations into errors. It also fails on:

- a missing trust dump;
- a covered module whose digests are not all `consistent`;
- a covered module with an *undescribed* transitive import;
- a dump without `decls`.

Imports that the dump lists as `excluded` or `unsupported` (with a reason) are not errors.
Without `--strict-trust`, these cases are reported but do not fail the run. Fixtures:

- `trust-strict-ok`: passes, with every import described or excluded with a reason;
- `trust-strict-gaps`: fails on undescribed imports;
- `trust-strict-violations`: fails, each violation an error.

The test `strict_trust_fails_where_report_only_writes` runs the same input both ways.

### Fail closed

These are errors, and no database is written: a wrong schema, a duplicate, an unknown
procedure, set, implementation or module, a set cycle, a malformed scope, an overlapping policy,
a grant beyond a parent's `max`, and a use in an excluded module.

These are **violations**: the uses that `allow` does not cover (`not-allowed`, direct or through
an import), the uses of a `planned` implementation (`unsupported`), and the axioms of a
declaration that no use accounts for (`unattributed-axiom`, checked only when `decls` is
present). Violations are reported as warnings and rows of `trust_violations`. A test checks that
the view and the warnings agree.

### Stability

The field names and meanings above are the v0.1 contract. A change of meaning or a removal is
`v0.2`. Within v0.1, only optional fields are added. Readers reject unknown fields, so even
such an addition needs the tool upgraded **in lockstep** with the producer. There is no promise
of forward compatibility.

The project procedures have bare names: `bytes.eq` and the ELF leaves `elf.layout`,
`elf.body`, `elf.loader`, `elf.rela`, `elf.tiles`, `elf.tiles.x86`, `elf.symbols.byName` and
`elf.symbols.byAddr`. Upstream backends keep their qualified names
(`lean.std.bv_decide.verifyBVExpr`).

## Tables and views (in `silmaril.project-db.v0.2`)

| table | key | content |
|---|---|---|
| `trust_inputs` | path | recorded and current digest, `match`/`changed`/`missing` |
| `trust_procedures` | name | `axiom`/`decision`, proposition, built-in flag |
| `trust_implementations` | procedure, backend, profile | checker, soundness, `supported`/`planned`, native surface |
| `trust_sets`, `trust_set_members` | name; set, member | hierarchical sets (members are procedures or sets) |
| `trust_policies`, `trust_policy_sets` | scope kind, scope | declared `allow`/`max` sets and origin |
| `trust_modules` | name | region, source digest and status, freshness, coverage (`covered`, `excluded`, `unsupported`, `undescribed`) |
| `trust_imports` | module, import | direct import edges |
| `trust_uses`, `trust_use_axioms` | module, decl, procedure, backend, profile | direct uses and the axioms of each use |
| `trust_decl_axioms` | module, decl, axiom | every axiom of a declaration (optional) |
| `trust_module_policy` | module, role, set | resolved `allow`/`max` sets per module |

These views are recursive (`WITH RECURSIVE`, `UNION`):

- `trust_set_closure`: the grants of each set;
- `trust_module_allowed`: the grants of each module's effective `allow`;
- `trust_module_deps`: the transitive imports;
- `trust_transitive_uses`: each module's own uses (`direct = 1`) and its imports' uses (`via`);
- `trust_coverage_gaps`: the transitive imports that are not `covered`;
- `trust_violations`.

`meta` gains `trust.status`, `trust.schema`, `trust.sha256` (the digest of the dump file),
`trust.producer`, `trust.toolchain`, `trust.toolchain_status` and `trust.decl_axioms`.

### Migration

The project database is a build output: it is regenerated from the canonical SQL text and
never migrated in place. v0.1 → v0.2 adds tables, views, indexes and `meta` keys, and changes
no existing table, so the existing queries still work. The explorer reads v0.1 files without the
Trust tab's data. Rebuild with `sil project sqlite` to get v0.2.

## Example

```
sil project sqlite --dump dump.json --trust trust.json
…
trust: 15 procedures (1 registered only), 21 implementations (11 native, 12 planned), 5 sets, 3 policies
trust modules: 5 covered, 1 excluded, 1 unsupported, 3 undescribed; 8 direct uses
trust violations: 0 (0 direct, 0 transitive)
trust digests: toolchain match, inputs match, modules 5 consistent, 0 stale, 2 unknown (consistent digests are not proof of freshness)
```

The cases in `tools/silmaril-project/tests/project/` are:

- `trust-bytes-elf`: `bytes.eq` and the eight ELF leaves of #110 and #123, each with a
  supported kernel pair (paranoid mode) and a planned native pair (fast mode), with no
  violations;
- `trust-violations`: a native ELF fast-mode use and a native `bv_decide` use (with its
  per-evaluation axiom recorded), each not allowed, not supported, and
  reported again through an importing module; an unattributed axiom; an edited source, which
  makes its module and that module's importer stale;
- `trust-invalid`: the fail-closed errors;
- `trust-strict-ok`, `trust-strict-gaps`, `trust-strict-violations`: `--strict-trust`.

Their sources are placeholder files whose digests are recorded, and the uses are illustrative,
not measured.

Transitive uses of a module, as one query:

```sql
SELECT via, decl, procedure, backend, profile FROM trust_transitive_uses
WHERE module = 'Silmaril.Elf.Staged.Example.Thms' AND direct = 0;
```
