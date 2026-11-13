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
- **Registry ≠ implementation.** `implemented = 0` marks a registry entry: for example the
  bytes relation's native profile, the staged ELF fast mode (#110), whole-file ELF and Wasm
  parsing, the Wasm interpreter and `lean.std.bv_decide.verifyBVExpr`. A use of an unimplemented
  implementation is a violation.
- **Native means trusted computation.** A native implementation trusts the compiled code path
  (the Lean compiler, the runtime and any native code), however narrow its envelope. The trust
  dump records the axioms Lean reported for each use, whatever the toolchain calls them. No
  axiom name is hard-coded, and no axiom is authorized by a name pattern.
- **Digest consistency ≠ freshness.** `freshness = consistent` means that every recorded
  digest still matches: the module source, the sources of its described imports (transitively),
  the listed inputs (policy files) and `lean-toolchain`. It does not prove that the dump is
  current: elaboration options and undescribed imports are not covered.

## The trust dump (`silmaril.trust-dump.v0.1`)

This is the contract proposed to the core work. Fields not listed here are rejected.

```jsonc
{
  "schema": "silmaril.trust-dump.v0.1",
  "toolchain": "leanprover/lean4:…",          // compared with ./lean-toolchain
  "producer": "tool/version",
  "inputs": [{ "path": "policy/trust.toml", "sha256": "…" }],    // policy files etc.
  "procedures": [{ "name": "silmaril.bytes.eq", "kind": "decision", "proposition": "…", "doc": "…" }],
  "implementations": [{ "procedure": "silmaril.bytes.eq", "backend": "kernel" | "native",
                        "profile": "bytearray", "decl": "…", "implemented": true,
                        "surface": "what is trusted beyond the kernel", "doc": "…" }],
  "sets": [{ "name": "kernel.elf.staged", "members": [
              { "set": "kernel.bytes" },
              { "procedure": "silmaril.elf.staged.layout", "backend": "kernel", "profile": "paranoid" }] }],
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
  `(procedure, backend, profile)`, so one procedure can have a native `ByteArray` check and a
  kernel `pageRead` check of the same proposition.
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

### Fail closed

These are errors, and no database is written: a wrong schema, a duplicate, an unknown
procedure, set, implementation or module, a set cycle, a malformed scope, an overlapping policy,
a grant beyond a parent's `max`, and a use in an excluded module.

These are **violations**: the uses that `allow` does not cover (`not-allowed`, direct or through
an import), the uses of an unimplemented implementation (`unimplemented`), and the axioms of a
declaration that no use accounts for (`unattributed-axiom`, checked only when `decls` is
present). Violations are reported as warnings and rows of `trust_violations`. A test checks that
the view and the warnings agree.

## Tables and views (in `silmaril.project-db.v0.2`)

| table | key | content |
|---|---|---|
| `trust_inputs` | path | recorded and current digest, `match`/`changed`/`missing` |
| `trust_procedures` | name | `axiom`/`decision`, proposition, built-in flag |
| `trust_implementations` | procedure, backend, profile | decl, `implemented`, native surface |
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
trust: 11 procedures (11 implementations, 6 native, 7 not implemented), 5 sets, 3 policies
trust modules: 5 covered, 1 excluded, 1 unsupported, 3 undescribed; 8 direct uses
trust violations: 0 (0 direct, 0 transitive)
trust digests: toolchain match, inputs match, modules 5 consistent, 0 stale, 2 unknown (consistent digests are not proof of freshness)
```

The cases in `tools/silmaril-project/tests/project/` are:

- `trust-bytes-elf`: the bytes relation and the staged ELF stages of #110, which are kernel
  checks in paranoid mode, with no violations;
- `trust-violations`: a native fast-mode use, which is not allowed, not implemented, and
  reported again through an importing module; an unattributed axiom; an edited source, which
  makes its module and that module's importer stale;
- `trust-invalid`: the fail-closed errors.

Their sources are placeholder files whose digests are recorded, and the uses are illustrative,
not measured.

Transitive uses of a module, as one query:

```sql
SELECT via, decl, procedure, backend, profile FROM trust_transitive_uses
WHERE module = 'Silmaril.Elf.Staged.Example.Thms' AND direct = 0;
```
