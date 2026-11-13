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
  implementation (`elf.symtrie`, `dwarf.line` in the fixtures) is *registered only*: no set
  can grant it and no use can name it. An implementation with `status = planned` (the native
  fast mode of the ELF stages, `bytes.eq` on `ByteArray`, LRAT) is not supported either: a set
  may grant it ahead of time, but a use of it is an `unsupported` violation.
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
  "procedures": [{ "name": "elf.layout", "kind": "decision", "proposition": "…", "doc": "…" }],
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
  procedure's one proposition `P c`. For example, `elf.layout` has a kernel pair (the reader over
  `pageRead` on 4 KiB literals with `layoutIs_of_sub`) and a native pair (the reader over
  `fastRead` on a `ByteArray` with `layoutIs_of_sub` and `sub_fast`). A `supported`
  implementation must name both `checker` and `soundness`.
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

The field names and meanings above are the v0.1 contract. Within v0.1, only optional fields are
added, and readers reject unknown fields, so a producer and the tool are upgraded together. A
change of meaning or a removal is `v0.2`. The procedure names in use are `bytes.eq`,
`elf.layout`, `elf.body`, `elf.loader`, `elf.entries` and `elf.tiles`. `elf.symtrie` and
`dwarf.line` are registered for the future.

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
trust: 14 procedures (3 registered only), 15 implementations (8 native, 9 planned), 5 sets, 3 policies
trust modules: 5 covered, 1 excluded, 1 unsupported, 3 undescribed; 8 direct uses
trust violations: 0 (0 direct, 0 transitive)
trust digests: toolchain match, inputs match, modules 5 consistent, 0 stale, 2 unknown (consistent digests are not proof of freshness)
```

The cases in `tools/silmaril-project/tests/project/` are:

- `trust-bytes-elf`: `bytes.eq` and the five ELF stages of #110, each with a supported kernel
  pair (paranoid mode) and a planned native pair (fast mode), with no violations;
- `trust-violations`: a native fast-mode use, which is not allowed, not supported, and
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
