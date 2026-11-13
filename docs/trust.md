# Kernel bytes and native edges

This note covers two things: the byte representation the kernel reads quickly
(`Silmaril.KBytes`), and the mechanism that lets a small, named set of compiled procedures
decide facts at designated edges (`Silmaril.Prelude.Trust`). Benchmarks are in
[benchmarks/kernel-bytes](../benchmarks/kernel-bytes/README.md).

## Trust, stated plainly

A native run (`Lean.Meta.nativeEqTrue`, the primitive behind `decide +native` and `bv_decide`)
compiles a closed `Bool` term, runs it, and adds its own axiom `d._native.<tactic>.ax_i_j :
e = true`. This toolchain has no `Lean.ofReduceBool`. A theorem that depends on such an axiom
is **not kernel-checked**. It trusts the Lean compiler, the runtime (GMP for `Nat`), and every
`@[extern]`, `@[implemented_by]` and `@[csimp]` the compiled code reaches. Registering a
procedure narrows that trust to named code; it does not remove it.

## Profiles

| profile | native procedures | use |
|---|---|---|
| `default` | each scope's `default` set (`policy.toml`) | normal builds and CI |
| `local` | each scope's `max` | fast local iteration |
| `paranoid` | none | periodic all-kernel builds |
| any trust set name | that set, cut to the scope's `max` | experiments |

The proposition is the same in every profile; only the proof term changes. A procedure
registered `with_kernel_fallback` is checked by the kernel when it may not run natively. One
without a fallback fails closed. `scripts/trust-profile.sh <profile>` builds under a profile
in its own build directory (`.lake/build-trust-<profile>`), and sets the ceiling, which source
files cannot raise. Run with no targets, it builds every module except those listed in
`scripts/trust-profile-exclude.txt`, each with a reason. It then says so before and after the
build (`trust coverage: PARTIAL`): a passing build covers the modules built, and is not a full
audit under that profile.

## Policy

`policy.toml` `[native]` lists scopes by module prefix. Each scope sets `max`, `default`,
`deps` and `axioms`, inheriting the keys it omits. A child's `max` must lie within its
parent's (checked when the policy loads). `Silmaril/Prelude/Trust/Policy/Defs.lean` loads the
file, pins its hash and declares the trust sets. `default` currently holds exactly six names:
`bytes.sameBytes`, `bytes.beq`, `bytes.wf`, `bytes.eqByteArray`, `bytes.cstring` and
`elf.layout`. `elf.layout` is implemented in ELF's own work, not here. `scripts/check-layout.sh`
fails if the pin is stale, if anything outside `Silmaril/Prelude/Trust` calls the native
evaluator, or if a source file sets the ceiling.

## Provenance

`edge_decide` records every use (declaration, module, procedure, native or kernel, profile,
axiom). `#trust_uses` prints procedures and uses as JSON lines. `trust_audit d₁ d₂ …` prints,
per declaration, its own native procedures, those it inherits through other theorems, its
native axioms and its other axioms, and fails if any of them is outside the policy. The axiom
name itself carries the procedure: `<decl>._native.edge.<procedure>.ax_i_j`.

## Interface for other workflows (stable)

**Bytes** (`import Silmaril.Prelude.Bytes.Thms`; `Silmaril.KBytes`):

* `kbytes_def x from_file "path" [computable]` defines `x`, `x.chunks`, `x.eq_ofChunks`,
  `x.wf_true : x.wf = true` and `x.len_eq` (`Silmaril.Prelude.Bytes.Elab.Defs`).
  `kbytes_def x of_include raw` does the same from an `include_bytes` definition and adds
  `x.toByteArray_eq : x.toByteArray = raw` (`Silmaril.Data.IncludeBytes.Kernel`).
* Reader: `x.readLE : Nat → Nat → Option Nat` (offset, width ↦ little-endian value). This is
  the shape of `Silmaril.Elf.Check.Src`. Spec: `KBytes.readLE_eq`.
  Single bytes: `get?` (`get?_eq`). Wide reads: `read` (`read_eq`).
* Ropes: `slice`, `++`, with `toList_slice` and `toList_append`. Equality: `rfl` on canonical
  trees, else `sameBytes` (`toList_eq_of_sameBytes`), or `canon` and then `beq`.
* Raw bytes: `kbytes_rel` proves `x.toByteArray = raw`.

**Declared two-backend procedures** (the API for ELF and other formats whose native and
kernel checkers take different sources). The declaring module imports only
`Silmaril.Prelude.Trust.Decl.Defs` (Init-only):

```
def Silmaril.Procedures.elf.layout : Silmaril.Trust.ProcDecl where
  doc := "…what the native run trusts…"
  native := some ⟨``layoutOk, ``layoutOk_sound_fast⟩     -- ByteArray / fastRead
  kernel := some ⟨``layoutOkK, ``layoutOkK_sound_pages⟩  -- 4 KiB page literals
```

Each soundness theorem has the form `∀ xs, check … = true → P …`, with the same `P` for both.
Leaf modules (importing `Silmaril.Prelude.Trust.Policy.Defs`) prove

```
theorem layout : LayoutIs F L := by
  sil_check elf.layout (native := layoutOk_sound_fast b L hb) (kernel := layoutOkK_sound_pages pg L hpg)
```

`sil_check` checks each side against the declaration (soundness head, checker head, goal). It
runs the native side if `elf.layout` is allowed natively here. That adds the axiom
`<decl>._native.edge.elf.layout.ax_i_j` and records the use under `elf.layout`. Otherwise
it checks the kernel side with the kernel only. Either side may be omitted. `#trust_decls`
and `#trust_dump` list declarations as `declared_procedure` lines (`name`, `constant`,
`native` and `kernel` as `{check, sound}` or null, `format`, `doc`). Declare only implemented
procedures.

**Native tactics** (for `bv_decide` and other tactics that run compiled code themselves):

```
/-- What the native run trusts. -/
native_tactic lean.std.bv_decide.verifyBVExpr
  evaluates Std.Tactic.BVDecide.Reflect.verifyBVExpr
  axiom_tag bv_decide
  components ["bit-blasting with hash-consing", "AIG to CNF", "relabeling", "LRAT parser and checker"]
  toolchain "leanprover/lean4:nightly-2026-11-05"
  fallback "bv_normalize only"
```

Registration requires that the evaluated constant exists and that `toolchain` is the running
toolchain (`Lean.toolchain`). An axiom tag can belong to only one procedure, and `edge` is
reserved. The `fallback` text is a description: it does not make `kernel_fallback` true.

Audits **classify** an axiom `<decl>._native.<axiom_tag>.ax_<n>` as the procedure by name, but
count it as a procedure-backed use (`own_native`/`dep_native`) only when it is **verified**:

* a recorded use of that procedure names exactly this axiom; and
* the axiom states exactly `@Eq Bool (f a₁ … aₙ) true`, closed, with `f` at the head being the
  procedure's evaluated constant, its paired native function, or (for a declared `ProcDecl`) its
  declared native check. Merely mentioning `f` somewhere is not enough.

The same rule applies to `edge_decide` and `sil_check` axioms. Anything else is listed in
`unverified_native` and is a violation, whatever the policy allows. Registration describes
and classifies; it does not authorize a run.

**Scope of this check.** `recordUse` is trusted elaborator instrumentation. `edge_decide`,
`sil_check` and reviewed framework wrappers call it, but any metaprogram could. The audit is
therefore accounting under reviewed elaborator code, not a sandbox against malicious
metaprograms. What it does guarantee: a recorded use cannot vouch for an axiom whose statement
has a different head, and an axiom with no matching record is never counted. Wrappers for native
tactics should validate the exact closed statement before recording. For `bv_decide` that
means `verifyBVExpr … = true` with the expected certificate and expression; LRAT owns that
check. Tests: `forgedShape` and `forgedDecl` in `Silmaril.Prelude.Trust.Examples` forge
records for wrongly shaped axioms, and the audit rejects both. The framework module that invokes the tactic must:

1. call `Silmaril.Trust.nativeAllowed name : CoreM Bool` (policy, profile and ceiling);
2. if allowed, run the tactic, then call `Silmaril.Trust.recordUse` with `mode := .native` and
   the axiom it added (`profileTag` gives the `profile` field);
3. otherwise run its kernel fallback and record `mode := .kernel`, or fail closed.

Procedure lines carry `evaluated_constant` as `function`, plus `axiom_pattern`, `components`,
`toolchain`, `kernel_fallback` (true when a fallback is described) and `fallback_coverage`.

**Native procedures** (`import Silmaril.Prelude.Trust.Elab.Defs`):

```
/-- What it decides, and what a native run trusts. -/
native_decider elf.layoutOk := Silmaril.Elf.Staged.layoutOk with_kernel_fallback
```

* Prove `f a₁ … aₙ = true` with `by edge_decide` (or `edge_decide elf.layoutOk`), then apply
  your soundness theorem. Keep `f` a plain `Bool` function with a proved soundness lemma. Put
  expensive edges in leaf modules that import the bytes and the shared bounded-width objects,
  so that a profile change rebuilds only those leaves.
* Register `with_kernel_fallback` only if the kernel can actually evaluate the term at the
  sizes you use. Otherwise leave it off; the paranoid profile will then fail closed.
* To run in the default profile, a procedure must be in the `default` trust set
  (`Silmaril/Prelude/Trust/Policy/Defs.lean`). Adding it is a reviewed change.
* Modules whose functions a native run executes must be imported with `meta import`.
* **Paired backends.** When the function the statement uses is slow to compile or run, register
  a separate native implementation and a theorem `@nativeFn = @fn`:
  `native_decider elf.layout := layoutOk with_kernel_fallback native layoutOkFast via
  layoutOkFast_eq`. The statement and the kernel fallback use `fn`. A native run executes
  `nativeFn` and transfers the result with the theorem. The axiom then states
  `nativeFn … = true`.
* **Same-target pairs.** When the native and kernel checkers take *different* arguments (a
  run-time `ByteArray` reader against kernel bytes), pair them through their soundness
  theorems instead of a function equality: `by edge_pair (native := fastSound b A) (kernel :=
  kernelSound kb A)`. Here `fastSound b A : fast b A = true → P` and `kernelSound kb A :
  check kb A = true → P`. The native side runs when its procedure is allowed; otherwise the
  kernel checks the kernel side. The kernel side never runs natively, even where the policy
  would allow its procedure (`decideEdge … (kernelOnly := true)`). The source binding stays in the proposition `P`.
* **Backend hook for adapters.** `Silmaril.Trust.decideEdge (e : Expr) (proc? : Option Name)
  : TermElabM Expr` returns a proof of `e = true` under the policy, records the use, and is
  what `edge_decide` calls. Adapters and format-specific tactics call it instead of reading
  `procExt`, `allowed` or `recordUse` themselves.

**Format checkers** (`import Silmaril.Prelude.Bytes.Checker.Thms`): one interface for every
data format (ELF, JSON, CBOR, S-expressions, WAT, …).

```
structure KBytes.FormatChecker (α : Type) where
  format : String
  Parses : KBytes → α → Prop          -- the bytes encode the value
  check  : KBytes → α → Bool          -- checks a claimed value; never has to parse
  sound  : ∀ b a, check b a = true → Parses b a

native_decider json.check := Silmaril.Formats.Json.checkBytes with_kernel_fallback
  format json sound Silmaril.Formats.Json.checkBytes_sound

theorem doc : jsonChecker.Parses bytes value := FormatChecker.parses_of jsonChecker (by edge_decide)
```

`edge_decide` sees through `C.check` to the registered function. The reference instance is
`KBytes.cstring` (NUL-terminated strings, `bytes.cstring`). Only it is implemented here; JSON,
CBOR, S-expression and WAT checkers are future instances of the same structure.

## Core trust export (`silmaril.trust-core.v1`)

`scripts/trust-export.sh [-o PATH] [MODULE …]` writes `.lake/silmaril/trust-core.json` through
`#trust_export` (`Silmaril.Prelude.Trust.Export`, whose docstring lists every field). It is the
core's format, distinct from the project database's `silmaril.trust-dump.v0.1`; the database
task owns the converter and its compatibility. It holds:

* toolchain, producer (profile, ceiling) and input hashes (policy, regions, toolchain,
  exclusions, policy pin);
* procedures, with backends;
* sets;
* policies from `policy.toml`;
* modules (region, source, SHA-256, imports);
* uses, with `verified` provenance;
* per-declaration axioms, native procedures and violations for the listed modules;
* unresolved set members (never treated as implemented);
* exclusions.

Coverage is only what the driver imports: a missing export or module means unknown, not
clean.

The export keeps the audit's evidence as it is. Recorded uses that fail the provenance check
stay in `uses` with `verified: false` and in each declaration's `unverified_native`. A native
result that a theorem inherits from another theorem stays in that theorem's `dep_native`; it is
not turned into a use of its own. Kernel-backend uses involve no native code, and their presence
authorizes nothing native. **Not integrated with the project database.** The database
reads the `silmaril.trust.v1` lines instead (#124's producer over `#trust_dump`, `moduleLine`
and `auditLine`), so nothing converts this export, and no round-trip through the database has
been tested.

## Provenance schema (`silmaril.trust.v1`)

`#trust_uses`, `#trust_registry` and `trust_audit` print one JSON object per line. Every
object has `"schema": "silmaril.trust.v1"` and a `"kind"`. Fields may be added within v1;
renaming or removing a field bumps the version.

| kind | printed by | fields |
|---|---|---|
| `procedure` | `#trust_uses` | `name`, `function` (the evaluated constant), `kernel_fallback` (bool), `module`, `format` (string or null), `sound` (theorem or null), `native_function` and `native_eq` (both strings, or both null), `axiom_pattern` (`"<decl>._native.<tag>.ax_<n>"` for native tactics, else null), `components` (strings), `toolchain`, `fallback_coverage`, `doc` |
| `use` | `#trust_uses` | `decl`, `module`, `procedure`, `mode` (`native` or `kernel`), `profile` (e.g. `default`, `local≤paranoid` under a ceiling), `axiom` (string or null) |
| `set` | `#trust_registry` | `name`, `all` (bool), `members`, `includes`, `resolved` (`"all"` or list of names) |
| `scope` | `#trust_registry` | `module` (prefix), `max`, `default`, `deps`, `axioms` (set names or null when inherited), `policy_file`, `policy_pin` |
| `audit` | `trust_audit`, `#trust_dump` | `decl`, `module`, `profile` (the audit's), `elaborated_profiles` (recorded when the declaration's own uses elaborated), `own_native`, `dep_native` (verified procedure names), `unverified_native` (`{procedure, axiom}` matched by name only), `native_axioms`, `axioms` (non-native axioms), `violations` (strings; empty when within policy) |
| `module` | `#trust_dump … M₁ M₂` | `module`, `imports`, `profile`, `ceiling`, `max`, `default`, `deps`, `axioms`, `allowed` (`"all"` or names), `scopes` (the scope chain); or `policy_error` |
| `declared_procedure` | `#trust_decls`, `#trust_dump` | `name`, `constant`, `native` and `kernel` (`{check, sound}` or null), `format`, `doc` |

`#trust_dump "path" M₁ M₂ …` writes every kind: the registry and uses for everything the
environment imports, plus a `module` line and an `audit` line per theorem and definition for
each listed module. `audit` lines never fail; they list `violations` against the policy under
the profile and ceiling of the dumping run, next to the profiles the uses were elaborated in.
Axioms are collected transitively with Lean's `collectAxioms`. It reads each imported
declaration's axioms as its defining module computed them from the full (private) bodies, so a
definition exported without its body (opaque to importers under the module system) never shows
up as an axiom, and native axioms reached through other theorems appear as `dep_native`. The
stable Lean hooks behind it are `Silmaril.Trust.dumpLines`, `moduleLine`, `auditLine`,
`declsOf` and `allDecls`; `trust_audit` is `auditLine` failing on violations. And
`#trust_roundtrip` re-reads every `procedure` and `use` line with `procOfJson?` and
`useOfJson?` and fails on any difference. This is a low-level emitter format; a database
schema should map it explicitly and check `schema` before reading a line.

Native axiom names have the form `<decl>._native.edge.<procedure>.ax_i_j`, with `<decl>`
possibly `_private.<module>.0.<decl>`. Native runs outside `edge_decide` (plain
`bv_decide`, `decide +native`) appear as `_native.<tactic>.ax_i_j`, and `trust_audit` rejects
them as unregistered. The registry, uses and policy are persistent environment extensions
(`Silmaril.Trust.procExt`, `useExt`, `setExt`, `policyExt`), so a tool that loads `.olean`
files can read them directly instead of parsing output.
