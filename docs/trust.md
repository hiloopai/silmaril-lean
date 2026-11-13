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
`scripts/trust-profile-exclude.txt`, each with a reason.

## Policy

`policy.toml` `[native]` lists scopes by module prefix. Each scope sets `max`, `default`,
`deps` and `axioms`, inheriting the keys it omits. A child's `max` must lie within its
parent's (checked when the policy loads). `Silmaril/Prelude/Trust/Policy/Defs.lean` loads the
file, pins its hash and declares the trust sets (`default` currently holds the four `bytes.*`
procedures). `scripts/check-layout.sh` fails if the pin is stale, if anything outside
`Silmaril/Prelude/Trust` calls the native evaluator, or if a source file sets the ceiling.

## Provenance

`edge_decide` records every use (declaration, module, procedure, native or kernel, profile,
axiom). `#trust_uses` prints procedures and uses as JSON lines. `trust_audit d₁ d₂ …` prints,
per declaration, its own native procedures, those it inherits through other theorems, its
native axioms and its other axioms, and fails if any of them is outside the policy. The axiom
name itself carries the procedure: `<decl>._native.edge.<procedure>.ax_i_j`.

## Interface for other workflows (stable)

**Bytes** (`import Silmaril.Prelude.Bytes.Thms`; `Silmaril.KBytes`):

* `kbytes_def x from_file "path" [computable]` defines `x`, `x.chunks`, `x.eq_ofChunks`,
  `x.wf : x.wf = true` and `x.len_eq` (`Silmaril.Prelude.Bytes.Elab.Defs`).
  `kbytes_def x of_include raw` does the same from an `include_bytes` definition and adds
  `x.toByteArray_eq : x.toByteArray = raw` (`Silmaril.Data.IncludeBytes.Kernel`).
* Reader: `x.readLE : Nat → Nat → Option Nat` (offset, width ↦ little-endian value). This is
  the shape of `Silmaril.Elf.Check.Src`. Spec: `KBytes.readLE_eq`.
  Single bytes: `get?` (`get?_eq`). Wide reads: `read` (`read_eq`).
* Ropes: `slice`, `++`, with `toList_slice` and `toList_append`. Equality: `rfl` on canonical
  trees, else `sameBytes` (`toList_eq_of_sameBytes`), or `canon` and then `beq`.
* Raw bytes: `kbytes_rel` proves `x.toByteArray = raw`.

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
  kernel side goes through `decideEdge`. The source binding stays in the proposition `P`.
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

## Provenance schema (`silmaril.trust.v1`)

`#trust_uses`, `#trust_registry` and `trust_audit` print one JSON object per line. Every
object has `"schema": "silmaril.trust.v1"` and a `"kind"`. Fields may be added within v1;
renaming or removing a field bumps the version.

| kind | printed by | fields |
|---|---|---|
| `procedure` | `#trust_uses` | `name`, `function`, `kernel_fallback` (bool), `module`, `format` (string or null), `sound` (theorem or null), `native_function` and `native_eq` (both strings, or both null), `doc` |
| `use` | `#trust_uses` | `decl`, `module`, `procedure`, `mode` (`native` or `kernel`), `profile` (e.g. `default`, `local≤paranoid` under a ceiling), `axiom` (string or null) |
| `set` | `#trust_registry` | `name`, `all` (bool), `members`, `includes`, `resolved` (`"all"` or list of names) |
| `scope` | `#trust_registry` | `module` (prefix), `max`, `default`, `deps`, `axioms` (set names or null when inherited), `policy_file`, `policy_pin` |
| `audit` | `trust_audit` | `decl`, `module`, `profile`, `own_native`, `dep_native` (procedure names), `native_axioms`, `axioms` (non-native axioms) |

`#trust_dump "path"` writes all four kinds for everything the environment imports, and
`#trust_roundtrip` re-reads every `procedure` and `use` line with `procOfJson?` and
`useOfJson?` and fails on any difference. This is a low-level emitter format; a database
schema should map it explicitly and check `schema` before reading a line.

Native axiom names have the form `<decl>._native.edge.<procedure>.ax_i_j`, with `<decl>`
possibly `_private.<module>.0.<decl>`. Native runs outside `edge_decide` (plain
`bv_decide`, `decide +native`) appear as `_native.<tactic>.ax_i_j`, and `trust_audit` rejects
them as unregistered. The registry, uses and policy are persistent environment extensions
(`Silmaril.Trust.procExt`, `useExt`, `setExt`, `policyExt`), so a tool that loads `.olean`
files can read them directly instead of parsing output.
