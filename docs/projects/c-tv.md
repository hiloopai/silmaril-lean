# C translation validation

The long-term goal is a translation-validation toolkit for C: given a C program, the
representations real tools produce for it (Clang's AST, Cerberus's Ail and Core, object code),
and a target profile (language, data model, ABI, implementation-defined choices), produce
kernel-checked statements that relate those representations, with validators whose soundness is
proved, explicit about what each statement assumes. The yardstick is the GCC C torture suite:
translation-validate every test that is in scope, and prove the validators sound. **That goal is
not met.** This page says what exists, what each piece means, and what remains, in order.

Related pages: [Cerberus C semantics](cerberus.md) (the Lean port this builds on),
[C to x86, segment by segment](compiles-to.md) (function-level C ↔ machine code),
[System V TV](sysv-tv.md) and [ABI](abi.md).

## What exists (stage 1)

| Piece | Where | Status |
| --- | --- | --- |
| Whole-program behaviours: endings, stuck states, divergence, observations | `Silmaril/Cerberus/TV/Behaviour/Defs.lean` | definitions |
| Whole-program refinement `Refines impl src tgt` and equivalence | same | definitions |
| Exhaustive bounded exploration of a closed Core program | `Silmaril/Cerberus/TV/Explore/{Defs,Thms}.lean` | soundness, completeness, termination and progress **proved** |
| Refinement validator `validate` (verdicts `validated`, `refuted`, `unsupported`, `unknown`) | `Silmaril/Cerberus/TV/Validate/{Defs,Thms}.lean` | `validate_sound`, `validate_refuted`, `validateEquivalent_sound` **proved** |
| Target profiles and their coherence with the Core semantics, per scalar type | `Silmaril/Cerberus/TV/Profile/Defs.lean` | decidable; table for x86-64 System V **computed in the kernel** |
| Per-type applicability of a profile to a program (`mentions`, `AppliesTo`, `RefinesOn`) | `Silmaril/Cerberus/TV/Applicability/Defs.lean` | decidable |
| Stages, artifacts, edges and evidence kinds | `Silmaril/Cerberus/TV/Provenance/Defs.lean` | vocabulary |
| Shapes `silmaril.shapes.c.tv.{refines,refines_ub_free,not_refines,equivalent,profile_coherent_at,profile_applies,refines_on}` | `Silmaril/Project/Shapes/CTV/{Defs,Thms}.lean` | shapes, bridges from verdicts |
| Registered rows over elaborated Core | programs in `Silmaril/Project/CTV/Examples/Defs.lean`, rows in `silmaril/c-tv.toml`, theorems in `examples/c-tv/CTvRows.lean`, more verdicts in `tests/cerberus/TVExamples.lean` | 14 kernel-checked verdicts, positive and negative; interpreted negative checks in `tests/cerberus/TVValidate.lean` |

All theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. Verdicts in the
examples are computed in the kernel (`by cbv`); none uses `native_decide`.

### The statement

`Refines impl src tgt` (`TV.Behaviour`) is about **closed** programs (the Core file, its enum
registry and its command-line arguments), run by the Lean port's Core LTS with the concrete
PNVI-ae-udi memory:

1. every observation (`Spec.Obs`: exit status or abort or signal, and the stdout bytes) the
   target allows, the source allows (`Spec.allowed`, with the implementation-defined choices
   `impl`);
2. the target never reaches a **gap** of the dynamics: no `error` or `unsupported` ending and no
   **stuck** state (not halted, no transition);
3. the target has no infinite run.

The behaviours are kept apart, not merged:

| Behaviour | How it enters |
| --- | --- |
| undefined behaviour | a source run reaching UB admits every observation (C11 §4p2); a target UB ending allows every observation, so only a source that may reach UB covers it |
| unspecified values | an unspecified exit value admits every exit status, with the same stdout |
| unspecified order / nondeterminism | every interleaving of `unseq` and every `nd` choice the port's LTS keeps is explored; the concrete memory's allocator is deterministic, so behaviours ISO C allows through other allocation addresses are not |
| implementation-defined choices | only the exit status and `abort` flushing are parameters (`impl`); the scalar choices of the target profile are compared, not parameterized (below); the rest (integer conversions and shifts in the runtime, aggregate layout, bit-fields, pointer representation) are fixed by the port |
| divergence | not an observation; the target must terminate (stronger than divergence-preserving refinement) |
| stuck / unsupported | never accepted on the target side (2); on the source side a gap admits nothing, so it can only make `validated` harder and it blocks `refuted` |

Requirement (2) is what keeps refinement from being vacuous: without it, a target whose runs all
end in `unsupported` would refine every source.

### The validator and what a verdict means

`validate impl src tgt bounds` is a **sound partial validator** (a sound semi-decision, not a decision procedure): it explores both programs and checks
that each target ending is covered by one source ending. `validated` and `refuted` are proved;
`unknown` may hide a true refinement, even with exhaustive explorations, because coverage is ending
by ending (a target with an unspecified exit value is covered only by an unspecified source exit
value, not by several source endings that together give every status).

| Verdict | Requires | Theorem |
| --- | --- | --- |
| `validated` | target exploration exhaustive, no gap, no stuck state, every target ending covered | `Refines impl src tgt` |
| `refuted` | both explorations exhaustive, source without gaps, some target ending has a witness observation no source ending admits | `¬ Refines impl src tgt` |
| `unsupported` | the target reached a gap or a stuck state | none (the target leaves the defined fragment) |
| `unknown` | a bound was hit, or no usable witness | none |

`Report.coveredOnlyByUB` is set when some target ending is covered only by source undefined
behaviour; the verdict is then still `validated` (that is C's meaning) and a reader should know.
`validateUBFree` (proved: `RefinesUBFree`, shape `c.tv.refines_ub_free`) additionally requires an
exhaustive source exploration without undefined behaviour, so its rows cannot rest on source UB.

**Bounded enumeration is not C behaviour in general.** Exhaustiveness means the execution tree of
this program on these arguments is finite and fits the bounds: every run has at most
`bounds.depth` transitions (`Closed.explore_terminates`). A program with an infinite run is
always `unknown`. Nothing is claimed for other inputs, other arguments or other profiles.

### Profiles and coherence

A result is about the Lean port's Core semantics. It says something about a real target only
where the semantics' choices agree with the target's. `Profile` (in `TV.Profile`) gathers the
target's independent parameters: the shared data model `Silmaril.Data.Layout.DataModel` (read
only), the **numeric format** of each floating kind (`NativeTypes.Floating`: binary32, binary64,
x87 extended, binary128, … — separate from storage size, so x87 `long double` is 80 value bits
in 16 bytes on x86-64), the elaborator's `Target.Config`, `impl` and the language. ABI argument
passing is not part of a profile. `Profile.issues p s` compares, per scalar type, the Core
memory's layout (`Mem.Concrete.typeLayout`, the function the dynamics uses), the elaborator's
layout, signedness, value range, endianness and numeric format with the target's.

For `linuxX86_64` (System V psABI data model, `TargetCoherence.linuxLP64` elaborator):

| Scalar types | Coherent |
| --- | --- |
| `_Bool`, `char`, `signed`/`unsigned char`, `short`, `int`, `long`, `long long` (both signs), `size_t`, `ptrdiff_t`, `intptr_t`, `uintptr_t`, pointers, `double` | yes (`linuxX86_64_coherentScalars`) |
| `wchar_t` | **no**: the port's `Mem.Concrete.integerBounds` gives `wchar_t` the range `0 … 2³²−1` while its layout and the psABI make it signed |
| `float` | **no**: the port stores it in 8 bytes and computes in binary64 (upstream's `DefaultImpl` shortcut); the target is binary32 in 4 bytes |
| `long double` | **no**: 8-byte binary64 in the port; x87 extended in 16 bytes on the target |

`legacyPinnedApple` (upstream's pinned `Target.pinnedApple` elaborator configuration) also
disagrees at the floating types in the elaborator. These legacy assumptions are reported, not
replaced. Coherence is **necessary, not sufficient** for a result to transfer to x86-64 Linux:
programs whose object types are outside the coherent set are about the port's legacy model, and
even inside it the comparison leaves out the runtime's implementation-defined integer operations,
aggregate layout and padding, bit-fields, pointer representation and allocation addresses.
`Profile.language` and the `float128` format are labels that nothing compares yet.

### Provenance and evidence

`TV.Provenance` names the stages (source, preprocessed, Clang AST, Cabs, Ail, typed Ail, Core,
object), the artifact identity (SHA-256 of the exact bytes, producer tool, version, arguments,
target) and the evidence an edge rests on: `kernel` (a theorem whose statement is the edge),
`compiled` (a compiled run of a Lean function), `oracle` (agreement with another implementation:
testing), `external` (tool output taken as given) or `missing`. Clang's JSON AST is untrusted
frontend output: source → Clang AST is `external`, Clang AST → typed Ail is the fail-closed
importer `cfront`, and only Core → Core edges carry semantic theorems so far. A missing stage is
shown as missing, never fabricated.

## Upstream Lean work on Cerberus

The authoritative Cerberus is [rems-project/cerberus](https://github.com/rems-project/cerberus)
(BSD 2-Clause with listed exceptions). It has no Lean backend. Silmaril's port is a hand
transcription pinned at `b3e11ea3` (see [cerberus.md](cerberus.md#provenance-and-licence)).
Two third-party Lean ports exist; neither is an official part of Cerberus, and agreement with
them would be differential evidence, not a formal equivalence with the C standard or with
upstream:

* [OathTech/cerberus-lean](https://github.com/OathTech/cerberus-lean), branch
  `mdd/cerberus-lean` (inspected at `8fa3050b`, 2026-11-14): a fork of rems-project/cerberus
  (base `c3ff8c53`) whose Lean is **generated from the Lem model** by a Lem fork
  (OathTech/lem-lean at `2220010b`); the OCaml parser emits Cabs JSON and Lean desugars, types,
  elaborates and executes; validated differentially against the OCaml engine. Licence: Cerberus's
  LICENSE and exceptions plus LemLib's notices (not BSD-only).
* [septract/lean-c-semantics](https://github.com/septract/lean-c-semantics): a hand-translated
  Core interpreter and memory model over Core JSON exported by a patched Cerberus.

Nothing from either is copied here. Using them is on the roadmap (stage 6) as a differential
comparison on the corpus, with their licences recorded if any file is ever reused.

## Relations: Core to Core, frontend agreement, compiler origin

Three different relations are kept apart, in the shapes, the provenance edges
(`TV.Provenance.Relation`) and the explorer:

| Relation | What it relates | Where |
| --- | --- | --- |
| Core to Core (`refines`, `equivalent`) | two closed Core programs, under the port's semantics | `c.tv.refines*`, `c.tv.equivalent`, `c.tv.not_refines` |
| frontend agreement (`frontendAgreement`) | the Cores two frontends (Clang route, Cerberus route) give one source: a Core-to-Core relation between their outputs | corpus reports, torture `cross-validated` |
| compiler origin (`compiles`) | a compiler's machine code and a C function's Core | `c.compiles_to*` ([compiles-to](compiles-to.md)); whole-program object code is open |

No Core-to-Core row implies anything about a compiler's output. The **per-type profile check**
(`c.tv.profile_applies`, and `c.tv.refines_on`, which is Core refinement plus that check on both
programs) is a necessary filter, not a statement about the target. It requires every type named
by the reachable Core to be in the coherence table and coherent: `TV.mentions` scans the program
part (its own functions, globals, tags and function information), the runtime functions and the
implementation constants it reaches (transitively, by symbol and by `PEimpl`/`Impl` name), and
over-approximates within them (a floating object or value without its kind counts as all three).
The x86-64 check fails for any program whose reachable Core names `float`, `long double`,
`wchar_t`, or a type outside the table (aggregates, enums, exact-width integers). It cannot see
operations rather than types (conversions, shifts, division in the runtime and `impl`;
builtin functions run natively and only their call-site types are scanned),
allocator addresses, byte-level punning, or the enum registry (run empty).

Under the default profile (`linuxX86_64`, elaborated with `TargetCoherence.linuxLP64`) the check is conservative to the point of failing on every corpus program: Cerberus's runtime
conversion functions that the corpus Cores reach (`conv_int` and its callees) dispatch on the
type and name `is_representable_floating`, `loaded_ivfromfloat` and the floating kinds, even on
integer-only paths. Only the constructed `return a + b;` files (whose runtime is three integer
functions) pass. A check over the types of the executed path, proved to cover them, is on the
roadmap (milestone 7).

## Undefined behaviour in the accounting

A source reaching undefined behaviour admits every observation (C11 §4p2). A verdict that rests
on it is never counted as a validation of defined behaviour:

* the report flags `coveredOnlyByUB`; the shape `c.tv.refines_ub_free` (`validateUBFree`)
  requires an exhaustive source exploration without undefined behaviour;
* the corpus labels such verdicts "only through source UB" (`overflow-return`), and the explorer
  tags them;
* the torture runner counts them as `cross-validated-ub`, separately from `cross-validated`,
  which requires UB-free sources in both directions.

## Registered rows

[`silmaril/c-tv.toml`](../../silmaril/c-tv.toml) registers the rows (group `silmaril.c_tv.all`, a
child of the root group), and [`examples/c-tv/CTvRows.lean`](../../examples/c-tv/CTvRows.lean)
solves or refutes each one with a theorem whose statement is the row. `sil project check` audits
the statements and axioms; the explorer's C tab and its problem pages read them from the
database. Rows: the fold refines / refines UB-free / is equivalent (THM); the wrong fold does not
refine (UNS); `INT_MAX + 1` is refined by anything (THM) but not UB-free (UNS); the x86-64 per-type
check passes on the fold (THM), the fold refines with the check on both programs (THM), and the
check fails on a synthetic file whose Core names `float` (UNS); and one `profile_coherent_at` row per scalar type of the
table, 18 THM and 3 UNS (`wchar_t`, `float`, `long double`).

`CTvRows` is not a `module`. Under the module system the same `cbv` runs of the Core dynamics are
two orders of magnitude slower (a six-transition prefix of `return 1 + 2;` did not finish in three
minutes, while the whole validation takes seconds outside one): the declarations are real
registered declarations with their kernel-checked proof terms, and moving them into a module is
an open obligation. No verdict is evaluated natively for a kernel claim.

## Two scopes

### The current, restricted validator

What a `validated` or `refuted` verdict covers today, and nothing more: a **closed** program (no
input, fixed command-line arguments), whose execution tree under the port's Core semantics is
**finite and fits the bounds** (every run at most `depth` transitions), with a **terminating**
target that stays in the supported fragment, as a **Core-to-Core** relation. Unknown verdicts may
hide true refinements (coverage is ending by ending). Programs with loops whose runs exceed the
bounds, inputs, divergence, or an object-code side are out of its scope by construction, not
merely untested.

### The long-term roadmap: every in-scope GCC torture test validated, validators proved sound

Independent of the restricted validator's limits; each milestone is a reviewed PR with
soundness theorems and negative tests, and moves torture statuses (benchmarks/gcc-torture) from
rejected/unknown toward validated against the fixed denominator of 3,852.

1. **Foundations** (#894). Done.
2. **Program corpus, stage artifacts and registered rows** (#898, and the registry PR). Remaining:
   kernel instances for corpus Cores (needs the module-system `cbv` issue solved, or a symbolic
   validator instead of enumeration).
3. **Explorer: C programs tab** (#900; on the project database and with tamper tests: #934 — the
   corpus's sources and provenance are registered artifacts, and a full `make pages` is checked
   together with the CLI tab). Remaining: rows for corpus programs once they exist.
4. **GCC torture manifest and runner** (#902). Remaining: interpret DejaGNU `.x` options and the
   builtins harness; a `gnu89`/permissive language profile with its own coherence obligations.
5. **Elaborator coverage.** Port the rest of `translation.lem`, ranked by the torture blockers:
   defined variadic, `noreturn` and non-`int` functions; statements and loops; all integer
   operators; initialized locals of every type; `sizeof` of expressions; aggregates; floating
   constants.
6. **Frontend coverage.** The Clang route's block locations, `asm` statements, `va_list`; the
   Cerberus route's implicit `int`, K&R definitions and GNU extensions, each preserved or
   rejected explicitly.
7. **A precise per-type check and profile-parametric memory.** A per-type check over the types
   the executed paths touch, proved to cover them (the current scan of reachable runtime code
   fails on every corpus program under the default profile). `ctv-pipeline --profile` selects the
   profile, its elaborator configuration and its implementation-defined choices; elaborated with
   upstream's `Target.pinnedApple` (`--profile legacyPinnedApple`) the integer corpus programs
   reach only integer runtime functions and pass that profile's check, which shows the check
   depends on the elaboration, not only on the source. Then profile-parametric memory: `Mem.Concrete` layouts and floating values from the profile
   (binary32, x87, binary128), the `wchar_t` range, aggregate layout through the shared ABI layout
   (main task's `Data.Layout`), endianness; then the profile applies to floating programs.
8. **Validators beyond enumeration.** Symbolic or simulation-based Core-to-Core validators with
   soundness proofs (no finite-tree requirement); divergence-aware refinement; set coverage of
   endings; partial-order reduction for `unseq`.
9. **Compositional evidence.** *Started* (`Silmaril.Cerberus.TV.Compose`): vertical composition
   (`Refines.trans`, `Equivalent.symm`/`trans`: pipeline steps compose without re-validating the
   end points; `fold_in_two_steps` in `CTvRows`), and function-level refinement over explicit
   contexts: the shape `c.tv.context_refines` is `FunctionRefines` (a nonempty list of contexts,
   each with a substitution witness `Substitutes`: the function defined in the context's own
   functions and not shadowed by its runtime library), validated by `validateContexts` with its
   soundness theorem; `ContextRefines` is the raw weak relation (vacuous for no context, a no-op for
   an undefined or shadowed symbol) and `ContextRefines.then` composes replacing one function and
   then another; a registered row replaces `main`'s Core in its file, and
   `tests/cerberus/TVCompose.lean` keeps the vacuous and bogus cases rejected. Several functions at
   once: `ModuleRefines` (shape `c.tv.module_refines`; nonempty contexts and replacements, distinct
   substituted functions), validated one function at a time (stage `i` to `i + 1`) and composed by
   induction (`validateModule_sound`, `refines_chain_upto`); registered rows replace `id` and
   `main` in `int id(int x) { return x; } int main(void) { return id(42); }` (THM: `id := return 42`
   refines only because `main` calls `id(42)`, so the claim is about that context) and refute
   `id := return 41` (UNS). The torture suite's 1,979 compile/ cases
   (46 of which elaborate without `main`) need exactly this function-level evidence, not
   whole-program behaviour. Remaining: contextual refinement for all
   contexts (a simulation over the Core LTS, or contracts at the function boundary), expression-
   and statement-level contexts, and external calls under contracts.
10. **Inputs and environment.** Observations over stdin, files and `argv`.
11. **Compiler origin.** Whole-program object code against the source's Core, through the ELF,
    startup and ABI shapes owned by those tasks (consumed by adapters); this, not frontend
    agreement, is what "the GCC torture test is translation-validated" requires.
12. **Upstream comparison.** OathTech/cerberus-lean and the OCaml Cerberus on the corpus and the
    torture cases, reported as oracle evidence with exact revisions.

## Unported C work from moria-lean, and the models still missing

Everything of moria-lean's C and Cerberus trees is either ported (the Cerberus closure, Core
elaboration, the Clang importer, the C semantics `Compiler/C/Sem` except below, CompilesTo and the
Cerberus oracle), owned by another task, or listed here with its reason.

| Unported | What | Why, and what would port it |
| --- | --- | --- |
| `Compiler/C/Sem/{C0SignedCondition,C0SignedConditionChecks,C0SignedSafety,C0SignedToCminor,C0SignedToCminorChecks,C0SignedX86Add,C0SignedX86AddChecks}` | signed C0 fragments lowered to Cminor and x86 adds | depend on `Machine/CSupport/CompCert/*`: **deferred by decision** (licence boundary, below) |
| `Compiler/C/Sem/RefinedC{MaxLir,MaxLirChecks,OwnedLir,OwnedRV64,OwnedScalar*,OwnedSwapLir*,OwnedUint64*,ProgramsLir,ProgramsSignedLir*}` (23 modules) | RefinedC-owned fragments lowered through LIR to RV64 | same dependency: **deferred** |
| `Machine/CSupport/CompCert/*` (12 modules) | restricted Clight, Cminor, integer support, lowering and validation | 8 carry `LGPL-2.1-or-later` headers adapted from CompCert v3.17 (`7b1f02b0`, files CompCert dual-licenses); 4 are moria-original but import them. Kept out of this MIT repository by decision (2026-11-17); porting would need a NOTICES/CompCert entry and the per-file licence, or a clean-room replacement |
| `tools/c-bench` (Rust: Clang JSON import benchmark, native-quality, native torture runner) | native-compiler measurements | not translation validation; `scripts/c-tv/torture.py` is the TV runner. Porting the JSON-import benchmark is optional tooling |
| `benchmarks/gcc-torture/{recorded,initial,latency}*.json`, `triage/` | the native compiler's torture coverage and its gap triage | native-compiler evidence, not TV; the manifest was ported |
| `checkpoint/c-layout-explorer-*` | C layout explorer | main task (9e7aa15b) |
| `oss/cerberus-tv` wave 3 (23 x86 modules) | x86 decoding, relocation, system V contracts | ELF/x86 tasks |

Models the toolkit does not have yet, each with its milestone above:

| Model | Now | Needed |
| --- | --- | --- |
| Memory | Cerberus's concrete PNVI-ae-udi memory, LP64 layouts fixed, deterministic allocator | profile-parametric layouts (7); other provenance models; allocation nondeterminism; effective types / strict aliasing |
| Floating point | every real floating type stored in 8 bytes and computed in binary64 | binary32, x87 extended, binary128 through the shared IEEE model (7) |
| Integers | LP64; `wchar_t`'s range is unsigned while its layout is signed (incoherent with x86-64) | the `wchar_t` range; other data models (7) |
| Endianness | little-endian | big-endian targets (7) |
| Concurrency, atomics | not supported (sequential semantics) | an SC or weak-memory Core semantics |
| Inputs and environment | closed programs, fixed `argv` | stdin, files, `argv` as inputs (10) |
| Divergence | targets must terminate | divergence-aware refinement and its validators (8) |
| Function boundaries | function- and module-level refinement over listed contexts | all contexts (simulation or boundary contracts), external calls under contracts (9) |
| Machine code | function segments (`c.compiles_to*`) | whole-program object code against the source's Core (11) |

### Open obligations (concrete, by area)

* **Semantics coverage.** The Ail-to-Core elaborator covers selected cases of `translation.lem`
  and rejects the rest (pointer arithmetic, floating constants, compound literals, indirect calls,
  …: [cerberus.md](cerberus.md#status)); every rejected construct is a torture-test blocker to
  port, with its upstream lines.
* **Data model and floating point.** Parameterize `Mem.Concrete` layouts by the profile instead
  of the LP64 constants; give `float` binary32 and `long double` x87/binary128 values through the
  shared IEEE model; fix the `wchar_t` range; big-endian targets (the concrete memory is
  little-endian).
* **Memory model.** Only PNVI-ae-udi concrete memory; ambiguous provenance (iota) is unsupported;
  effective types / strict aliasing are not checked; object lifetimes follow Cerberus's
  allocation model.
* **Concurrency and atomics.** Not supported (Cerberus's sequential semantics; `memory_order`
  is syntax only).
* **Validator completeness.** Cover a target ending by a set of source endings (unspecified exit
  values), and add the profile comparisons above (language, `float128`, implementation-defined
  integer operations, aggregate layout).
* **Divergence.** Refinement requires target termination; a divergence-aware relation
  (divergence allowed when the source may diverge, observed output prefixes) and validators for
  it (simulation with a measure, or cut-point invariants) are needed for nonterminating programs.
* **Inputs.** Closed programs only (arguments fixed); programs reading stdin or files need an
  environment model in the observation.
* **Scale.** The validator enumerates the whole execution tree; exponential interleavings of
  `unseq` need partial-order reduction (proved sound) or symbolic validation.
* **Frontend edges.** Source → Clang AST is external; the Clang importer and the Lean Cerberus
  frontend are fail-closed decoders, not proved to implement the C grammar or C's typing rules;
  the preprocessor is external.
* **Machine code.** Whole-program C ↔ object code (beyond the function segments of
  [compiles-to](compiles-to.md)) needs the ELF/startup and ABI pieces owned by the ELF and ABI
  work, consumed through adapters.
* **Kernel evaluation under the module system.** The registered rows (`CTvRows`) are computed by
  `cbv` in a non-`module` library: in a `module` the same `cbv` runs did not finish within minutes
  (with the `cbv_eval` equations and `import all` of the String modules the compiles-to proofs
  use), while each takes seconds outside one.
* **Validator soundness for the full toolkit.** Each new validator lands with its soundness
  theorem and negative tests; native (compiled) evaluation of a validator is tagged `compiled`,
  never presented as a kernel fact.
