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
| Stages, artifacts, edges and evidence kinds | `Silmaril/Cerberus/TV/Provenance/Defs.lean` | vocabulary |
| Shapes `silmaril.shapes.c.tv.{refines,refines_ub_free,not_refines,equivalent,profile_coherent_at}` | `Silmaril/Project/Shapes/CTV/{Defs,Thms}.lean` | shapes, bridges from verdicts |
| Examples over elaborated Core | programs in `Silmaril/Project/CTV/Examples/Defs.lean`, verdicts in `tests/cerberus/TVExamples.lean` | 14 kernel-checked verdicts, positive and negative; interpreted negative checks in `tests/cerberus/TVValidate.lean` |

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

## Roadmap to a full C translation-validation toolkit

Each stage is a reviewed pull request with its own scope. Caveats of the current stage are
listed with the stage that addresses them.

1. **Foundations** (this stage). Done: as above.
2. **Program corpus and stage artifacts.** *Started*: [`examples/c-programs`](../../examples/c-programs/README.md)
   (16 programs, every artifact with provenance and SHA-256; `ctv-pipeline`; Clang route vs
   Cerberus route cross-validated through the same elaborator where both elaborate: 3 programs,
   compiled evidence; `make c-tv-check`). Remaining: C programs with their exact source, preprocessed text,
   Clang JSON AST, Cabs/Ail/typed Ail/Core from the Lean frontend and from the Clang route, each
   with provenance (source SHA-256, compiler and version, options, target, language); records
   (`silmaril/c-tv/*.toml`) with instances of the shapes and `@[solves]` theorems, so the
   explorer associates evidence by the exact statement checked by `sil project check`, not by a
   theorem's name. Includes Clang-route vs Cerberus-route Core equivalence where both frontends
   accept the program, and explicit rejections (asm labels, attributes, unsupported constructs
   are preserved as named errors, never normalized away).
3. **Explorer: C programs tab.** *Started*: `views/c.js` with data from `tools/c-pages` (`make pages`):
   the corpus with every stage, its producer, SHA-256 checked in the browser and evidence tag;
   the C TV theorems listed **from their statements** (a theorem is never matched by its name);
   the profile coherence tables; browser test `tests/explore/c.mjs`, including the negative
   association checks (a decoy theorem, no theorem on a corpus program). Remaining: Source, Clang AST JSON, Ail, Core and the translations with
   their trust tags, models and profile; source links pinned to a commit; browser tests including
   negative association tests (a theorem about another program or profile is not shown as
   evidence).
4. **GCC torture manifest.** GCC 14.3.0 (`c9cd41fb`), all 3,852 files of
   `gcc.c-torture/{compile,execute}` with SHA-256s (GPL-3.0-or-later tests stay in the pinned GCC
   checkout; only the manifest is stored); per test a status among *not attempted*, *outside the
   supported profile* (with the construct), *frontend rejected*, *validator unknown* (bound),
   *validator unsupported* (gap), *validated*, *refuted*, *timeout*, *UB-dependent test*
   (tests that rely on undefined or implementation-specific behaviour), with the denominator
   always 3,852. Execution comparisons against GCC/Clang binaries are sanity checks and are
   reported separately from validation.
5. **Compositional evidence.** Statements for expressions, statements and functions in
   contexts (evaluation contexts of Core, the function's caller and its external calls under
   contracts), composed into whole-program statements, instead of one monolithic equality;
   connect to the existing function-level shapes (`c.elaborates_to`, `c.ir_refines`,
   `c.compiles_to*`) through adapters.
6. **Upstream comparison.** Differential runs of OathTech/cerberus-lean and of the OCaml
   Cerberus on the corpus, reported as oracle evidence with exact revisions.

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
* **Kernel evaluation under the module system.** The example verdicts are computed by `cbv` in a
  non-`module` test file: in a `module` the same `cbv` runs did not finish within minutes (with the
  `cbv_eval` equations and `import all` of the String modules the compiles-to proofs use), while
  each takes seconds outside one. Rows in the project database (stage 2) need them in a module, so
  this has to be resolved (or the rows built in a non-module library) first.
* **Validator soundness for the full toolkit.** Each new validator lands with its soundness
  theorem and negative tests; native (compiled) evaluation of a validator is tagged `compiled`,
  never presented as a kernel fact.
