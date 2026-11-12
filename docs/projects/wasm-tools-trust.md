# `wasm-tools` in Lean: what is verified, and what is trusted

Draft of the public trust statement of the core `wasm-tools` CLI (wave 1: every subcommand
but `component`, `compose` and the generators). Decision to confirm: the claim is a
**verified core with an explicit trust boundary**, not "every function verified".

## The claim

Each subcommand's core is a pure Lean function with a specification theorem, checked by
Lean's kernel. The binary runs those functions (or fast variants proved equal to them).
Byte-for-byte agreement with upstream wasm-tools 1.262.0 is **tested**, not proved: the
fast golden suites (`tools/wasm-tools/test-cli.py`) on every build, the corpus
differentials (`tools/wasm-tools/tests/differential.sh`) on demand.

| Subcommand | Proved | Tested only |
| --- | --- | --- |
| `validate` (core modules) | equal to the specification validator (`check_ok_iff`), fast path `checkFast_eq` | wasmparser's error texts (only the class is matched) |
| `validate` (components) | the core-module parts (`check_core`) | the component rules: a tested transcription |
| `parse` | sound: the output encodes the module the text denotes (`textToBinary_sound`, `Layout.relayout_sound`), fast path `watToBinaryFast_eq` | the binary layout is upstream's |
| `print` | sound: the text parses back to the module (`printModule_sound`, `print_parse_roundtrip`), fast path `binaryToWatWithFast_eq`, colours `colorText_spec` | wasmprinter's exact formatting |
| `strip`, `objdump` | `strip_module*`, `Regex.search_iff`, `objdump_ranges`, `stripFast_eq`, `objdumpFast_eq` | — |
| `dump` | `dExpr_erase`, `dump_tiles` | the text of each line |
| `metadata show` / `add` | `parseBinaryB_spec`, `payloadOfB_spec`, `addMetadataB_spec`, round trips | the SPDX and URL checks |
| `demangle` | `demangle_ok`, `demangleB_spec` (the section rewrite) | the demanglers against a grammar |
| `addr2line` | `specialRegs_spec`, `binarySearch_spec` | the DWARF line programme reader |
| `json-from-wast`, `wast` | `Script.read_print`, `read_sound`, `checkedCore_sound`, `checkDirective_spec`, `checkScriptPure_spec`, `reencode_sound` | component text, error-message matching |
| argument grammar | the laws of `Cli/Thms` | the rendering of clap's messages |
| `completion` | — | the scripts are captured upstream data |

## The trust boundary

Trusted, as for any Lean program: Lean's kernel, its compiler and runtime (the binary is
compiled code; code generation is not verified), the C toolchain that links it, and the
`@[csimp]` lemma `printSExp2With_eq_fast` of the S-expression printer (a theorem, so it is
checked; it only redirects compilation).

Not proved, and listed here so that a reader can see where the proofs stop:

**`partial def`s.** None in the executable. Every function of the closure described below,
the component validator, the folded-instruction printer and the component binary checker
included, is a total definition (structural or well-founded recursion), so theorems can unfold
it. The `partial def`s left in the wave-1 sources are not part of `wasm-tools`:

| Module | Functions | Role |
| --- | --- | --- |
| `Wasm/Auto/VCGen/Thms`, `Wasm/Auto/VCGen2/Thms`, `Wasm/Auto2/VCGen/Thms` | `envAtoms` (`meta`) | tactic code of the Auto verification-condition generators, run while proofs elaborate; the kernel checks the proofs it builds |
| `tools/wasm-tools/WasmToolsWastBench` | `syms` | a benchmark driver, not part of `wasm-tools` and not in wave 1 |

**Glue without theorems.** `tools/wasm-tools/**` (about 2,300 lines, of which about 700 are
captured help texts and completion scripts): argument dispatch, reading and writing files,
stdin and stdout, exit codes. `Wasm/Tools/Meta/Main/Defs` (300 lines): the IO layer of
`metadata`, `demangle` and `addr2line`. Topic modules with no `Thms` (definitions used by
tested code only): `Annot`, `CompNames`, `DumpComp`, `DumpFlat`, `OpTable` (generated from
wasmparser), `OptGrammar`, `RustDebug`, `WastEnc` (a transcription of the `wast` crate's
encoder, tested against it).

**Unproved properties of proved functions.** Decoder completeness (every binary upstream
accepts is decoded) is not proved; `parse` and `print` are sound, not complete. Agreement of
output bytes with upstream is a test result, as above.

## What the executable is built from

The wave-1 executable is `tools/wasm-tools/WasmTools.lean` without the `component` and `gen`
subcommand groups (`WasmTools.Component`, `WasmTools.Gen`), built as `wasm-tools-core`. Its
import closure (textual, `mor runtime-closure wasm-tools-core --list`) is 79 project modules,
122 silmaril-lean modules and 19 modules of `tools/wasm-tools` (the root included). Besides
`Silmaril/Wasm/Tools`, the project modules are:

- the component binary format and its text form, used by `validate` on components and by
  `wast` on component directives: `Silmaril/Wasm/Component/{Binary,Binary/Encode,BinaryP3,
  BinaryP3/Encode,BinaryP3/Check,Wat,Wat/Ids,Wat/Sexp}/Defs` and the component text reader
  `Silmaril/Wasm/Wac/WatX/Defs` (8 + 1 modules). They ship in wave 1 as part of the core
  CLI; the `component` subcommands that build on them do not;
- the parser combinators of the component binary decoder: `Silmaril/Parse/ByteParse/Defs` only.
  A `Grammar` there pairs a parser with the relation it implements; the laws (soundness and
  completeness, `Grammar.Lawful`) are instances proved in `Silmaril/Proofs/Parse/ByteParse/*` and
  `Silmaril/Proofs/Wasm/Component/*/Lawful`, which the executable does not import. Those proofs,
  and the round trips of the component codec, belong to the component half of the CLI and are
  not part of wave 1: in wave 1 the component decoder is shipped, and tested, as definitions.

No module of the executable's closure is a proof module (`Proofs`, `Raw` or `Thms`):
`mor runtime-closure` checks this for the four wave-1 executables with an empty baseline.

The WIT modules (`Silmaril/Wasm/Wit/**`) are not in the closure: the component text reader no
longer imports the WIT tool.

## Checked for this draft

- No `sorry`, no `axiom` declaration and no proof by compiled code in `Silmaril/Wasm/Tools`,
  `Silmaril/Proofs/Wasm/Tools`, `Silmaril/Wasm/Models` or `tools/wasm-tools` (textual search). No
  module of `Silmaril/Wasm/Tools` is in `Raw` any more.
- The `partial def`, `unsafe def`, `@[csimp]`, `@[implemented_by]` and `@[extern]` lists
  above are a textual search over the closure described above (for `partial def`, also over
  every Lean file of the wave-1 copy list). No `partial def`, `unsafe def`,
  `@[implemented_by]` or `@[extern]` occurs in the closure; the one `@[csimp]` is in silmaril-lean
  (`Silmaril.Formats.SExp.PrinterChunks`).
- **Axiom audit** (repeatable). The module `scripts/oss-wasm/Wave1AxiomAudit.lean`, generated
  from the wave-1 copy list by `scripts/oss-wasm/gen-axiom-audit.sh`, imports every Lean
  module of the release that a library owns (734 modules: the `wasm-tools` library, the
  Binaryen tooling, their foundations and the tests of `tests/wasm/auto`; the four executable
  roots are command-line glue and cannot be imported). While it elaborates
  (`lake build Wave1AxiomAudit`), it recomputes the axioms of each of their 64,801
  constants (33,282 theorems) from the stored terms, following every constant they
  use into Lean core, Mathlib and silmaril-lean, and fails on any axiom other than `propext`,
  `Classical.choice` and `Quot.sound` (so on `sorryAx`, `Lean.ofReduceBool` from
  native evaluation, `Lean.trustCompiler`, or a project axiom). Result on this draft: no
  non-standard axiom; `propext` is reached by 36,600 constants, `Classical.choice` by 29,563
  and `Quot.sound` by 16,791; every theorem's proof was loaded and walked. The module
  elaborates in about 16 s. It is a library rather than an executable: an executable would
  compile every audited module to C and, when run, evaluate their initializers.
