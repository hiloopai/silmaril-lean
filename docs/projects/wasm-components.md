# Wasm components: wasm-tools components, jco, WAC, WIT and the generator API

The second part of the Wasm tooling. It adds the WebAssembly component model to the Lean
`wasm-tools`, Lean versions of jco (`wasm-jco`) and WAC (`wasm-wac`), a WIT tool, the
command-line specification API, and the program generator API. The core `wasm-tools` and the
Binaryen tooling are described in [wasm-binaryen-tooling.md](wasm-binaryen-tooling.md) and
[wasm-tools-trust.md](wasm-tools-trust.md).

## What ships

| Part | Modules | What it is |
| --- | --- | --- |
| Component model | `Silmaril.Wasm.Component` | the component binary codec behind one facade (`Codec`: `mvp`, `strict`, `async` and `lax` variants, with `mvp ⊆ lax` and `strict ⊆ lax` proved), the validator (proved sound), the canonical ABI, a reference component machine, resources, streams and futures |
| WIT | `Silmaril.Wasm.Wit` | WIT text and binary packages: parser, printer, elaboration and the custom-section encoding |
| jco | `Silmaril.Wasm.Jco`, `Silmaril.Wasm.JcoTool` | the transpilation of components to core modules and JavaScript glue, with the stream stack |
| WAC | `Silmaril.Wasm.Wac` | the WAC composition language: text, resolution and composition of components |
| Perf | `Silmaril.Wasm.Perf` | fast paths (validator, decoder, encoder, printer) used through `@[csimp]`; each states its equation with the verified version in `Thms` |
| Versions | `Silmaril.Wasm.Versions` | Wasm 1.0, 2.0 and Lime1 models with translations to Core 3.0 |
| CLI spec | `Silmaril.Cli.Spec.WasmTools`, `.Jco`, `.Wac`, `Silmaril.Cli.Clap` | the command lines as values, with derived help and usage errors |
| Generators | `Silmaril.Wasm.Tools.Gen` | `Gen.API` (core-only interface), per-model kits, the generators, mutators and shrinkers of `smith`, `mutate`, `shrink` and `wit-smith` |
| SpecTec | `Silmaril.Wasm.SpecTec` | the SpecTec headers that need the modules above: institution chains between 2.0 and 3.0, the remaining Sim10/Sim20 halves, `BinaryAgree`, the Lime1 grammar and simulations |

## Tools

| Executable | Source | What it does |
| --- | --- | --- |
| `wasm-tools` | `tools/wasm-tools` | the full build: the core subcommands plus `component new/wit/embed/targets/unbundle/semver-check`, `compose`, `smith`, `mutate`, `shrink`, `wit-smith`; every command line is read through `Silmaril.Cli.Spec.WasmTools.tool` |
| `wasm-tools-gen` | `tools/wasm-tools` | the generator subcommands alone |
| `wasm-tools-gen-check` | `tools/wasm-tools-gen-check` | measures how often each checked generator or mutator falls back |
| `wasm-jco` | `tools/wasm-jco` | a jco 1.39.0 work-alike (`transpile`, `new`, `wit`, `embed`, …) |
| `wasm-wac` | `tools/wasm-wac` | a WAC 0.12.0 work-alike (`compose`, `plug`, `parse`, `resolve`) |
| `wasm-wit` | `tools/wasm-wit` | WIT text and package tools |
| `wasm-perf` | `tools/wasm-perf` | runs the fast paths on inputs, for benchmarks |
| `cli-spec`, `cli-harness`, `cli-demo` | `tools/cli-*` | print and test the CLI specifications; a small demo program |

Build them with Lake:

```sh
lake build wasm-tools wasm-tools-gen wasm-tools-gen-check wasm-jco wasm-wac wasm-wit wasm-perf cli-spec cli-harness cli-demo
.lake/build/bin/wasm-tools component wit some-component.wasm
.lake/build/bin/wasm-jco transpile some-component.wasm -o out
```

## The `wasm-tools` command line, specified

The command line of `wasm-tools` 1.262.0 is a value: an argument grammar in the clap dialect
(`Silmaril.Cli.Spec.WasmTools.tool`) with every subcommand, option, positional argument, value
check and `requires`/`conflicts_with` rule of upstream. The executable reads every command line
with it before anything else.

- **Reading.** The clap pre-pass, then the argument parser proved sound and complete for the
  grammar, then the value checks and rules. When the pre-pass passes, the clap reading is proved
  to agree with the generic front end (`read_agrees`). The program reads as the spec
  (`WasmTools.toolAt_read`).
- **Help and errors are derived.** The `-h` and `--help` texts of every command path and every
  usage error are rendered from the grammar in clap 4.6's layout, byte-identical to upstream's
  on all 29 command paths at 100 and 80 columns and on 1096 of 1098 tested command lines (the 2
  others differ in the order in which upstream checks values).
- **Layout facts, proved.** Wrapping only inserts line breaks and indentation and drops trailing
  white space (`wrap_erase`); help and the version go to stdout and every usage error to stderr
  (`Tool.text_channel`); an error text starts with `error: `.

Where the layout puts its line breaks, and clap's wording, are tested against the pinned
binary, not proved.

## Program generators, mutators and shrinkers

`smith`, `mutate`, `shrink`, `wit-smith` and `wasm-tools-gen-check` are instances of one small
interface, `Silmaril.Wasm.Tools.Gen.API`, which needs only Lean's core library.

| Object | Meaning |
|---|---|
| `Rng`, `Rand` | SplitMix64, a splittable 64-bit generator, and seeded computations over it |
| `Lang`, `DecLang` | syntax with a validity predicate; a language with a Boolean checker proved equivalent to validity |
| `Generator L` | from a seed and a size, a program; every output is valid |
| `Mutator L` | a seeded rewrite that preserves validity |
| `SemMutator L Eqv` | a mutator whose output is `Eqv`-equivalent to its valid input |
| `Shrinker S` | a size and a candidate list; `Shrinker.shrink p x` greedily takes the first strictly smaller candidate satisfying `p`, and terminates |
| `ByteGen L`, `PMutator L` | the byte-seeded shapes of `wasm-tools smith` and `wasm-tools mutate` |

`Generator.guarded`, `Mutator.guarded` and `SemMutator.guarded` turn an unverified generator or
rewrite into a verified one: an output is kept when the checker accepts it, and replaced by a
valid default otherwise. The laws (`Gen.API.Thms`): checked shrinking keeps the predicate and
validity, never grows the input and ends in a local minimum.

`Silmaril.Wasm.Tools.Gen.Model` has a kit (checker, generator, mutator, shrinker) per model:
`kit10`, `kit20`, `kit30`, `kitLime1`, `kitFX`, and `coreKitT`/`kitFXT` whose generators are
valid by construction. `Gen.Comp` generates components and `Gen.Wit` WIT packages.

Trust boundary: the raw generators and mutators are unverified; validity comes from the checker
(a fast Core validator proved equal to the verified one) or from typing by construction. The
component validator is proved sound, not complete, so a checked component generator may fall
back where upstream would accept.

## Known limitations

- **Frozen statements.** Some results are stated as `def Task.x : Prop` and used only as
  hypotheses. Nothing unconditional depends on them. For the components and WIT:
  `Task.check_complete` (`Proofs/Wasm/Wit/Tool/Complete`), `Task.refToSpecFXE`,
  `Task.coreFraming_of_decode`; for the asyncify link to Core 3.0 (`FX/Asyncify/Tool`):
  `Task.machine_core`, `Task.fits`. For the CLI:
  `WasmTools.SpecThms.Task.*_agree` and `Wast.Spec.Task.*_agree` (the older core readers agree
  with the specification; tested on records with 0 differences). The SpecTec modules add
  `Task.composite*`, `Task.swapStep*`, `Task.unstripStep*` and a few others, described in
  [the SpecTec guide](spectec/README.md).
- **Raw modules.** About 200 modules under `Silmaril/Raw/Wasm/{Component,Versions,…}` hold
  valid but unrefined proofs, about 1,350 theorems of the component model among them. Headers
  re-export the parts other topics use.
- **Partial definitions.** `Tools/Component/Layout`, `Tools/Component/Typed`, `Wac/Text/Json`,
  `Wit/Binary/Print` and `wasm-tools-gen-check` still contain `partial def`s.
- **Upstream parity is tested, not proved.** The suites under `tools/wasm-tools/tests/
  {component,compval,gen}`, `tools/wasm-jco/tests`, `tools/cli-spec/tests` and
  `tools/cli-harness/tests` compare against pinned upstream binaries (wasm-tools 1.262.0,
  jco 1.39.0, wac 0.12.0, wasmtime 50.0.0) and skip when those are not installed; CI does not
  run them. Some read component fixtures that are not part of this repository yet. Last full
  run before release: jco suite 442 passed and 0 failed; the component validator agreed with
  upstream on 1896 of 1919 corpus components (13 valid ones rejected, 10 invalid ones
  accepted); `component new` agreed on 78 cases, both refused 15 and 22 differed; the CLI texts
  1096/1098.
- **Not implemented:** `wit-dylib` and `component link` report `not implemented in this build`.
