# wasm-tools in Lean

`wasm-tools` here is a Lean program that reproduces the command line of
[bytecodealliance/wasm-tools](https://github.com/bytecodealliance/wasm-tools) 1.262.0 for its
core subcommands. The core of each command is a pure Lean function with a theorem about it.
Agreement with upstream is **tested** against the pinned upstream release; it is not proved.

This release covers the core subcommands. The component subcommands (`component …`,
`compose`) and the generators (`smith`, `mutate`, `shrink`, `wit-smith`, `wit-dylib`) are not
part of it. Like any upstream subcommand this build lacks, they print
`error: wasm-tools NAME: not implemented in this build` and exit with status 1.

## Install

You need the Lean toolchain named in `lean-toolchain` (install it with
[elan](https://github.com/leanprover/elan)) and a C toolchain for linking.

```sh
lake build wasm-tools
.lake/build/bin/wasm-tools --version     # wasm-tools 1.262.0 (lean)
```

The binary has no runtime dependencies beyond the C library. Its version line names this
build instead of upstream's commit. The command line matches upstream 1.262.0: the same
subcommands, options, help texts, error messages and exit statuses (0 success, 1 failure,
2 usage error).

## What it does

| Subcommand | State | Main theorems | Tested against 1.262.0 |
| --- | --- | --- | --- |
| `parse` (`wat2wasm`) | Core modules in the Wasm 3.0 model; upstream's binary layout, `name`, `@custom`, `@producers` | `textToBinary_sound`, `Layout.relayout_sound`; fast path `watToBinaryFast_eq` | byte-identical on 2,717 of 2,843 corpus files; the other 126 use proposals outside the model and are rejected |
| `print` (`wasm2wat`) | wasmprinter's format, every flag except `--print-operand-stack`, colours | `printModule_sound`, `print_parse_roundtrip`; fast path `binaryToWatWithFast_eq`; `colorText_spec` | byte-identical on the same 2,717 files for each of 11 flag sets |
| `validate` | Core modules, all features of the model; components partly | `check_ok_iff` (equal to the specification validator); fast path `checkFast_eq`; components `check_core` | 7,874 of 7,874 modules; components 1,728 of 1,919 |
| `strip`, `objdump` | Done | `strip_module*`, `Regex.search_iff`, `objdump_ranges`, `stripFast_eq`, `objdumpFast_eq` | byte-identical on 7,874 modules and 101 components |
| `dump` | Done | `dExpr_erase`, `dump_tiles` | byte-identical on 10,292 of 10,292 binaries |
| `metadata show`, `metadata add` | Done, including `.dep-v0`; a subset of URL syntax | `parseBinaryB_spec`, `payloadOfB_spec`, `addMetadataB_spec`, round trips | 503 of 503 cases; 1,478 malformed inputs identical (upstream panics on 22 more) |
| `demangle` | Rust (v0 and legacy) and C++ (Itanium) | `demangle_ok`, `demangleB_spec` (the section rewrite) | Rust 943 of 943, libc++ 4,191 of 4,191, 20,000 of 20,000 mutated symbols |
| `addr2line` | DWARF versions 2 to 5, line tables | `specialRegs_spec`, `binarySearch_spec` | 9,605 of 9,605 addresses |
| `json-from-wast` (`wast2json`) | Core text done; component text partly | `Script.read_print`, `read_sound`, `checkedCore_sound` | spec scripts: JSON 67 of 67, written modules 2,134 of 2,135 |
| `wast` | Checks scripts short of running them | `checkDirective_spec`, `checkScriptPure_spec`, `reencode_sound` | 66 of 67 spec scripts |
| `completion` | Done; the scripts are upstream's, captured | — | 5 of 5 shells |
| `help`, `-h`, `--help`, `-V`, unknown subcommands | Done, including clap's "similar subcommand" tips | `didYouMeanAll_mem`, the argument-grammar laws | every captured case |

The test counts were measured on 2026-11-10 with the suites below. The corpus is upstream's
test and snapshot files, the WebAssembly specification test suite at a pinned revision,
DWARF samples compiled with a pinned wasi-sdk, and further binaries of the development tree.
Not all of the latter are distributed, so a rerun from this repository covers most, but not
all, of those counts.

## Known limitations

- **Proposals outside the model.** The Lean model of Wasm covers Wasm 3.0. Inputs that use
  threads, wide arithmetic, custom descriptors, custom page sizes, compact imports or
  stack-switching are rejected where upstream accepts them.
- **Component support is partial.** `validate` checks components with a tested
  transcription of wasmparser's component rules. Only the core-module parts are proved
  (`check_core`), and 191 of 1,919 corpus components disagree. `json-from-wast` and `wast`
  read only part of the component text format.
- **Error messages.** `validate` reproduces whether a module is valid, not wasmparser's
  error texts. SPDX expression errors in `metadata add` lack upstream's caret line.
- **Refused options.** `print --print-operand-stack` and `parse -g`/`--generate-dwarf`
  print an error instead of running.
- **Speed.** `parse`, `print` and `wast` are 10 to 50 times slower than upstream on inputs
  above about 100 KB. The certified lexer runs sequentially.
- **Re-encoding.** LEB128 integers are re-encoded at minimal width, as wasm-encoder does, so
  an input with padded integers re-encodes to different bytes.
- **`help CMD NAME`** for a command without subcommands differs from clap's message.

## Trust boundary

The claim is a **verified core with an explicit trust boundary**. It does not say that every
function is verified. The full statement is in [the trust statement](../../docs/projects/wasm-tools-trust.md).
In short:

- **Proved.** Each subcommand's pure core meets the theorem named in the table above. The
  binary runs those functions, or fast variants proved equal to them.
- **Tested, not proved.** Byte-for-byte agreement with upstream. Decoder completeness:
  `parse` and `print` are sound, but it is not proved that every binary upstream accepts is
  decoded. The component validation rules, the demanglers, the DWARF reader, and the text of
  each `dump` line.
- **Not verified.** The `partial def`s are listed in the trust statement; they have no
  termination proof, so no theorem can unfold them. The rest is glue under `tools/wasm-tools`:
  argument dispatch, file and stream input/output, exit codes, and captured help texts.
- **Trusted.** As for any Lean program: Lean's kernel, compiler and runtime, and the C
  toolchain that links the binary.

No module of this tool uses `sorry`, declares an axiom, or trusts compiled code in a proof.

## Tests

The fast suites need no upstream binary and run in about five seconds:

```sh
python3 -I tools/wasm-tools/test-cli.py [BINARY]   # default .lake/build/bin/wasm-tools
```

They replay 315 recorded command lines (help, the argument grammar of every subcommand,
top-level behaviour) and compare stdout, stderr and the exit status with the outcomes
recorded from upstream. Known differences are listed in the golden files with a reason.

The differential suites compare this binary with the pinned upstream release on corpora.
They take minutes to hours, so they are opt-in. Every script skips with a message, and exit
status 0, when its pinned inputs are absent:

```sh
tools/wasm-tools/tests/fetch-pins.sh wasm-tools spec   # downloads, checks SHA-256, unpacks
tools/wasm-tools/tests/differential.sh --quick         # all suites on a sample
tools/wasm-tools/tests/differential.sh validate dump   # selected suites in full
```

`tools/wasm-tools/tests/pins.sh` is the one place that names the pinned versions, their URLs
and their SHA-256 sums: wasm-tools 1.262.0, its source archive, the specification test suite,
and wasi-sdk 27.0 for the DWARF samples. Downloads go into a cache directory, are checked
against the sums before anything is unpacked, and only the released binaries are run. The
suites are listed in [tests/README.md](tests/README.md).

## Layout

- `WasmTools.lean`: the entry point and subcommand dispatch. `WasmTools/` holds the
  subcommand groups and the input/output glue.
- `tests/`: golden suites, differential scripts, pins, and the generators that regenerate
  the captured upstream data (help texts, completion scripts, operator tables, SPDX
  identifiers) from the pinned source.
- The Lean library is under `Wasm/Tools/<Topic>/{Defs,Thms}.lean`, with proofs under
  `Proofs/Wasm/Tools`. It builds on the Wasm 3.0 model, decoder, validator and text format of
  this repository.

Material derived from wasm-tools (help texts, completion scripts, operator tables, test data)
is listed in `NOTICES/wasm-tools`.
