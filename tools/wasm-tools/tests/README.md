# Tests of `tools/wasm-tools`

Two layers: a fast golden check that needs only our binary, and opt-in differential suites
against the pinned upstream wasm-tools 1.262.0 and its corpora.

## Fast check (no upstream binary)

```sh
python3 -I tools/wasm-tools/test-cli.py [--suite NAME]... [--verbose] [.lake/build/bin/wasm-tools]
```

Runs the golden suites `golden/*.json` (about 300 command lines, a few seconds): each case
is a command line, run in a fresh directory holding the suite's fixtures (`fixtures/`), with
the outcome upstream gave for it: exit status, stdout, the SHA-256 of every file the command
wrote, and stderr as far as the suite's mode compares it (`exact`, `exact-unless-1`: only the
first word when the command failed with status 1, `error-word`, `empty-or-not`). A case may
name a fixture as its stdin. Cases marked `known` (with the reason) are reported and do not
fail the run. Exit status 0 when every other case agrees; it skips without our binary.

| Suite | Covers |
| --- | --- |
| `top-level` | no arguments, `-h`, `--help`, `-V`, unknown subcommands and clap's tips, aliases, `help NAME` |
| `help` | `-h`, `--help` and `help NAME` of every subcommand of the release, nested `help` of `metadata` |
| `validate-args` | `validate`, `strip`, `objdump`: option forms, feature flags, errors, `-o` |
| `parse-print-args` | `parse`, `print`, `completion`: clusters, `=`, `--`, colours, errors, `-o` |
| `meta-args` | `demangle`, `metadata`, `addr2line`, `dump` on small inputs; every input reader on stdin |
| `wast-args` | `json-from-wast` and `wast`: options, written files, assertion modes |

`golden-capture.sh [SUITE]...` re-records the outcomes from the pinned upstream binary (its
SHA-256 checked first). To add a case, add it to the suite's `cases` and re-record; review the
diff of `golden/` before committing it.

## Pins

`pins.sh` is the only place that names the tool cache (`$SIL_TOOLS`), the pinned versions,
URLs and SHA-256 sums; every script sources it. `fetch-pins.sh` installs them:

```sh
tools/wasm-tools/tests/fetch-pins.sh                    # wasm-tools 1.262.0, its source, the spec testsuite, the WASI adapters
tools/wasm-tools/tests/fetch-pins.sh binaryen wasi-sdk  # Binaryen version_123, wasi-sdk 27.0
tools/wasm-tools/tests/fetch-pins.sh --check wasm-tools src spec adapters binaryen wasi-sdk
```

| Pin | Archive SHA-256 | Checked file |
| --- | --- | --- |
| wasm-tools 1.262.0 x86_64-linux release | `655b8df6…a9ed65` | `wasm-tools` `fe6a056d…acb211` |
| wasm-tools 1.262.0 source (tag archive) | `8fafe356…5f101c` | data only |
| WebAssembly/spec `608711107b` (`test/core`) | `22ef0dd9…a1b` | data only |
| wasmtime v50.0.1 WASI preview1 adapters (`command`, `reactor`) | — | `0b4fe490…a3c4`, `6d52112d…671f` (data only) |
| Binaryen version_123 x86_64-linux | `e959f217…88fe` | `bin/wasm-opt` `d66c6724…9c4a` |
| wasi-sdk 27.0 x86_64-linux | `b7d4d944…bc2` | `bin/clang-20` `e78c818b…be77` |

Downloads go to a fresh empty directory and are checked before anything is unpacked; only the
released binaries are run, the source archives are read as data.

## Corpus

The suites read no file outside `tools/`: the spec testsuite and the adapters come from the
pins, and the other binaries are vendored in `corpus/` (WIT packages, WASI 0.3 components and
tiny modules; provenance in `corpus/README.md`, digests in `corpus/SHA256SUMS`, checked by
`wt_corpus_check` before a suite runs). `wt_corpus_wasm` (pins.sh) lists the binaries of the
`validate` and `dump` suites: `corpus/`, `fixtures/`, the adapters and the test inputs of
`tools/wasm-check` and `tools/wasm-egraph`. The 3.1 MB debug build of `corpus/cat.wasm`
is not vendored: set `WT_CAT_DEBUG` to it (SHA-256 pinned in `pins.sh`) to add it to
`meta-differential.sh`, `addr2line/differential.sh` and the benchmarks; without it those cases
are skipped and say so.

## Differential suites (opt-in)

```sh
tools/wasm-tools/tests/differential.sh [--quick] [SUITE]...
```

runs, and summarizes, the suites below; each skips (status 0) without its pins. They take
minutes to hours and are not part of the fast check.

| Suite | Script | Compares |
| --- | --- | --- |
| `golden` | `golden-capture.py` into a scratch copy | every recorded golden outcome still reproduces |
| `validate` | `diff.sh [--quick] [--sweep]` | `validate` (per feature group with `--sweep`), `objdump`, `strip`, `strip -a` on the spec testsuite and the corpus binaries (`wt_corpus_wasm`); baseline `known-diffs.txt` |
| `dump` | `dump-diff.sh` | `dump` byte for byte; bound `dump-baseline.txt` |
| `parse-print` | `parse-print.sh` | `parse`/`print` on upstream's printer snapshots; print certification |
| `meta` | `meta-differential.sh` | `demangle`, `metadata show`/`add`, demangler corpora (`symbols/`) |
| `meta-malformed` | `meta-malformed.sh` | error messages of `metadata show` and `demangle` on mutated binaries |
| `addr2line` | `addr2line/differential.sh` | `addr2line` on DWARF 4/5 samples (wasi-sdk) and, with `WT_CAT_DEBUG`, a Rust component |
| `wast` | `wast/differential.sh DIR` | `json-from-wast` (stdout and written files) and `wast` |

Benchmarks with regression baselines: `bench.sh` (`bench-baseline.tsv`), `pp-bench.sh`
(`pp-bench-baseline.tsv`), `meta-bench.sh`, `wast/bench.sh`. Component suites
(`comp-diff.sh`, `wast/components.sh`) belong to the component commands.

## Generators

The verbatim upstream data in the sources is regenerated from the pins: `capture-help.sh` and
`gen-help.py` (help texts of the meta subcommands), `gen-help.sh` (`WasmTools/Help.lean`), `gen-helpv.py` (the definitions of `WasmTools/HelpV.lean`),
`gen-completion.sh`, `gen-op-table.py`, `gen-ops.py`, `gen-arity.py` (operator tables from the
wasmparser and wast sources), `gen-spdx.py` (SPDX identifiers), `gen-rust-ranges.py`.
