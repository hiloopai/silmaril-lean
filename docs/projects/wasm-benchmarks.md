# Wasm tool benchmarks

[Reproduce the measurement](#reproduce) · [Per-fixture results](../benchmarks/wasm-v133-2026-10-25.json) · [Wasm guide](wasm.md)

These measurements compare native executables with Binaryen **version_133** on
original upstream module inputs. They measure accepted input, independently
validated output, elapsed process time and output bytes. They do not run WAST
assertions or compare behavior, expected text, pass implementations or
optimization quality.

## Measured sample

Measured on 25 October 2026, Linux x86-64, Intel Core i7-8700. The tested Silmaril
binaries were built from `fa138030d91c0985b18c1e708aaa664c2bccd1a9`, before the
repository layout change. The JSON records every executable's SHA256 and the
harness hash. That pre-release revision is outside this repository's initial
history. These numbers are a baseline for that build; rerun after rebuilding.

| Command | Valid outputs / upstream-valid inputs | Paired inputs | Silmaril time | Binaryen time | Silmaril / Binaryen output bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| `wasm-as` | 17 / 24 | 17 | 1,452 ms | 68 ms | 2,083 / 1,904 |
| `wasm-dis` | 20 / 22 | 20 | 2,063 ms | 80 ms | 473,764 / 1,001,231 |
| `wasm-opt` without passes | 19 / 22 | 19 | 1,607 ms | 87 ms | 83,868 / 156,460 |
| `wasm-opt -O2` | 19 / 22 | 19 | 2,633 ms | 843 ms | 86,065 / 148,131 |
| `wasm-opt -O3` | 19 / 22 | 19 | 2,621 ms | 1,371 ms | 86,065 / 147,705 |
| `wasm-merge` | 13 / 21 | 13 | 1,366 ms | 97 ms | 804 / 877 |

**Time and byte totals use only inputs for which both tools produced valid
outputs.** Each time is the sum of per-input medians, with three measured fresh
processes after one warmup. Timing includes startup and file IO; validation runs
outside the timed region. Runs alternate implementation order. Both thread
settings are one. Small Silmaril invocations took roughly 80 ms on this host;
startup is a substantial part of these measurements.

This was a shared host: its one-minute load average ranged from 9.52 to 11.09
on 12 logical CPUs. These are reproducible procedures and recorded observations,
not stable performance guarantees. Compare fresh builds on an idle machine before
attributing differences to individual passes.

Text sizes reflect formatting and name/custom-section policy. Binary sizes also
reflect encoding and retained metadata. In particular, a smaller no-pass output
is not evidence of a better optimizer; the `-O2` and `-O3` implementations run
different pass pipelines. See the [tool contracts](wasm.md).

## Input selection and remaining gaps

- The scanner found **4,021** top-level text modules and binary fixtures at the
  pinned upstream commit. It does not execute script assertions, shell directives
  or invalid modules nested inside assertions.
- A 256 KiB limit excluded six inputs. The scanner rejected one malformed source
  file. It then chose 24 text modules and 24 modules/binaries at evenly spaced
  ranks by input size, **before running either implementation**. Rejected inputs
  were not replaced.
- All 24 assembly inputs passed upstream preparation. Two inputs from the other
  sample failed upstream preparation: an intentionally rejected component file
  and an invalid `publish` instruction. The remaining 22 form the shared
  disassembly/optimizer sample.
- Merge uses all 21 positive recipes accepted by the harness's restricted recipe
  grammar in `test/lit/merge`. It preserves source order, namespaces and conflict
  policies, assembles each input with upstream, and requests binary output.
  Four metadata/debug/source-map recipes are explicitly excluded. Negative tests
  and golden text checks are not run.
- Every retained successful output was validated by upstream `wasm-opt --all-features`.
  Disassembly output was first reassembled by upstream `wasm-as`. No candidate
  output failed those checks; some candidate commands rejected inputs.

The seven assembly rejections include atomic/thread syntax, continuations,
legacy exceptions, descriptor/reference constructs and one validation rejection.
Disassembly rejects the selected descriptor/shared-type cases. Optimization
also rejects a shared-memory encoding. Merge rejects eight recipes involving
unsupported import/type encodings, stateful linking or legacy exceptions. The
JSON includes the exact input IDs, hashes and error messages for each result.
These sample counts cannot estimate whole-suite acceptance percentages.

`wasm-shell` is not compared because its binary invocation interface differs
from upstream's WAST script runner. `wasm-ctor-eval` and `wasm-metadce` have
narrower transformation contracts and need separately aligned constructor/root
graph jobs. The [seven-tool demo](wasm.md) checks their actual supported behavior;
this benchmark does not assign them a misleading upstream speed ratio.

## Reproduce

Requirements: Python 3.11 or newer, CMake, a C++ toolchain, built Silmaril tools,
and Git. Node is used by the separate execution tests, not this benchmark.
The benchmark uses only Python's standard library.

From the Silmaril repository root:

```sh
make tools

git clone https://github.com/WebAssembly/binaryen.git build/reference/binaryen
git -C build/reference/binaryen checkout fba5005a132d85d578be5bd010e0487ed8e2ce3e
cmake -S build/reference/binaryen -B build/reference/binaryen-build \
  -DCMAKE_BUILD_TYPE=Release -DBUILD_TESTS=OFF
cmake --build build/reference/binaryen-build --parallel 4 \
  --target wasm-as wasm-dis wasm-opt wasm-merge

python3 tools/binaryen-lean/benchmark-native.py \
  --candidate-bin build/bin \
  --candidate-revision "$(git rev-parse HEAD)" \
  --reference-bin build/reference/binaryen-build/bin \
  --upstream build/reference/binaryen \
  --work build/wasm-benchmark \
  --report build/wasm-benchmark.json
```

Build first, then pass the revision that was actually compiled. The harness
checks the upstream revision, clean fixture tree and v133 executable versions;
it records hashes of the supplied binaries. It does not infer source identity
from a binary or establish a reproducible native build.

Use `--samples 0 --max-bytes 0 --repeats 1` to measure every scanned module input,
or `--tools as dis` for the codec pair. Full enumeration is much slower and still
is not the complete upstream test suite. The default per-process timeout is ten
seconds; timeouts and rejections remain in the report. A nonzero harness exit
indicates invalid or missing successful output, or a setup failure; ordinary
unsupported-input rejections are recorded measurements.
