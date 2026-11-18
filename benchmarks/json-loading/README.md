# JSON loader benchmarks

Run from the repository root with the pinned Lean toolchain, Python 3, GNU `time` and `timeout`:

```sh
make json-loading-check
python3 benchmarks/json-loading/run.py /tmp/silmaril-json-bench --runs 2 --seconds 15
```

The runner generates synthetic fixtures (no large blobs in git), reuses three tracked input
files, writes `results.csv`, and keeps separate process logs and timing files. `--case` limits
it to named fixtures and is repeatable. The processes use one Lean thread, a 4,096 MiB Lean
memory limit, and a 32 MiB Lean thread stack. Each check has a wall-time limit. Kernel query
and agreement probes use `maxRecDepth 8192` and no heartbeat limit; the memory and time limits
still apply. For meaningful comparisons, avoid rebuilding the library during a run.

- **Runtime:** the same Lean `--run` harness reads each file as bytes, then times acceptance
  with `JsonWire.parse?` (the old ordered exact-decimal parser), `Fast.parseBytes`, and
  `Lean.Json.parse`. The last is a useful speed reference, not a compatible replacement: it
  does not expose ordered duplicate members or the same decimal/sign contract. Lean core and
  repository modules need not run through identical machine-code paths in this harness; this
  is not a standalone native executable benchmark.
- **Declare:** new Lean processes write an `.olean` for a source-only Wire or Fast parser
  application (Fast with `silmaril.json.precompute false`) or the default precomputed Fast
  constructor tree. The precomputed logs separate the
  compiled parse and expression emission, and Lean profiles kernel `type checking` and
  `.olean serialization`. External wall time includes startup, IO, elaboration and output.
- **Import:** a fresh Lean process only imports the corresponding `.olean`.
- **Query:** the same import plus one `decide +kernel` proof about a late element, including
  an indexed-versus-linear comparison on the same precomputed object. The list case uses
  chunk routing in both variants. Wall/RSS include the common module load; compare to import
  to approximate the incremental cost.
- **Agreement:** a fresh process checks `SourceMatches` for the complete precomputed result
  on the small and medium inputs against a separate `json_text` definition, not just a field claim.

## Results

November 18, 2026; Linux/x86-64 sandbox, Lean `4.37.0-nightly-2026-11-05`
(`67dafde474f`). Medians of two fresh processes per cell; failures reproduced in both runs.
All runtime parsers accepted the tracked files they completed. The wide case has 42,001
members with a long shared key prefix; the list has 40,001 items; nested has 32 enclosing
objects around 33,000 records. The checker selects a late field/item, not the first one.

| Input | Bytes | Wire parse (ms) | Lean.Json parse (ms) | Fast parse (ms) |
| --- | ---: | ---: | ---: | ---: |
| Small | 442 | 1.02 | 0.064 | 0.51 |
| Medium | 35,686 | 121 | 0.40 | 20.2 |
| Wide | 2,772,046 | timeout | 27.2 | 1,516 |
| List | 3,280,007 | timeout | 16.8 | 1,473 |
| Nested | 2,959,906 | timeout | 33.4 | 1,807 |
| Tracked OCI manifest | 219 | 0.92 | 0.048 | 0.52 |
| Tracked litmus corpus | 116,688 | 5,803 | 1.92 | 75.7 |
| Tracked litmus metadata | 232,566 | timeout | 3.36 | 132 |

Fast completed the multi-MiB parses in 2.1–2.5 s wall, at 2,269–2,285 MiB process peak RSS
(about 2,207 MiB for the small input including the Lean environment). Wire hit the 15 s wall
limit on those three cases, not a measured completion time. On the medium fixture Fast was
6× faster than Wire by parse time. Core `Lean.Json` was substantially faster than both on
these inputs but does not implement the same API/semantics. In a wide-fixture pilot, Lean's
array quicksort took the Fast parser to about 13 s; the stable merge sort brought the same
parse to about 1.5 s, with insertion order retained within hash collisions.

| Input | Precomputed build wall (s) | `.olean` source / precomputed (MiB) | Import precomputed (s) | Wire / source kernel query (s) | Precomputed indexed / linear query (s) |
| --- | ---: | ---: | ---: | --- | --- |
| Small | 0.62 | 0.005 / 0.008 | 0.52 | no reduction / 0.71 | 0.54 / 0.55 |
| Medium | 0.57 | 0.038 / 0.49 | 0.53 | memory / no reduction | 0.56 / 3.51 |
| Wide | 3.98 | 2.65 / 36.69 | 0.50 | memory / memory | 0.55 / memory |
| List | 2.17 | 3.13 / 12.85 | 0.54 | memory / memory | 0.54 / 0.52 |
| Nested | 9.90 | 2.83 / 26.67 | 0.53 | memory / memory | 0.53 / 0.59 |

The source-only definitions (both parsers) built in roughly 0.5–0.9 s and imported in roughly
0.5 s. Their imports do not evaluate the parser. Precomputation trades larger declarations for
field proofs near the import-only cost. Prepared queries on large inputs peaked at 2,207–2,228
MiB; linear search on the medium object peaked at 3,013 MiB. The large memory failures peaked
near 4,100 MiB. The small Wire query and medium source query reported that `decide` did not
reduce (rather than returning `false`). On the small object there is no hash index to compare.

In the wide precomputed build, median parser/emitter/kernel-type-check/serialization times were
1,514/56/375/1,500 ms. For the list they were 1,469/13/31/103 ms, and for nested
1,807/164/357/6,975 ms. Nested builds ranged from 6.33 to 13.47 s wall, largely serialization
variance. The peak precomputed build RSS on large cases was about 2.4 GiB. Kernel-only full
`SourceMatches` verification took 0.66 s on the small input and exceeded the memory limit on the
medium input. The large selective proof times do **not** include that full certification.

## Follow-up: checked object fragments

`Certificate.lean` and `certificate.py` are a benchmark, not a new import mode. The generator
splits a nonempty top-level object ending in LF on top-level commas. For each fragment the kernel
checks (1) its exact packed UTF-8 spelling and (2) `parseText ("{" ++ fragment ++ "}") = .ok
(Value.ofObject entries)` for the emitted entries. A balanced proof tree joins the fragments with
literal commas and joins the ordered entries with checked lengths. `spells_of_check` uses the
proved `KBytes` comparison to link the rendering, including braces and final LF, byte-for-byte to
an independent embedding of the original. `Spells original result` relates those bytes to the
same unindexed `Value` used by the field proof. The splitter and precomputed values are proposals,
not trusted parser results. The theorem concerns embedded bytes, not the filesystem.

This proves a lossless **compositional object spelling relation**, not `SourceMatches`, and not
equivalence to a monolithic parser run or its hash index. The checked fragments reuse Fast's
existing Unicode and decimal semantics; joins retain every entry in source order. The semantic
test checks a literal/escaped duplicate key across fragments, a surrogate pair, exact decimals,
a nested field, and rejection of an equal-length spelling change (`e` to `E`). The audited
agreement theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

```sh
python3 benchmarks/json-loading/certificate.py /tmp/json-cst-test --case semantics
python3 benchmarks/json-loading/certificate.py /tmp/json-cst-small --case small --width 4
python3 benchmarks/json-loading/certificate.py /tmp/json-cst-medium --case medium --width 1
python3 benchmarks/json-loading/certificate.py /tmp/json-cst-medium-4 --case medium --width 4
python3 benchmarks/json-loading/certificate.py /tmp/json-cst-wide --case wide --width 4 --seconds 75
```

Measurements on the pinned Lean nightly (`-j1 -M 4096 -s 32768`, separate processes, one run per
row) exclude Lake setup and fixture generation. Splitting/emitting the driver took 0.014 s at
35,686 bytes (width 1) and about 0.35 s at 2,772,046 bytes (width 4). Fragment wall is a proxy
including import, local parsing/emission, kernel validation, assembly and serialization. Link
wall includes import, independent byte embedding, and the kernel comparison. Peak RSS is the
maximum over the measured Lean phases, not their sum.

| Fixture / proof | Fragments (s) | Byte link (s) | Import / linked query (s) | Peak RSS (GiB) |
| --- | ---: | ---: | ---: | ---: |
| 442 B, width 4 | 0.71 | 0.60 | 0.57 / 0.58 | 2.19 |
| 35,686 B, width 1 | 12.49 | 0.89 | 0.59 / 0.73 | 2.20 |
| 35,686 B, width 4 | 13.44 | 0.65 | 0.60 / 0.60 | 2.19 |
| 35,686 B, monolithic `SourceMatches` | — | 9.85, memory limit | — | 4.00 |
| 2,772,046 B, width 4 | timed out at 75 s | not reached | not reached | 2.25 |

The monolithic baseline is the `agreement` row of `run.py --case medium --seconds 20`.
The 35 KiB linked query selects the final entry by ordinal (not by hash index) after import. The
certificate succeeds below the memory cap but is not a faster implementation of `SourceMatches`.
The wide run did not get as far as byte linking: even small independent fragments still pay to
reduce the text parser and check their decoded values. The next architecture to test is a
lexical-event checker over packed spans, proving token decoding and ordered AST assembly
separately, with reusable block proofs. This experiment does not justify a production CST API
or a change to the default/precomputed trust boundary.

## Follow-up: one native executable

```sh
python3 benchmarks/json-loading/run.py /tmp/json-native --native-only --runs 3 --seconds 15
```

The harness builds one optional Lake executable from `Runtime.lean` using a temporary copy of
the Lake config. All three branches are compiled in the same executable; no Lean elaborator
is running in the timed process. The inner timer excludes file I/O/startup; wall and RSS include
both. Values below are medians of three fresh processes. Native timeouts have no measured parse
completion time. Core accepts these fixtures but has a different contract, including object
representation; the numbers do not establish semantic equivalence.

| Fixture | Wire parse / wall / RSS | Core parse / wall / RSS | Fast parse / wall / RSS |
| --- | ---: | ---: | ---: |
| Small | 0.19 ms / 0.03 s / 66 MiB | 0.15 ms / 0.03 s / 66 MiB | 0.17 ms / 0.03 s / 68 MiB |
| Medium | 92.94 ms / 0.13 s / 68 MiB | 0.32 ms / 0.03 s / 66 MiB | 1.50 ms / 0.03 s / 66 MiB |
| Wide | 15 s timeout / 129 MiB | 28.22 ms / 0.06 s / 78 MiB | 114.15 ms / 0.15 s / 130 MiB |
| List | 15 s timeout / 144 MiB | 17.29 ms / 0.05 s / 78 MiB | 117.90 ms / 0.15 s / 146 MiB |
| Nested | 15 s timeout / 133 MiB | 33.93 ms / 0.07 s / 92 MiB | 126.68 ms / 0.16 s / 136 MiB |

Wire also hit 15 s on the 232,566-byte litmus metadata and took 5.38 s on the 116,688-byte
litmus corpus; Fast took 9.81 ms and 5.58 ms respectively. With native runtime already under
0.13 s on the three multi-MiB cases, this follow-up targets the source-linked proof bottleneck,
not further runtime tuning.
