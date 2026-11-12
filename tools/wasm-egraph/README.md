# wasm-egraph

Untrusted, proof-producing equality saturation for straight-line integer Wasm (`i32`/`i64`
constants, `local.get`, integer unary, binary, test and comparison operators). It searches for
a chain of rules of the verified library `Silmaril.Wasm.Auto.Rules.library` and prints a
certificate that Lean's checker (`Silmaril.Wasm.Auto.EGraph.segEquiv_of_checkEqL`,
`segRefines_of_checkRefL`) validates with `decide +kernel`. Nothing in this tool is trusted.
Documentation: [docs/projects/wasm-binaryen-tooling.md](../../docs/projects/wasm-binaryen-tooling.md).

```sh
cargo build --release --offline
target/release/wasm-egraph rules                       # the library, index order
target/release/wasm-egraph prove --locals i32,i32 --lean x \
  '(i32.mul (local.get 1) (i32.add (local.get 0) (i32.const 0)))' '(i32.mul (local.get 0) (local.get 1))'
target/release/wasm-egraph prove --flat --locals i32 'local.get 0; i32.eqz; i32.eqz; i32.eqz' 'local.get 0; i32.eqz'
target/release/wasm-egraph optimize --locals i64 '(i64.add (i64.add (local.get 0) (i64.const 7)) (i64.const -7))'
target/release/wasm-egraph bench corpus/regression.sexp --lean OUT.lean --module Corpus
target/release/wasm-egraph tv IN.wasm OUT.wasm --lean OUT.lean --module TvX
# code with local.set / local.tee / drop, through effect summaries (Lean's Silmaril.Wasm.Auto.ESeg)
target/release/wasm-egraph tv-seg IN.wasm OUT.wasm --lean OUT.lean --module TvX --table OUT.md
target/release/wasm-egraph bench-seg corpus/locals.sexp --lean OUT.lean --module ESegCorpus
target/release/wasm-egraph gen-random-locals 40 11 OUT.wasm
```

`tv-seg` and `bench-seg` lift each body to an effect summary (stack, locals, and the guards that
keep the traps of discarded terms), prove the stack slots equal with e-graph chains (with the
second family of computed rewrites, Lean's `comp2?`) and cover the terms of each side, and print
`BodyEquiv` theorems (`bodyEquiv_of_checkBody`, checked by `decide +kernel`) plus `_everyRun`
theorems in the every-run logic for trap-free bodies (`Silmaril.Wasm.Auto.ESeg`). The search
tries the pass-1 limits first, then a backoff scheduler; certificates are minimised (detours
cut). `WASM_EGRAPH_DEBUG=1` traces the search on stderr.

`rules.sexp` is the library in the order of the Lean schemas (`?n` typed variables, `?n!`
total variables that match only terms without division or remainder, `ones` and `width`
constants). `tests/wasm/auto/Rules/Tests.lean` holds the expected text; `tests/run.sh` compares.

Tests (no external tools needed; the optimizer outputs are pinned under `corpus/`):

* `tests/run.sh`: unit tests, the corpus (every case meets its expectation, the generated
  `tests/wasm/auto/EGraph/Corpus.lean` is up to date), translation validation of the pinned
  runs (`Tv{Binaryen,Silmaril,Random}.lean` up to date) and the rule-text sync;
* `tests/run.sh` also checks the locals corpus (`corpus/locals.sexp`) and the pinned runs of
  `tests/seg-runs.txt` (the Lean modules `tests/wasm/auto/ESeg/{Corpus,Tv*}.lean` and the
  summary `tests/seg-expected.txt`); `tests/gen-tv-seg.sh` regenerates them (Binaryen as below,
  its SHA-256 checked; per-function tables in `tests/tables/`);
* `tests/gen-corpus.sh`, `tests/gen-tv.sh`: regenerate. `gen-tv.sh` uses Binaryen `wasm-opt`
  version_123, pinned (URL, archive and binary SHA-256, install path) in
  `tools/wasm-tools/tests/pins.sh` and installed by `tools/wasm-tools/tests/fetch-pins.sh
  binaryen`, and `.lake/build/bin/wasm-opt`; it keeps the pinned outputs with a message
  when either is absent or the binary's hash differs.
