# Kernel bytes: path-copying and rope writes

`bench.py` times one `decide +kernel` of four `readLE` facts after `n` 8-byte writes at
pseudo-random offsets in 1 MiB of zero bytes. It covers the two writes of
`Silmaril.Prelude.Bytes.Write` (`write`, path copying; `ropeWrite`, rope) on the two zero
memories (`zerosCanon 4096`, 256 leaves of 4 KiB; `zeros`, one 1 MiB leaf). The expected values
come from a Python model of the same writes, so a wrong read fails the check. The cases are a
targeted sample, not a matrix, and they do not rank the representations in general. The Wasm
memory benchmarks of hiloopai/silmaril-lean#131 and #133 measure more, including `PageMem`.

## Provenance of the table

Every row is from **one** run of this script at commit `e52f1f65` (2026-11-14), with Lean
`nightly-2026-11-05` (Lake 5.0.0), on an 8-core Linux sandbox, one sample per case:

```
lake build Silmaril.Prelude.Bytes.Write.Thms
python3 -I benchmarks/kernel-bytes-write/bench.py 64 256 1024
```

The raw output is [`results-2026-11-14.tsv`](results-2026-11-14.tsv), with only the temporary
directory removed from the one error line. The run used a checkout whose Lake project contains
only the `Silmaril` modules these import (`Init`/`Lean` only), so `lake env lean` started without
Mathlib. Times are wall clock of `lake env lean` on the generated file, including about 0.3 s of
start-up and import, under the default `maxHeartbeats`. The timeout cell is the kernel's
deterministic timeout, not the script's 300 s limit.

| base | write | n = 64 | n = 256 | n = 1024 |
|---|---|---:|---:|---:|
| `zerosCanon 4096` | `write` | 0.37 s | 0.43 s | 0.68 s |
| `zerosCanon 4096` | `ropeWrite` | 1.62 s | 16.15 s | deterministic timeout (177.53 s) |
| `zeros` (one leaf) | `write` | 4.24 s | 17.97 s | 72.29 s |
| `zeros` (one leaf) | `ropeWrite` | 0.55 s | 8.22 s | 155.23 s |

Reading: in these cases the cost follows the leaf size and the tree depth. Path copying on
bounded leaves (`leafBound 4096`, which `write` preserves) stays below a second. On one
unbounded leaf, every write rewrites a 1 MiB number. Rope writes add nodes and leaves on every
write, so reads slow down with the number of writes on either base.
