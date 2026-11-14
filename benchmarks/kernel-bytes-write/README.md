# Kernel bytes: path-copying and rope writes

`bench.py` times one `decide +kernel` of four `readLE` facts after `n` 8-byte writes at
pseudo-random offsets in 1 MiB of zero bytes, for the two writes of
`Silmaril.Prelude.Bytes.Write` (`write`, path copying; `ropeWrite`, rope) on the two zero
memories (`zerosCanon 4096`, 256 leaves of 4 KiB; `zeros`, one 1 MiB leaf). The cases are a
targeted sample, not a matrix; they do not rank the representations in general (the Wasm memory
benchmarks of hiloopai/silmaril-lean#131 and #133 measure more, including `PageMem`).

Measured 2026-11-14, Lean `nightly-2026-11-05`, one run each, wall clock of `lean` on the file
(including about 0.3 s of start-up and import), default `maxHeartbeats`:

| base | write | n = 64 | n = 256 | n = 1024 |
|---|---|---:|---:|---:|
| `zerosCanon 4096` | `write` | 0.33 s | 0.41 s | 0.69 s |
| `zerosCanon 4096` | `ropeWrite` | 1.58 s | 14.65 s | timeout (145 s) |
| `zeros` (one leaf) | `write` | 4.30 s | 17.93 s | 72.58 s |
| `zeros` (one leaf) | `ropeWrite` | 0.49 s | 7.90 s | 151.56 s |

Reading: the cost follows the leaf size and the tree depth. Path copying on bounded leaves
(`leafBound 4096`, which `write` preserves) stays below a second; on one unbounded leaf every
write rewrites a 1 MiB number. Rope writes add nodes and leaves on every write, so reads
slow down with the number of writes on either base.
