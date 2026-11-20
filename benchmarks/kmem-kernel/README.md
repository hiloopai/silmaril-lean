# End-to-end component acceptance in the kernel: `KMem` against `ByteArray`

`bench.py` measures wall time and peak RSS of `lake env lean` on two files:

* `kmem`: `Silmaril/Wasi/Component/Accept/Ref/KMem/Examples.lean`. It checks
  `runHiK_true` by `decide +kernel` (decode, validate, instantiate and run the `"hi!"`
  acceptor over `core3K neverFail`, whose memories are `KMem` trees), then `acceptedK_hi`,
  `hi_mem_of_progRel` and `hi_mem`.
* `bytearray`: a generated file that checks `runHi = true` (the same run over the `ByteArray`
  engine `core3 neverFail`) by `decide +kernel`. This case is expected to fail. It is a
  measurement, not a test, and CI does not run it.

See `docs/projects/wasm-memrep.md` for what the checks prove.

## Provenance

One run on commit `bd1e3054` (branch `wasm/kmem-evaluator`, 2026-11-16), Lean
`nightly-2026-11-05`, on a 2-vCPU Linux sandbox, one sample per case:

```
lake build Silmaril.Wasi.Component.Accept.Ref.KMem.Examples
python3 -I benchmarks/kmem-kernel/bench.py
```

Raw output: [`results-2026-11-16.tsv`](results-2026-11-16.tsv). Times and RSS are for the whole
`lean` process, including the imports.

| case | result | wall | peak RSS |
|---|---|---:|---:|
| `kmem` | passes | 7.3 s | 1.47 GB |
| `bytearray` | `(kernel) deep recursion detected` | 14.5 s | 3.42 GB |
