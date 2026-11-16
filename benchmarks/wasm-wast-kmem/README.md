# `address.wast` in the kernel: `KMem` against `ByteArray`

`bench.py` measures wall time and peak RSS of `lake env lean` on one generated file per case:

* `imports`: only the imports (`Silmaril.Project.WasmWast.Address.Defs`,
  `Silmaril.Project.Shapes.WasmWast.Thms`), the fixed cost of every case;
* `kmemJ`: `ScriptHolds neverFail mJ cmdsJ` by `ScriptHolds.of_kernelKM` and `decide +kernel`, the
  check of `scriptJ` in `Silmaril/Project/WasmWast/Address/Thms.lean`: decode, validate,
  instantiate on `KMem` stores (data segments included) and run every command;
* `bytesJ`: the same by `ScriptHolds.of_kernel` (`scriptK`, `ByteArray` stores). Expected to fail.
  A measurement, not a test; CI does not run this script.

See `docs/projects/wasm-wast.md` for what the checks prove.

## Provenance

One run on branch `wasm/wast-kmem` (#843 with #796 merged, 2026-11-16), Lean
`nightly-2026-11-05`, on a 2-vCPU Linux sandbox, one sample per case:

```
lake build Silmaril.Project.WasmWast.Address.Defs Silmaril.Project.Shapes.WasmWast.Thms
python3 -I benchmarks/wasm-wast-kmem/bench.py
```

Raw output: [`results-2026-11-16.tsv`](results-2026-11-16.tsv). Times and RSS are for the whole
`lean` process, including the imports (3.6 s, 1.55 GB).

| module | commands | `KMem` (`scriptKM`) | `ByteArray` (`scriptK`) |
|---|---:|---|---|
| 0 (line 3) | 91 | passes, 27.8 s, 5.92 GB | `(kernel) deep recursion detected`, 38.4 s, 6.84 GB |
| 1 (line 223) | 126 | passes, 47.4 s, 9.49 GB | `(kernel) deep recursion detected`, 52.1 s, 10.15 GB |
| 2 (line 514) | 19 | passes, 5.3 s, 1.95 GB | `(kernel) deep recursion detected`, 15.6 s, 3.32 GB |
| 3 (line 564) | 19 | passes, 6.2 s, 2.00 GB | `(kernel) deep recursion detected`, 15.9 s, 3.32 GB |

The `ByteArray` cases fail while instantiating (the data segment write into the 64 KiB memory);
they never reach the commands. For module 1, most of the time and memory is decoding the module
in the kernel, not memory operations: a separate file checking only
`(decode? bytes1).isSome = true` by `decide +kernel` took 40 s and 9.0 GB (imports included, one
run).
