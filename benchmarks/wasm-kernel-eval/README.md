# Kernel evaluation benchmarks

Benchmarks for `Silmaril.Wasm.KernelEval`; results and analysis in
[docs/projects/wasm-kernel-eval.md](../../docs/projects/wasm-kernel-eval.md).

- `bench.py`: the kernel matrix (`decide +kernel`, `decide`, `run` vs `runRec`, list vs packed
  memory); `--native --tactic native` adds `native_decide` cases, written to a temporary
  directory only.
- `GenChunks.lean` (with `KernelRfl.lean`): `lake env lean --run benchmarks/wasm-kernel-eval/GenChunks.lean N K > Chunk.lean`
  prints a piecewise certificate for `fillSort N` with `K`-step chunks; check it with
  `lake env lean Chunk.lean`.
- `opcode_census.py`: instruction counts of Wasm binaries (core modules and components).
- `mem_bench.py`: kernel benchmarks of the memory representations (one `decide +kernel` per
  case; kernel time and peak memory of the `lean` process).
- `NativeBench.lean`: the same workloads compiled natively; `lake build kernel-eval-bench &&
  .lake/build/bin/kernel-eval-bench`. See
  [docs/projects/wasm-kernel-eval-memory.md](../../docs/projects/wasm-kernel-eval-memory.md).
