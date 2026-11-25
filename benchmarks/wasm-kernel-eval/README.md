# Kernel evaluation benchmarks

Benchmarks for `Silmaril.Wasm.KernelEval`; results and analysis in
[docs/projects/wasm-kernel-eval.md](../../docs/projects/wasm-kernel-eval.md).

- `bench.py`: the kernel matrix (`decide +kernel`, `decide`, `run` vs `runRec`, list vs packed
  memory).
- Generate and replay checkpoints for `fillSort 64` in 5,000-step chunks:

  ```sh
  lake build --wfail +Silmaril.Wasm.KernelEval.Tests +Silmaril.Wasi.Versions.WitImport.KRfl.Defs
  lake env lean --run benchmarks/wasm-kernel-eval/GenChunks.lean 64 5000 > Chunk.lean
  LEAN_NUM_THREADS=1 lake env lean -DElab.async=false -DwarningAsError=true Chunk.lean
  ```

  The generated file also disables asynchronous elaboration so Lean's cumulative
  `type checking` time counts serial work. Measure wall time around the replay command.
  For separate-process timings, retain the imports and options in every file, followed by
  the one or two checkpoint definitions the theorem uses and the theorem itself.
- `opcode_census.py`: instruction counts of Wasm binaries (core modules and components).
