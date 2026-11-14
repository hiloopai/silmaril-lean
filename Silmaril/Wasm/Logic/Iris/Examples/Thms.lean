module

public import Silmaril.Proofs.Wasm.Logic.Iris.Examples

/-!
# Worked examples for the Iris logic of Wasm Core 3.0

Proofs in `Silmaril/Proofs/Wasm/Logic/Iris/Examples.lean`, for **every profile** and
**every host relation**, and for any module instance in which the indices
resolve as the hypotheses state:

* memory64: `storeLoad_wp` (an `i32.store` then `i32.load` at an `i64` address
  returns the stored value and leaves its four little-endian bytes owned),
  `storeLoad_hwp` (its adequacy: every run is safe and exits with `[c]`);
* multiple memories: `twoMems_wp` (stores at the same address of two memories do
  not interfere);
* globals: `bump_wp` (`global.get; i32.const 1; i32.add; global.set`),
  `bump_itriple` (an `ITriple`), `bump_triple` (the Silmaril every-run triple
  `Silmaril.Wasm.Logic.Hoare.Triple` obtained by `ITriple.sound`, with the final
  store's global read through `wp_exit_cells`);
* GC arrays: `arrLen_wp` (`array.new_fixed` of two elements, then `array.len`);
* exceptions: `throw_wp`, `throw_hwp` (`throw` exits with outcome `throw a`);
* nondeterminism: `grow_wp`, `grow_hwp` (`memory.grow` on a memory64 memory
  returns the old size or `-1`, whichever the profile allows).
-/