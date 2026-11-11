module

public import tests.wasm.auto.FrontBenchX.Defs
public import tests.wasm.auto.FrontBenchX.Proofs.Proved
public import tests.wasm.auto.FrontBenchX.Proofs.Refuted

/-!
# The front-end benchmark, extended set: results

Proofs in `Silmaril.Proofs.Wasm.Auto.FrontBenchX.{Proved,Refuted}`, all by kernel evaluation:

* at every profile, both relations (`wasm_prove`, the extended summaries): `requantO2_equiv`
  (the `requant` kernel against Binaryen `-O2`/`-O3`), `divRemO2_equiv`,
  `divRemRef_equiv` (trap guards), `counterO2_equiv` (a global, `wrap`/`extend`);
* at the deterministic profile (`wasm_diff_refute`): `requantO2_not_refines_v0`,
  `divRemSigned_not_refines`.

The memory cases (`adlersum8-O2`, `adlersum8-mutant`) are decided by the compiled tool only: a
one-page memory does not instantiate in the kernel in reasonable time and memory.
-/

@[expose] public section
