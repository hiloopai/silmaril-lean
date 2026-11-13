module

public import Silmaril.Proofs.Wasm.Examples.WatSpec.Basic
public import Silmaril.Proofs.Wasm.Examples.WatSpec.VCRegress

/-!
# Annotated WAT examples: results

Proofs in `Silmaril.Proofs.Wasm.Examples.WatSpec.{Basic,VCRegress}`:

* the verification conditions of the `wat_spec!` functions: `addS_vc`, `squareS_vc` (`i64`),
  `maxS_vc` (`select`), `countdownS_vc` (a loop writing its parameter, invariant over
  `old_n`): by `wat_vc` alone; `absS_vc` (`if`, under `x ≠ intMin`), `sumS_vc` (a loop with
  an invariant): `wat_vc` and one arithmetic step each;
* with `Silmaril.Wasm.WatSpec.Annotated.sound`, each gives a valid every-run specification at
  every profile and for every host relation;
* `VCRegress`: `wat_vc` alone closes small conditions with `br_table` (an entry and the
  default), conversions, `unreachable` and a `call` against an explicit spec context;
* **`addS_export`**: every run of `$invoke` of the instantiated annotated `add` on `x, y` can
  still step or has returned `x + y` with the store unchanged.
-/
