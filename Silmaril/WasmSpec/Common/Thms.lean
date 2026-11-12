module

public import Silmaril.Proofs.WasmSpec.Common.Bridge
public import Silmaril.Proofs.WasmSpec.Common.Ops

/-!
# Wasm specification library: shared results

* `Silmaril.WasmSpec.funcPost_mono`: `funcPost` is monotone in its result predicate;
* `Silmaril.WasmSpec.Computes.funcSpec`: a body-level specification (`Computes`)
  for every input gives the call-level `PureSpec` of a function stored at an
  address whose instance runs that body
  (`Silmaril.Proofs.WasmSpec.Common.Bridge`);
* `Silmaril.WasmSpec.Ops`: `i32` tests, comparisons and the signed shift as
  `BitVec 32` operations, by `rfl` (`Silmaril.Proofs.WasmSpec.Common.Ops`).
-/
