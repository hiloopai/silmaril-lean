module

public import Silmaril.Proofs.Wasm.Examples.Verified.Basic

/-!
# Verified Wasm functions: results

Proofs in `Silmaril.Proofs.Wasm.Examples.Verified.Basic`: `double_vc`, `abs_vc`, `max_vc`, `sum_vc`
(a loop), `storeLoad_vc`, `get_vc` (memory) for the functions of `prog`; with
`Silmaril.Wasm.Verify.FnSpec.sound` each gives a valid every-run call specification at every
profile and for every host relation. **`double_verified`**: function `0` of the module decoded
from the 43-byte `double.wasm` meets `doubleSpec` (`doubleBytes_decode`, `doubleWat_vc`).
-/

/-- info: 'Silmaril.Wasm.Examples.Verified.get_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Examples.Verified.get_vc

/-- info: 'Silmaril.Wasm.Examples.Verified.sum_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Examples.Verified.sum_vc

/-- info: 'Silmaril.Wasm.Examples.Verified.double_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Examples.Verified.double_verified
