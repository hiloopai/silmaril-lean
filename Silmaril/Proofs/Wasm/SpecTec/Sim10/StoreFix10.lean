module

public import Silmaril.Wasm.SpecTec.Sim10.StoreFix.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixTyped
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdStoreVac

/-!
# The 1.0 `STORE` erratum applies, and types what the original refutes

* `storeInstrErratum10_applies`, `storeAdminErratum10_applies` (kernel): each erratum applies to
  the script it is applied to; `applyErrata_store10`: in order, on `Scripts.Wasm10.fixed`, they give
  `fixedT10`.
* Non-vacuity is in `StoreFix10Typed` and `StoreFix10Cfg`, by evaluation of `hasTyp`, at every builtins:
  - `typedV_i32Store10T`, `typedV_i64Store8_10T`, `typedV_f32Store10T`: `i32.store`,
    `i64.store8` and `f32.store` are typed `admininstr`s of `simEnv10T`. In the original script
    no `STORE` is (`Whole.not_typedV_store10`);
  - `storeCaseFix10_rejects_f32_8`: the premise is not vacuous (a packed float store is rejected);
  - `typed10T_storeFnCfg`: a configuration whose store holds a function whose body is
    `i32.store` has a typed image in `simEnv10T`.

What is not done: the forward rules are stated in `simEnv10 B`, and moving them to `simEnv10T B`
needs an agreement theorem between the two type tables (as for 2.0's `simEnv20T`). So stores are
typed, but not yet matched by the forward theorem.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config)
open Silmaril.Wasm.SpecTec.Sim (TypedV)

/-! ## The errata apply -/

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **The `instr` erratum applies** to `Scripts.Wasm10.fixed` (kernel). -/
theorem storeInstrErratum10_applies :
    storeInstrErratum10.applies Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed = true := by
  decide +kernel

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **The `admininstr` erratum applies** after it (kernel). -/
theorem storeAdminErratum10_applies :
    storeAdminErratum10.applies (replaceDefs instrFix10 Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed) =
      true := by
  decide +kernel

set_option maxRecDepth 8000000 in
/-- Applying both gives `fixedT10`. -/
theorem applyErrata_store10 :
    applyErrata [storeInstrErratum10, storeAdminErratum10] Silmaril.Wasm.SpecTec.Scripts.Wasm10.fixed =
      some fixedT10 := by
  simp only [applyErrata_cons, applyErrata_nil, applyErratum, storeInstrErratum10_applies,
    ↓reduceIte, Option.bind_some]
  have h : storeInstrErratum10.corrected = instrFix10 := rfl
  simp only [h, storeAdminErratum10_applies, ↓reduceIte, Option.bind_some, applyErrata_nil]
  rfl

end Silmaril.Wasm.SpecTec.Sim10.StoreFix
