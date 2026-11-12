module

public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFix
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixNeed
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixTyped
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixLift
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixClosed
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixStep
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFixFire

/-!
# The 2.0 `STORE` erratum: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.StoreFix`; see `docs/projects/spectec/README.md`.

* `StoreFixNeed`: without the erratum the corrected script is stuck from every state whose store
  has a storing function (`stuck_storeFn20S`, at every builtins; the rule check
  `stepRules20S_state` is by `decide +kernel`).
* `StoreFix`: the two errata (`storeInstrErratum20`, `storeAdminErratum20`) apply on top of
  `StepFix.fixedS20` and give `fixedT20` (`applyErrata_store20`).
* `StoreFixTyped`: in `simEnv20T` the V2 store instructions tested are typed, a packed float
  store is not, and the storing configuration `storeFnCfg` has a typed image.

* `StoreFixLift`, `StoreFixClosed`, `StoreFixStep`, `StoreFixFire`: on `memStoreCfg` (a storing
  function, an empty memory, code `i32.const 0; i32.const 0; i32.store; nop`) V2 steps to
  `trap; nop`; `simEnv20S` is stuck (`stuck_memStoreCfg`), and `simEnv20T` steps between the
  images through `store-num-trap` under `ctxt-instrs` (`sstepT_memStoreCfg`, every builtins).

Open: the forward rules of the 2.0 route in `simEnv20T` in general (they need a `hasTyp`
agreement theorem between the two type tables).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.stuck_storeFn20S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.stuck_storeFn20S

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.stuck_configV_storeFn20S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.stuck_configV_storeFn20S

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.stepRules20S_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.stepRules20S_state

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.not_typedV_state_storeFn20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.not_typedV_state_storeFn20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.applyErrata_store20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.applyErrata_store20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.typedV_i32Store20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.typedV_i32Store20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.typedV_i64Store8_20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.typedV_i64Store8_20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.typedV_f32Store20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.typedV_f32Store20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.storeCaseFix_rejects_f32_8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.storeCaseFix_rejects_f32_8

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.typed20T_storeFnCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.typed20T_storeFnCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.sstepB20T_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.sstepB20T_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.sstepT_ctxtInstrs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.sstepT_ctxtInstrs

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.step_memStoreCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.step_memStoreCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.stuck_memStoreCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.stuck_memStoreCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.fires_storeTrapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.fires_storeTrapM

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreFix.sstepT_memStoreCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.StoreFix.sstepT_memStoreCfg
