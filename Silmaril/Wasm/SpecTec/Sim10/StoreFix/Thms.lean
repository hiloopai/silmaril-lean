module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreFix10Fire

/-!
# The 1.0 `STORE` erratum: round 4, pass 2

In `Silmaril.Wasm.SpecTec.Sim10.StoreFix` (definitions in `Sim10.StoreFix.Defs`).

* The erratum `storeCaseFix10` binds `Inn` through a premise on the payload's `valtype`; its two
  `IL.Erratum`s apply (`storeInstrErratum10_applies`, `storeAdminErratum10_applies`, kernel) and
  give `fixedT10` (`applyErrata_store10`).
* In `simEnv10T`, `STORE` instructions are typed (`typedV_i32Store10T`, `typedV_i64Store8_10T`,
  `typedV_f32Store10T`), a packed float store is still rejected (`storeCaseFix10_rejects_f32_8`),
  and a storing configuration has a typed image (`typed10T_storeFnCfg`).
* **A store matched, at one instance** (`StoreFix10Step`, `StoreFix10Closed`, `StoreFix10Fire`):
  at `memStoreCfg10` (`i32.const 0; i32.const 0; i32.store` over an empty memory) V1 traps
  (`step_memStoreCfg10`); in the original script the image is untyped
  (`not_typed10_memStoreCfg`), in `simEnv10T` both images are typed and the script steps between
  them (`typed10T_memStoreCfg`, `typed10T_memStoreCfg'`, `sstep10T_memStoreCfg`).
* Not done: the forward 1.0 rules in general in `simEnv10T`, which need an agreement theorem
  between the type tables of `simEnv10` and `simEnv10T`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.storeInstrErratum10_applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.storeInstrErratum10_applies

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.storeAdminErratum10_applies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.storeAdminErratum10_applies

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.applyErrata_store10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.applyErrata_store10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.typedV_i32Store10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.typedV_i32Store10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.typedV_i64Store8_10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.typedV_i64Store8_10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.typedV_f32Store10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.typedV_f32Store10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.storeCaseFix10_rejects_f32_8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.storeCaseFix10_rejects_f32_8

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.typed10T_storeFnCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.typed10T_storeFnCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.not_typed10_memStoreCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.not_typed10_memStoreCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.typed10T_memStoreCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.typed10T_memStoreCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.typed10T_memStoreCfg'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.typed10T_memStoreCfg'

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.closedB_step10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.closedB_step10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.StoreFix.sstep10T_memStoreCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.StoreFix.sstep10T_memStoreCfg
