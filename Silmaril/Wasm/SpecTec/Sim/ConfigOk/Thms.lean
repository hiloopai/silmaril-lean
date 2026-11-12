module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Step
public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Exports
public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Bounds
public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Store
public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Mem

/-!
# SpecTec ↔ Core 3.0, round 3, track configok: what is proved

Gaps 2–3 of "Round 2 status" (`docs/projects/spectec/README.md`): `Typed` from Core's `ConfigOk`, and
the typing bundles `Residue`, `Extra`, `BwdOpen` for the concrete `B`. Namespace
`Silmaril.Wasm.SpecTec.Sim.ConfigOk`.

**Non-vacuity.** `typedStep_exists`: for every `B`, `hn`, profile and host there is a step
`c → c'` with `ConfigOk c []`, `Integrate.Covered c` (so `StoreOk c.store`), `Typed c` and
`Typed c'` (`nop` on the empty state).

**Findings (formal refutations).**

* `not_hasTyp_exportinstText`, `not_typedV_moduleinstText_of_export`: the ported bridge encoded
  an export's `NAME` as a text, and `name` is a variant, so no module instance with an export was
  typed. Round 3 concluded that `ConfigOk c ts → Typed (simEnv B) hn c` was false for every `B`
  (witness `exportConfig`, still `configOk_exportConfig`). Round 4 fixed the encoding (upstream
  item U4: `RuntimeBridge.nameToValue`), so the configuration-level refutations were retired; the
  text encoding is kept as `RuntimeBridge.exportInstToValueText`.
* `not_typeTyping`, `not_residue`: `Prims.TypeTyping` and so `Integrate.Residue` are false in
  every `simEnv B` (`typeuse*` of `[_IDX 2^32]`; `typeidx = u32`).
* `not_ctrlCall`, `not_wholeAssumptions`: family C's `CtrlCall.valtypes` is false
  (`valtype*` of `[ref (_IDX 2^32)]`), so `Whole.Assumptions` is uninhabited.
* `not_aggTypes`, `not_extra`: `AggTypes.storagetype` is false, so `Integrate.Extra` is
  uninhabited.
* `not_wholeStepBounded_of_concrete_hyp`: the hypothesis of
  `Integrate.wholeStepBounded_of_concrete` is false; `forward_concrete` and `backward_concrete`
  hold vacuously.

**Discharged** (every `B`): `Residue.funcinst` (`funcinst_of_store`), `Residue.result`
(`typedV_result`), `BwdOpen.exnFields` (`exnFields_simEnv`), `Memory.MemTyping`
(`memTyping_simEnv`), `Memory.InstTyping` (`instTyping_simEnv`), and `AggTypes.arrayOfStore`,
`structOfStore`, `mut_` (`arrayOfStore_simEnv`, `structOfStore_simEnv`, `typedV_mut`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.ConfigOk.typedStep_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConfigOk.typedStep_exists

/--
info: 'Silmaril.Wasm.SpecTec.Sim.ConfigOk.not_typedV_moduleinstText_of_export' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms ConfigOk.not_typedV_moduleinstText_of_export

/-- info: 'Silmaril.Wasm.SpecTec.Sim.ConfigOk.configOk_exportConfig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConfigOk.configOk_exportConfig

/-- info: 'Silmaril.Wasm.SpecTec.Sim.ConfigOk.not_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConfigOk.not_residue

/-- info: 'Silmaril.Wasm.SpecTec.Sim.ConfigOk.not_wholeAssumptions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConfigOk.not_wholeAssumptions

/-- info: 'Silmaril.Wasm.SpecTec.Sim.ConfigOk.not_extra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConfigOk.not_extra

/--
info: 'Silmaril.Wasm.SpecTec.Sim.ConfigOk.not_wholeStepBounded_of_concrete_hyp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms ConfigOk.not_wholeStepBounded_of_concrete_hyp

/-- info: 'Silmaril.Wasm.SpecTec.Sim.ConfigOk.memTyping_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConfigOk.memTyping_simEnv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.ConfigOk.exnFields_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConfigOk.exnFields_simEnv
