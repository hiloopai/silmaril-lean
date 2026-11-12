module

public import Silmaril.Wasm.SpecTec.Sim.Round4.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4.Grow
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4.Sizes
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4.Multi
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4.Preserve
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4.Typed

/-!
# SpecTec ↔ Core 3.0, round 4: what is proved

The frozen target is `Round4.Task.wholeStepValid` (`Round4/Defs.lean`): the one-step
simulation, both directions up to `Bwd.ConfigEq`, from valid (`ConfigOk`) and bounded
(`Bounded`) configurations. It is **not proved**. Proved here:

* **Grow failure, backward, from valid sources** (`Step` 16, 27; the rules round 3's refutation
  used): `bwd_tableGrowFail`, `bwd_memoryGrowFail`, for every `B` and every profile in which
  growth may fail (`growMayFail_spec`). Through `table?_of_configOk`, `mem?_of_configOk`: an
  index of a top-level instruction of valid code resolves in the frame's module and the store
  (`adminsOk_mem`, `instrOk_of_configOk`).
* **Size results, backward, over bounded stores** (`Step_read` 27, 52, 81): `bwd_tableSize`,
  `bwd_memorySize`, `bwd_arrayLenArray`, for every `B` that leaves the store accessors to their
  clauses (`BwdRead.NoAcc`, true of `Prims.builtins`).
* **Preservation.** Core's `Step.preservation` (silmaril-lean) keeps `ConfigOk`; `Bounded` is
  not kept (`not_bounded_preserved`: an `i32` memory grows to `2 ^ 32` bytes from the valid,
  bounded `growCfg`).
* **Runs, conditionally on the one-step simulation along `SimRel`** (`OneStepRel`):
  `steps_sim`, `ssteps_sim` (Core runs ↔ SpecTec runs, up to `ConfigEq`, for `HostOk` hosts and
  runs that stay bounded) and `vals_iff` (Core reaches values `vs` iff SpecTec reaches their
  image).
* **`ConfigOk ∧ Bounded → Typed`, reduced** to the positive typing of the encoding's leaves
  (`PosTyping`: instructions, `CALL_REF` annotations, frame modules, stores; catch clauses are
  typed outright, `typedV_catch`):
  `typed_of_configOk`. With it, `oneStep_of_rel` and `wholeStepValid_of` reduce the frozen
  target to `PosTyping` and `OneStepRel`. `PosTyping` is not discharged.

See `docs/projects/spectec/README.md`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.bwd_memoryGrowFail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.bwd_memoryGrowFail

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.bwd_tableGrowFail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.bwd_tableGrowFail

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.bwd_tableSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.bwd_tableSize

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.bwd_memorySize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.bwd_memorySize

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.bwd_arrayLenArray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.bwd_arrayLenArray

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.not_bounded_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.not_bounded_preserved

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.steps_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.steps_sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.ssteps_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.ssteps_sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.vals_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.vals_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.typed_of_configOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.typed_of_configOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round4.wholeStepValid_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round4.wholeStepValid_of
