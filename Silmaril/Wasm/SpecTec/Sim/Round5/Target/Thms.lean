module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Target.Assemble
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Target.Multi

/-!
# SpecTec ↔ Core 3.0, round 5, track target: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Target`; see `docs/projects/spectec/README.md`.

**Refutation** (`Guard.lean`, `Refute.lean`).

* `stepRules_lastGuarded`: every one of the 36 `Step` rules reads the last instruction of its
  left-hand code through a quantifier of type `instr*` or `val*`, or as a literal case other
  than `VUNOP` (checked on the fixed script by `rfl`);
* `lastGood_of_lastOk`, `not_sstep_of_last`, `not_sstep_of_last_f32x4Sqrt`: so SpecTec does not
  step from a configuration whose last instruction is `f32x4.sqrt` (its image is neither a typed
  `instr`, `SimdTy.not_typedV_f32x4Sqrt`, nor a typed `val`, `not_typedV_val_vunop`);
* `configOk_sqrtCfg`, `boundedNE_sqrtCfg`, `step_sqrtCfg`, `not_sstep_sqrtCfg`: the witness
  `v128.const 0; f32x4.sqrt` is valid, bounded and export-free, and Core steps from it;
* `not_wholeStepValidOk`: **`Round5.Task.wholeStepValidOk` is false.**

**The restated target** `Round5.Task.wholeStepValidSel` (header `Defs.lean`: also no
`SimdTy.FloatMissel` code, at any depth, in the code or the store's function bodies).

* `posTypingSel`: the positive typing `PosTypingSel B hn` holds for every `B` (track pos's
  reduction re-run on `instrSel` code, with `SimdTy.simdTypingSel` for the SIMD
  leaf); `typed_of_configOk_sel`: `ConfigOk ∧ BoundedSel → Typed` (`Typing.lean`);
* `wholeStepValidSel_of_partsSel`, `wholeStepValidSel_of_open5`: the target from `PartsSel`,
  resp. from `Open5` (`refOk`, `vecOps`), with `simd` discharged (`Assemble.lean`);
* `partsSel_of_partsOkS`, `open5_of_open4`, `wholeStepValidSel_of_ok`: the new statements ask
  no more than the earlier ones;
* `not_open5_spec`: `Open5` is still false under the spec NaN profile (`vecOps.convert`).

**Multi-step** (`Multi.lean`): `fwdRelSel_of_open5`, `bwdRelSel_of_open5`, `multiSel_of_open5`,
`runsSel_of_open5`: pass 2's run corollaries with `BoundedSel` for `Pos.BoundedNE` and without
the `simd` leaf.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.stepRules_lastGuarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round5.Target.stepRules_lastGuarded

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.not_sstep_sqrtCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Target.not_sstep_sqrtCfg

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.not_wholeStepValidOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round5.Target.not_wholeStepValidOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.posTypingSel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Target.posTypingSel

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.typed_of_configOk_sel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round5.Target.typed_of_configOk_sel

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.wholeStepValidSel_of_partsSel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round5.Target.wholeStepValidSel_of_partsSel

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.wholeStepValidSel_of_open5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round5.Target.wholeStepValidSel_of_open5

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.not_open5_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Target.not_open5_spec

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.wholeStepValidSel_of_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round5.Target.wholeStepValidSel_of_ok

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.multiSel_of_open5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Target.multiSel_of_open5

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Target.runsSel_of_open5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Target.runsSel_of_open5
