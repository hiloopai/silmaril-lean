module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Agree
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Vtestop
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.ConvertRefute
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.LanesAgree

/-!
# SpecTec ↔ Core 3.0, round 5, track simd: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Simd`; see `docs/projects/spectec/README.md`.

* `not_vecAgree_of_lanes`: family V's `VecAgree` is false wherever `B` does not answer `$lanes_`,
  as `Prims.builtins` did before this track (so pass 1's `Round5.Int.Open` was unsatisfiable).
* `applies_lanes`, `applies_invLanes`: `Prims.builtins` now answers `$lanes_` and `$inv_lanes_`
  by Core's lanes (`Round5/Lanes/Defs.lean`); `lanesV_injective`.
* `extractNum`, `extractPack`, `splat`, `replaceLane`, `allTrue`: five lane fields of `VecAgree`,
  proved at the concrete builtins (with `applies_lunpack`, `applies_lpacknum`, and, for every
  `B`, `applies_prod`, `applies_jsizenn`).
* `vecAgree_of_ops`: `VecAgree` at the concrete builtins from `VecAgreeOps`, its remaining
  fields; `open_of_openS`: `Round5.Int.Open` from `OpenS`.
* `bwd_vsplat`, `bwd_vextractLaneNum`, `bwd_vextractLanePack`, `bwd_vreplaceLane`: `Step_pure`
  70–73 backward at the concrete builtins, with no hypothesis (the quantifiers `nt : numtype`,
  `pt : packtype` and `$lunpack` pick the shape); `pureOpenV_of_vtestop`: `BwdStep.PureOpenV`
  from rule 64 alone.
* `wholeStepValidOk_of_openS`: the restated target from `OpenS`.
* `vectorFwd_of`: `Open.vector` from family V's `VecTyping` and `VecAgreeOps`;
  `vecInstrV?_isSome`: `vecInstrV?` answers every bounded SIMD instruction.

Pass 3:

* `num_i32_inv`: a value of type `num_(I32)` is `%(n)`; `bwd_vtestop`: `Step_pure` 64 backward at
  the concrete builtins; `pureOpenVtestop`: `PureOpenVtestop` holds (the `vtestop` field of
  `Round5.Int2.Open2`).
* `not_convert_spec`, `not_vecAgreeOps_spec`, `not_vecAgree_spec`: under `P.nan = .spec`,
  `$vcvtop__` (a function) cannot list both canonical NaNs `promote_low` allows, so
  `VecAgreeOps`, family V's `VecAgree` and (`not_open2_spec`) `Round5.Int2.Open2` at every
  `Profile.spec nd r` are unsatisfiable, for every environment.
* `not_narrow_of`, `not_vecAgreeOps_of_narrow`: without a fallback the lane-wise operators denote
  nothing (their clauses bind lanes in `if` premises, `vnarrowop_undef`), so `VecAgreeOps` was
  also false at `Prims.builtins` before this pass.
* `Prims.builtins` now answers the lane-wise operators by `vecOpCall` (`Round5/Lanes/Defs.lean`);
  `vecAgreeLanes_builtins`: every field of `VecAgreeOps` but `convert` holds at the concrete
  builtins; `vecAgreeOps_of_lanes`; `vecConvertR_of_undef`: the restated `VecConvertR` from the
  definite failure of `$vcvtop__`'s clauses.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.not_vecAgree_of_lanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.not_vecAgree_of_lanes

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.extractNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.extractNum

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.extractPack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.extractPack

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.splat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.splat

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.replaceLane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.replaceLane

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.vecAgree_of_ops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.vecAgree_of_ops

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.open_of_openS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.open_of_openS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.bwd_vextractLaneNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.bwd_vextractLaneNum

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.bwd_vextractLanePack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.bwd_vextractLanePack

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.bwd_vsplat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.bwd_vsplat

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.bwd_vreplaceLane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.bwd_vreplaceLane

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.pureOpenV_of_vtestop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.pureOpenV_of_vtestop

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.wholeStepValidOk_of_openS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.wholeStepValidOk_of_openS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.allTrue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.allTrue

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.vectorFwd_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.vectorFwd_of

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.vecInstrV?_isSome' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Round5.Simd.vecInstrV?_isSome

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.bwd_vtestop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.bwd_vtestop

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.pureOpenVtestop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.pureOpenVtestop

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.num_i32_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.num_i32_inv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.not_convert_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.not_convert_spec

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.not_vecAgreeOps_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.not_vecAgreeOps_spec

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.not_vecAgree_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.not_vecAgree_spec

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.not_open2_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.not_open2_spec

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.not_narrow_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.not_narrow_of

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.not_vecAgreeOps_of_narrow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.not_vecAgreeOps_of_narrow

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.vecAgreeLanes_builtins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round5.Simd.vecAgreeLanes_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.vecAgreeOps_of_lanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.vecAgreeOps_of_lanes

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.vecConvertR_of_undef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.vecConvertR_of_undef

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.f_shuffle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.f_shuffle

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Simd.f_extBinOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Simd.f_extBinOp
