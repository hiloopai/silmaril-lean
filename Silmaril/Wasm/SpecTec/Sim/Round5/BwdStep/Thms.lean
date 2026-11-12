module

public import Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.BwdStep.Assemble
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.BwdStep.Provisional

/-!
# SpecTec ↔ Core 3.0, round 5, track bwdstep: what is proved

At the concrete `B := Prims.builtins P hn host`, from every source satisfying
`Round4Read.ReadValid`:

* `bwd_tableGrowSucceed` (15), `bwd_memoryGrowSucceed` (26): in every profile in which growth may
  succeed; `$growtable`/`$growmem` are read back through `B` (`growtable_inv`, `growmem_inv`).
* `bwd_tableGrowFail` (16), `bwd_memoryGrowFail` (27): in every profile in which growth may fail
  (r4-validity's lemmas, redone from `ReadValid` instead of `ConfigOk`).
* `bwd_storeNumVal` (19), `bwd_storePackVal` (21): a firing `$with_mem` is in bounds
  (`withMem_bound`), so Core's store succeeds and the written state is its image.
* `bwd_arraySetArray` (35), `bwd_structSetStruct` (31): `$type`, `Expand`, `$packfield_`,
  `$with_array`/`$with_struct` and the two-domain iteration `(%% mut? zt)*` read back
  (`type_inv`, `packfield_inv`, `withArray_inv`, `withStruct_inv`, `iterList2_inv`).
* `bwd_arrayNewFixed` (32), `bwd_structNew` (29): the `^n` iterations over `val*` (and `zt*`)
  read back (`iterListN1_inv`, `iterListN2_inv`, `packFields_inv`, `packFields2_inv`), `val*`
  decoded by family E's `StructDecode.vals`.
* `step_lt`: no `Step` rule of index `≥ 36` fires.
* `remStep_of_open`: the `step` field of `Round4Read.RemainingV` from `StepOpenV`, the rules of
  `stepOpenR5` alone.
* `not_fires_vstoreOob`, …, `not_fires_vstoreLaneVal` (22–25): at the current, provisional
  encoding of the memory SIMD instructions none of these rules fires (their `ao.OFFSET` has no
  value), so `stepOpenV_provisional` and **`remStep`: the `step` field of `RemainingV` is
  discharged** at the concrete `B` (every profile in which growth may succeed and fail).
  `remainingV_of`: `RemainingV` from `VecAgree`, `PureOpenV` and the `Step_read` field.
* `vecDecode`: family V's decoder interface `Vec.VecDecode`, discharged.
* `pure_vecDone`: 20 of the 25 vector rules of `Step_pure` (`pureVecDone`), from family V's
  `VecAgree` at the concrete `B`; `remPure_of_open`: the `pure` field of `RemainingV` from
  `VecAgree` and `PureOpenV` (rules 64, 70–73).

See `docs/projects/spectec/README.md`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.step_doneR5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.BwdStep.step_doneR5

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.remStep_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.BwdStep.remStep_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.vecDecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.BwdStep.vecDecode

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.remPure_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.BwdStep.remPure_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.remStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.BwdStep.remStep

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.remainingV_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.BwdStep.remainingV_of
