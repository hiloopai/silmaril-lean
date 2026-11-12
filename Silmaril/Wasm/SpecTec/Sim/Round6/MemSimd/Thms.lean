module

public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.MemSimd.Excl
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.MemSimd.Typing
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.MemSimd.Utf8
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.MemSimd.VStore

/-!
# SpecTec ↔ Core 3.0, round 6, track memsimd: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd`; see `docs/projects/spectec/README.md`.

**The memory SIMD exclusion** (`Excl.lean`).

* `noMemSimd_of_bounded`, `noMemSimd_of_boundedSel`: `Round4.Bounded` (hence `Pos.BoundedNE`
  and `Target.BoundedSel`) implies `NoMemSimd`: no `vecLoad*`/`vecStore*` in the code, at any
  depth, or in the store's function bodies. The round-6 target's domain excludes `Step` 22–25
  and `Step_read` 42–51 explicitly through this.
* `not_fires_vstore_of_bnd`, `not_fires_vstore_of_bounded` (`VStore.lean`): `Step` 22–25 do not
  fire on bounded code, in any `simEnv B`, by instruction heads only (round 5's discharge went
  through the provisional payload and breaks under a real encoding). The loads (`Step_read`
  42–51) were already discharged this way (`Round5.Read.bwdS_vload`).

**The additive IL encoding** (`Typing.lean`).

* `typedV_vecLoad`, `typedV_vecLoadLane`, `typedV_vecStore`, `typedV_vecStoreLane`,
  `typedV_vecMemV`: the new images `instrToVM i` of all four memory SIMD instructions are typed
  `instr`s in every `simEnv B`, without validity (`vloadop_`'s premises are checked at every
  load shape: `evalExp_shapePrem`, `hasTypCase_zero`);
* `instrToVM_of_not`: off the four constructors `instrToVM` is `instrToV`;
* `not_typedV_instrToV_vecStore`: the provisional image of `v128.store` is **not** a typed
  `instr` (its memory argument is a `$record` case, `not_hasTyp_memarg_case`).

**U7** (`Utf8.lean`).

* `withUtf8_call_g`: the builtin answers `$utf8("g") = [0x67]`;
* `not_typedV_moduleinst_withUtf8`: it is inert: exporting module instances stay untyped;
* `not_forwardSelE`, `not_wholeStepValidSelE`: `Round5.Task.wholeStepValidSel` with `NoExports`
  dropped (`WholeStepValidSelE`) is false for every choice of builtins.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.noMemSimd_of_bounded' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Round6.MemSimd.noMemSimd_of_bounded

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.not_fires_vstore_of_bnd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round6.MemSimd.not_fires_vstore_of_bnd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.typedV_vecMemV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round6.MemSimd.typedV_vecMemV

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.not_typedV_instrToV_vecStore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round6.MemSimd.not_typedV_instrToV_vecStore

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.not_typedV_moduleinst_withUtf8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round6.MemSimd.not_typedV_moduleinst_withUtf8

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.not_wholeStepValidSelE' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round6.MemSimd.not_wholeStepValidSelE
