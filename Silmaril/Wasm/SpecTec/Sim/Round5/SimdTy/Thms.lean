module

public import Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.SimdTy.Refute
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.SimdTy.Vector
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.SimdTy.Exact

/-!
# SpecTec ↔ Core 3.0, round 5, track simdty: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy`; see `docs/projects/spectec/README.md`.

* `not_typedV_f32x4Sqrt`, `not_simdTyping`, `not_instrTyping`, `not_posTypingNE`: the image of
  `f32x4.sqrt` is not a typed `instr`, so `Pos.SimdTyping`, `Pos.InstrTyping` and
  `Pos.PosTypingNE` are false for every `B` (the integer instance of `vunop_` is selected at
  float shapes, `hasTypDef_of_insts_match`, `matchArgs_jnnShapePat`);
* `not_vecTyping`: family V's `Vec.VecTyping` is false for every `B` (its `lanes` field types
  every list, `[true]` included, as lanes; `not_hasTyp_bool_lane`);
* `simdTypingSel`: the restated `SimdTypingSel B` holds for every `B`: every SIMD instruction
  Core accepts, bounded and not `FloatMissel`, is a typed `instr` (`typedV_of_vectorOk`), through
  the typing of the shapes (`typedV_shape`, `typedV_ishape`, `typedV_bshape`) and of the operator
  families (`hasTyp_vIntUnOp`, …, `hasTyp_vConvertOp`);
* `not_typedV_of_floatMissel`, `typedV_iff_not_floatMissel`: the restriction is exact: a bounded
  SIMD instruction Core accepts is typed iff it is not `FloatMissel`;
* `vecTypingL`: the restated vector typing `VecTypingL` (`Round5/VecTyL/Defs.lean`) holds at the
  concrete builtins (lanes `hasTyp_laneInt`, operator fields by inverting `instr`,
  `typedDep_of_instrTyped`, `extractSx_of_instrTyped`);
* `fwd_vectorL`, `vectorFwd_of_ops`: `Int.VectorFwd` from `VecAgreeOps` alone;
  `vector_of_open2`: `Open2.vector` follows from `Open2.vecOps`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.not_simdTyping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.SimdTy.not_simdTyping

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.not_posTypingNE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.SimdTy.not_posTypingNE

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.not_vecTyping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.SimdTy.not_vecTyping

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.simdTypingSel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.SimdTy.simdTypingSel

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.vecTypingL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.SimdTy.vecTypingL

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.vectorFwd_of_ops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.SimdTy.vectorFwd_of_ops

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.typedV_iff_not_floatMissel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round5.SimdTy.typedV_iff_not_floatMissel
