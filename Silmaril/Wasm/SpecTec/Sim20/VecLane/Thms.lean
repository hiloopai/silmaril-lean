module

public import Silmaril.Wasm.SpecTec.Sim20.VecLane.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLanePackV
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneStep
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneB
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneFExt

/-!
# Vector lanes and vector numerics of wasm-2.0 in the corrected script: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.VecLane`; see `docs/projects/spectec/README.md`, "vec".

* `VecLanePack`, `VecLanePackV`: `vextract_lane-pack` (rule 47) at `i8x16`/`i16x8`:
  `fwd_vextractLanePack` in any environment with `PackEnv`; **`fwd_vextractLanePack20V`** and
  **`sstepV_vextractLanePack`** in `simEnv20V (storeB P)`.
* `VecLaneFOp`: **`hasTyp_famFloat`**, every float operator has its corrected family's type at a
  float shape.
* `VecLaneRules`, `VecLaneFNum`, `VecLaneFNum2`, `VecLaneStep`: under the vector numerics
  hypothesis `VecNumAgree` (assumed), the float `vunop`, `vbinop-val` and `vrelop` rules match
  every V2 step at float shapes (`fwd_vecFloatUnOp20V`, `fwd_vecFloatBinOp20V`,
  `fwd_vecFloatRelOp20V`) and are `Step`s (`sstepV_vecFloatUnOp`, …).
* `VecLaneB`: **`vecB P`**, builtins with `$lanes_` at float shapes and `$inv_lanes_` inverting
  `$lanes_` (`vecB_invLanes`, `vecB_invLanesF`), still answering as `storeB P` elsewhere
  (`laneCalls20_vecB`, `floatB_vecB`).
* `VecLaneFExt`: `vextract_lane-num` at `f32x4`/`f64x2`: **`fwd_vextractLaneF20V`**,
  **`sstepV_vextractLaneF`** at `vecB P`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecLane.sstepV_vextractLanePack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecLane.sstepV_vextractLanePack

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecLane.sstepV_vecFloatUnOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecLane.sstepV_vecFloatUnOp

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecLane.sstepV_vecFloatBinOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecLane.sstepV_vecFloatBinOp

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecLane.sstepV_vecFloatRelOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecLane.sstepV_vecFloatRelOp

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecLane.vecB_invLanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecLane.vecB_invLanes

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecLane.vecB_invLanesF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecLane.vecB_invLanesF

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecLane.sstepV_vextractLaneF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecLane.sstepV_vextractLaneF
