module

public import Silmaril.Wasm.SpecTec.Sim20.VecFix.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixOps
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixFire20
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixFireV

/-!
# The 2.0 vector errata: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.VecFix`; see `docs/projects/spectec/README.md`, "vec-erratum".

* `VecFix.Defs`: the errata. `fixFamily` prepends float instances at `F32 X M` and `F64 X M` to
  `vunop_`, `vbinop_` and `vrelop_`; `extractCaseFix` restates the `VEXTRACT_LANE` case of
  `instr` and `admininstr` without its unbound `numtype` quantifier. `fixedV20` applies them on
  top of `StoreFix.fixedT20`; `simEnv20V B` is its environment.
* **`typedA_floatVec20V`**: every float `VUNOP`, `VBINOP` and `VRELOP` (all operators, both
  float shapes) is an `admininstr` of `simEnv20V B`, for every `B` (by evaluation, files
  `VecFix{Un,Bin,Rel}1..4`). Without the erratum the fourteen float-only ones are not
  (`VecRefute.not_typedA_floatOnly20T`).
* **`typedA_extract20V`**: every `VEXTRACT_LANE` that V2 accepts (`immediatesValid`), at every
  lane index, is an `admininstr` of `simEnv20V B`: the payload is typed (`typedV_shape20V`,
  `typedV_sx20V`, `typedV_laneidx20V`) and the corrected premise holds (`premsOk_extract20V`).
* **`not_typedA_extract20T`**: without the erratum, no valid `VEXTRACT_LANE` at lane 0 is an
  `admininstr` of `simEnv20T B`.
* **`fwd_vextractLaneNum`**: in any environment with the facts of `ExtractEnv` (rule 46 of
  `Step_pure`, the types of its quantifiers, `$lanes_` answered as V2 computes lanes), every V2
  pure step from `v128.const c; i32x4.extract_lane i` (or `i64x2`) is matched by
  `Step_pure/vextract_lane-num`, from the image of the source to the image of V2's successor.
  **`fwd_vextractLaneNum20V`** (the corrected script, `extractEnv20V`) and
  `fwd_vextractLaneNum20` (the original, `extractEnv20`) instantiate it at `Whole.storeB P`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecFix.typedA_floatVec20V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecFix.typedA_floatVec20V

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecFix.typedA_extract20V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecFix.typedA_extract20V

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecFix.not_typedA_extract20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecFix.not_typedA_extract20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecFix.fwd_vextractLaneNum20V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecFix.fwd_vextractLaneNum20V

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecFix.fwd_vextractLaneNum20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecFix.fwd_vextractLaneNum20
