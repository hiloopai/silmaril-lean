module

public import Silmaril.Wasm.SpecTec.Sim20.VecAgree.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim20.VecAgree.Typ
public import Silmaril.Raw.Wasm.SpecTec.Sim20.VecAgree.Fam
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeEnvX
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeRel
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeImg
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeLift
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgree20

/-!
# Typing across the 2.0 vector errata: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.VecAgree`; see `docs/projects/spectec/README.md`, "vec".

* `Raw/…/VecAgree/Typ`: **`hasTyp_vec`**. Two environments that evaluate alike, whose type
  tables agree off three families and whose instance lists at a family agree with a two-instance
  prefix (`FamRel`), type alike in one direction at values whose family operators are float-shape
  safe (`VOk`): what the first types, the second types (at fuel `3 n + C`).
* `Raw/…/VecAgree/Fam`: the prepended float instances, evaluated in every environment.
* `VecAgreeEnvX`: `simEnv20T B` to `simEnv20X B` (the `VEXTRACT_LANE` repair) is a round 4 repair
  pair (`envSameX`, `typRepairX`, the original case dead: `deadCase_extract`); `hasTyp_toX`.
* `VecAgreeCheck`, `VecAgreeLk`, `VecAgreeEnvV`, `VecAgreeRel`: `simEnv20X B` to `simEnv20V B` is
  a `FamRel` pair (`famRelV`, with the kernel check `tableOkB_fixedX20`), so
  **`typedV_TtoV`**: `TypedV (simEnv20T B) t v → TypedV (simEnv20V B) t v` at every `VOk` value
  and every type naming no family directly.
* `VecAgreeVOk`, `VecAgreeImg`: every V2 state, code and configuration image is `VOk`
  (`vOk_stateV`, `vOk_adminsToV`, `vOk_configV`).
* `VecAgreeLift`: **`sstepV_vextractLaneNum`**, `vextract_lane-num` at `i32x4`/`i64x2` is a `Step`
  of `simEnv20V (storeB P)` at every V2 state typed in `simEnv20T`; `sstepV_vextractLaneNum_typF`
  at the state of a `TypF` configuration over a `StoreOkB` store.
* `VecAgree20`: `hasTyp_20toV`, the same transfer from the original script `simEnv20`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecAgree.hasTyp_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecAgree.hasTyp_vec

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecAgree.typedV_TtoV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecAgree.typedV_TtoV

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecAgree.vOk_stateV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecAgree.vOk_stateV

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecAgree.sstepV_vextractLaneNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecAgree.sstepV_vextractLaneNum

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecAgree.sstepV_vextractLaneNum_typF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecAgree.sstepV_vextractLaneNum_typF
