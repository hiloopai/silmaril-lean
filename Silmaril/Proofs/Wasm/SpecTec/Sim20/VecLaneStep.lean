module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneFNum2

/-!
# The float vector operators as `Step`s of the corrected script

**`sstepV_vecFloatUnOp`**, **`sstepV_vecFloatBinOp`**, **`sstepV_vecFloatRelOp`**: under
`VecNumAgree (simEnv20V B) P`, every V2 pure step from `v128.const c; sh.op` (and the binary forms)
at a float shape is a `Step` of `simEnv20V B` between the images, at every state typed in
`simEnv20T B` that is `VOk` (every V2 state image is, `VecAgree.vOk_stateV`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (SStep cfgV TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V FloatVec typedA_floatVec20V)

variable {B : Builtins}

theorem typedV_vconstV (c : BitVec 128) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (adminToV (vconst c)) :=
  Sim.typedV_list_iff.1 (VecAgree.typedV_admins_valV (.vec c)) _ (by simp [adminsToV, Val.toAdmin])

/-- One vector constant and a float vector operator: a typed `admininstr*` of `simEnv20V`. -/
theorem typedV_src1 (c : BitVec 128) {i : V2.Instr} (hi : FloatVec i) :
    TypedV (simEnv20V B) adminsTy (.list (adminsToV [vconst c, .plain i])) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  simp only [Pure.adminsToV_eq_map, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact typedV_vconstV c
  · exact typedA_floatVec20V hi

/-- Two vector constants and a float vector operator: a typed `admininstr*` of `simEnv20V`. -/
theorem typedV_src2 (c₁ c₂ : BitVec 128) {i : V2.Instr} (hi : FloatVec i) :
    TypedV (simEnv20V B) adminsTy (.list (adminsToV [vconst c₁, vconst c₂, .plain i])) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  simp only [Pure.adminsToV_eq_map, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact typedV_vconstV c₁
  · exact typedV_vconstV c₂
  · exact typedA_floatVec20V hi

/-- A firing of a `Step_pure` rule of the corrected script, between typed codes at a state typed
in `simEnv20T` that is `VOk`, is a `Step`. -/
theorem sstepV_of_fires {k : Nat} {z : Value} {is js : List Value}
    (hz : TypedV (simEnv20T B) stateT z) (hv : VecAgree.VOk z)
    (his : TypedV (simEnv20V B) adminsTy (.list is)) (hjs : TypedV (simEnv20V B) adminsTy (.list js))
    (hf : Sim.Fires (simEnv20V B) "Step_pure" k (.tuple [.list is, .list js])) :
    SStep (simEnv20V B) (cfgV z is) (cfgV z js) := by
  obtain ⟨ty, rules, hrel⟩ := VecAgree.findRel_pure20V B
  exact VecAgree.sstepV_pure (VecAgree.typedV_TtoV VecAgree.ffT_state hv hz) his hjs
    ((Sim.dderives_iff_fires hrel).2 ⟨k, hf⟩)

/-- **The float `vunop`s are `Step`s of the corrected script.** -/
theorem sstepV_vecFloatUnOp {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {z : Value}
    (hz : TypedV (simEnv20T B) stateT z) (hv : VecAgree.VOk z) {s : FloatShape} {op : FloatUnOp}
    {c : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecFloatUnOp s op)] code') :
    SStep (simEnv20V B) (cfgV z (adminsToV [vconst c, .plain (.vecFloatUnOp s op)]))
      (cfgV z (adminsToV code')) := by
  have hf := fwd_vecFloatUnOp20V hA h
  obtain ⟨r, -, rfl⟩ := pureStep_vecFloatUnOp_inv h
  exact sstepV_of_fires hz hv (typedV_src1 c trivial) (VecAgree.typedV_admins_valV (.vec r)) hf

/-- **The float `vbinop`s are `Step`s of the corrected script.** -/
theorem sstepV_vecFloatBinOp {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {z : Value}
    (hz : TypedV (simEnv20T B) stateT z) (hv : VecAgree.VOk z) {s : FloatShape}
    {op : V2.VecFloatBinOp} {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatBinOp s op)] code') :
    SStep (simEnv20V B) (cfgV z (adminsToV [vconst c₁, vconst c₂, .plain (.vecFloatBinOp s op)]))
      (cfgV z (adminsToV code')) := by
  have hf := fwd_vecFloatBinOp20V hA h
  obtain ⟨r, -, rfl⟩ := pureStep_vecFloatBinOp_inv h
  exact sstepV_of_fires hz hv (typedV_src2 c₁ c₂ trivial) (VecAgree.typedV_admins_valV (.vec r)) hf

/-- **The float `vrelop`s are `Step`s of the corrected script.** -/
theorem sstepV_vecFloatRelOp {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {z : Value}
    (hz : TypedV (simEnv20T B) stateT z) (hv : VecAgree.VOk z) {s : FloatShape}
    {op : FloatRelOp} {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatRelOp s op)] code') :
    SStep (simEnv20V B) (cfgV z (adminsToV [vconst c₁, vconst c₂, .plain (.vecFloatRelOp s op)]))
      (cfgV z (adminsToV code')) := by
  have hf := fwd_vecFloatRelOp20V hA h
  rw [pureStep_vecFloatRelOp_inv h] at hf ⊢
  exact sstepV_of_fires hz hv (typedV_src2 c₁ c₂ trivial) (VecAgree.typedV_admins_valV (.vec _)) hf

end Silmaril.Wasm.SpecTec.Sim20.VecLane
