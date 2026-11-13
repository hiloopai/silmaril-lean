module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneB
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgree20

/-!
# `vextract_lane-num` at float shapes

Rule 46 of `Step_pure` also covers `f32x4.extract_lane` and `f64x2.extract_lane`: `nt` is `F32`
(`F64`) and `$lanes_(nt X N, c)` must answer the lanes as floats. `storeB P` does not; `vecB P`
does (`vecB_lanesF`).

* `fires_vextractLaneF`: in any environment with the facts of `FExtractEnv`, rule 46 fires at a
  float shape, to `CONST nt` of the lane.
* **`fwd_vextractLaneF20V`**: at `vecB P`, every V2 pure step from
  `v128.const c; f32x4.extract_lane i` (or `f64x2`) is matched by rule 46 of the corrected script.
* **`sstepV_vextractLaneF`**: it is a `Step` of `simEnv20V (vecB P)` at every V2 state typed in
  `simEnv20T (vecB P)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires SStep cfgV TypedV ValsOnly QuantsOk stateT evalExp_tup2
  evalExp_case)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V vextractLaneNumRule ntShapeE pureStep_extract_inv)

/-- **The facts about `env` that make rule 46 fire forward at float shapes.** -/
structure FExtractEnv (env : Env) : Prop where
  rule : HasRuleAt env "Step_pure" "%~>%" 46 vextractLaneNumRule
  vec : ∀ c : BitVec 128, TypedV env (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]) (pctV c.toNat)
  numtype : ∀ t, TypedV env (.varT "numtype" []) (numTypeV t)
  num : ∀ (t : FloatType) (x : BitVec t.width), Pure.TypedAt env "num_" "nt" (numTypeV (.float t))
    (Sim.floatV t x)
  N : ∀ k : Nat, TypedV env (.varT "N" []) (.num (.natN k))
  laneidx : ∀ j : LaneIdx, TypedV env (.varT "laneidx" []) (pctV j.val)
  lanesDef : ∃ ps t, env.findDef? "lanes_" = some (ps, t, [])
  lanes : ∀ (t : FloatType) (c : BitVec 128),
    env.builtins.call "lanes_" [.val (fshapeV t), .val (pctV c.toNat)] = some (.list (lanesFV t c))

/-- The float lane `i` of `c`. -/
def laneF (t : FloatType) (c : BitVec 128) (i : Nat) : BitVec t.width :=
  (Numerics.lanes t.width (128 / t.width) c).getD i 0

theorem getElem?_lanesFV (t : FloatType) (c : BitVec 128) {j : Nat} (hj : j < 128 / t.width) :
    (lanesFV t c)[j]? = some (Sim.floatV t (laneF t c j)) := by
  have hl : j < (Numerics.lanes t.width (128 / t.width) c).length := by
    simpa [Numerics.lanes] using hj
  simp [lanesFV, laneF, List.getElem?_map, List.getElem?_eq_getElem hl]

theorem fshapeV_eq (t : FloatType) :
    fshapeV t = .case "%X%" (.tuple [numTypeV (.float t), pctV (128 / t.width)]) := by
  cases t <;> rfl

/-- **Rule 46 fires at a float shape**, for a lane `i` in range, to `CONST nt` of the lane. -/
theorem fires_vextractLaneF {env : Env} (E : FExtractEnv env) (t : FloatType) (c : BitVec 128)
    (i : LaneIdx) (hi : i.val < 128 / t.width) :
    Fires env "Step_pure" 46 (.tuple [
      .list [adminToV (vconst c), .case "VEXTRACT_LANE" (.tuple [fshapeV t, .opt none, pctV i.val])],
      .list [.case "CONST" (.tuple [numTypeV (.float t), Sim.floatV t (laneF t c i.val)])]]) := by
  let σ : List (IL.Id × Value) := [("c_1", pctV c.toNat), ("nt", numTypeV (.float t)),
    ("N", .num (.natN (128 / t.width))), ("i", pctV i.val), ("c_2", Sim.floatV t (laneF t c i.val))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fc : (VarEnv.empty.bindVals σ).findVal? "c_1" = some (pctV c.toNat) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "nt" = some (numTypeV (.float t)) := rfl
  have fN : (VarEnv.empty.bindVals σ).findVal? "N" = some (.num (.natN (128 / t.width))) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.val) := rfl
  have fx : (VarEnv.empty.bindVals σ).findVal? "c_2" = some (Sim.floatV t (laneF t c i.val)) := rfl
  have hq : QuantsOk env (VarEnv.empty.bindVals σ)
      (match vextractLaneNumRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fc (E.vec c _ hρ) (QuantsOk.cons ft (E.numtype _ _ hρ)
      (QuantsOk.cons fN (E.N _ _ hρ) (QuantsOk.cons fi (E.laneidx i _ hρ)
        (QuantsOk.cons fx (E.num t _ _ hρ ft) QuantsOk.nil))))
  have eSh : EvalExp env (VarEnv.empty.bindVals σ) ntShapeE (fshapeV t) := by
    rw [fshapeV_eq]
    exact evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var ft))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, Equiv.Validation.evalExps_cons_iff.2
        ⟨_, _, rfl, evalExp_var fN, Equiv.Validation.evalExps_nil_iff.2 rfl⟩, rfl⟩)))
  have hl : EvalExp env (VarEnv.empty.bindVals σ)
      (.listE [vconstE "c_1", .caseE "VEXTRACT_LANE" (.tupE [ntShapeE, .optE none, .varE "i"])])
      (.list [adminToV (vconst c), .case "VEXTRACT_LANE" (.tuple [fshapeV t, .opt none,
        pctV i.val])]) :=
    Pure.evalExp_list2 (evalExp_vconst fc) (evalExp_case (Sim.evalExp_tup3 eSh
      (evalExp_optE_none_iff.2 rfl) (evalExp_var fi)))
  have hr : EvalExp env (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c_2"])])
      (.list [.case "CONST" (.tuple [numTypeV (.float t), Sim.floatV t (laneF t c i.val)])]) :=
    Sim.evalExp_list1 (evalExp_pairV ft fx)
  have eLanes : EvalExp env (VarEnv.empty.bindVals σ)
      (.callE "lanes_" [.expA ntShapeE, .expA (.varE "c_1")]) (.list (lanesFV t c)) := by
    obtain ⟨ps, ty, hd⟩ := E.lanesDef
    exact evalExp_callE_iff.2 (Equiv.ExecBuiltins.callDef_of_builtin_nil
      (findDef_none_bindVals σ _) hd
      (evalArgs_cons eSh (evalArgs_cons (evalExp_var fc) evalArgs_nil)) (E.lanes t c))
  have eLane : EvalExp env (VarEnv.empty.bindVals σ)
      (.idxE (.callE "lanes_" [.expA ntShapeE, .expA (.varE "c_1")])
        (.projE (.uncaseE (.varE "i") "%") (0 : Int))) (Sim.floatV t (laneF t c i.val)) :=
    Sim.RefsGC.evalExp_idx eLanes (Sim.RefsGC.evalExp_unpct (evalExp_var fi))
      (getElem?_lanesFV t c hi)
  refine Pure.fires_of_ruleAt E.rule σ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  rw [List.mem_singleton.1 hpr]
  exact .ifPr (Whole.evalExp_eqTrue (evalExp_var fx) eLane)

/-! ## Forward from V2 -/

theorem adminsToV_extractF (t : FloatType) (c : BitVec 128) (i : LaneIdx) :
    adminsToV [vconst c, .plain (.vecExtractLane (.float (fshapeOf t)) none i)] =
      [adminToV (vconst c), .case "VEXTRACT_LANE" (.tuple [fshapeV t, .opt none, pctV i.val])] := by
  cases t <;> rfl

theorem adminsToV_extractFRes (t : FloatType) (c : BitVec 128) (i : LaneIdx) :
    adminsToV [(Val.num ⟨(Shape.float (fshapeOf t)).unpacked,
      VecExtractLane (.float (fshapeOf t)) none i.val c⟩).toAdmin] =
      [.case "CONST" (.tuple [numTypeV (.float t), Sim.floatV t (laneF t c i.val)])] := by
  cases t <;> rfl

/-- **`vextract_lane` at float shapes, forward**, in any environment with `FExtractEnv`. -/
theorem fwd_vextractLaneF {env : Env} (E : FExtractEnv env) {P : Profile} (t : FloatType)
    {c : BitVec 128} {i : LaneIdx} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane (.float (fshapeOf t)) none i)] code') :
    Fires env "Step_pure" 46 (.tuple [.list (adminsToV [vconst c, .plain (.vecExtractLane
      (.float (fshapeOf t)) none i)]), .list (adminsToV code')]) := by
  obtain ⟨hi, rfl⟩ := pureStep_extract_inv h
  rw [adminsToV_extractF, adminsToV_extractFRes]
  have hi' : i.val < 128 / t.width := by cases t <;> exact hi
  exact fires_vextractLaneF E t c i hi'

theorem ffT_numNt : VecAgree.ffT (.varT "num_" [.expA (.varE "nt")]) := by
  simp [VecAgree.ffT, Sim.Round7.Script.evTyp, Sim.Round7.Script.evArgs, Sim.Round7.Script.evArg,
    Sim.Round7.Script.evExp, ElseAgree.GoodT, ElseAgree.tyEvB, VecAgree.fams]

/-- **The corrected script has the facts of `FExtractEnv`** at builtins answering `$lanes_` at
float shapes. -/
theorem fExtractEnv20V {B : Builtins}
    (hL : ∀ t c, B.call "lanes_" [.val (fshapeV t), .val (pctV c.toNat)] = some (.list (lanesFV t c))) :
    FExtractEnv (simEnv20V B) where
  rule := VecFix.hasRuleAt_vextractLaneNum20V B
  vec := VecFix.typedV_vecV128_20V
  numtype := VecFix.typedV_numtype20V
  num t x ρ hρ hx := VecAgree.hasTyp_20toV hρ (by decide) ffT_numNt
    (VecAgree.vOk_of_vokB _ (VecAgree.vokB_floatV t x))
    (Pure.hasTyp_num_float20 t x (evalExp_var hx))
  N := VecFix.typedV_N20V
  laneidx := VecFix.typedV_laneidx20V
  lanesDef := VecFix.findDef_lanes20V
  lanes t c := by
    rw [simEnv20V, Env.builtins_withBuiltins]
    exact hL t c

/-- **`vextract_lane` at `f32x4`/`f64x2` forward, in the corrected script** at `vecB P`. -/
theorem fwd_vextractLaneF20V {P : Profile} (t : FloatType) {c : BitVec 128} {i : LaneIdx}
    {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane (.float (fshapeOf t)) none i)] code') :
    Fires (simEnv20V (vecB P)) "Step_pure" 46 (.tuple [.list (adminsToV [vconst c,
      .plain (.vecExtractLane (.float (fshapeOf t)) none i)]), .list (adminsToV code')]) :=
  fwd_vextractLaneF (fExtractEnv20V (vecB_lanesF P)) t h

/-- **`vextract_lane` at `f32x4`/`f64x2` is a `Step` of the corrected script** at `vecB P`, at every
state typed in `simEnv20T (vecB P)` that is `VOk`. -/
theorem sstepV_vextractLaneF {P : Profile} (t : FloatType) {z : Value}
    (hz : TypedV (simEnv20T (vecB P)) stateT z) (hv : VecAgree.VOk z) {c : BitVec 128}
    {i : LaneIdx} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane (.float (fshapeOf t)) none i)] code') :
    SStep (simEnv20V (vecB P))
      (cfgV z (adminsToV [vconst c, .plain (.vecExtractLane (.float (fshapeOf t)) none i)]))
      (cfgV z (adminsToV code')) := by
  have hf := fwd_vextractLaneF20V t h
  obtain ⟨-, rfl⟩ := pureStep_extract_inv h
  have hsrc : TypedV (simEnv20V (vecB P)) StepFix.adminsTy
      (.list (adminsToV [vconst c, .plain (.vecExtractLane (.float (fshapeOf t)) none i)])) := by
    refine Sim.typedV_list_iff.2 fun u hu => ?_
    simp only [Pure.adminsToV_eq_map, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact typedV_vconstV c
    · exact VecFix.typedA_extract20V _ _ _ (by
        cases t <;> simp [V2.Instr.immediatesValid, fshapeOf, Shape.laneWidth, FloatShape.laneWidth])
  exact sstepV_of_fires hz hv hsrc (VecAgree.typedV_admins_valV _) hf

end Silmaril.Wasm.SpecTec.Sim20.VecLane
