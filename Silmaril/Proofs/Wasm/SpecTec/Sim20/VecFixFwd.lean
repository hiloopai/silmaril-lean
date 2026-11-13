module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixFire

/-!
# `vextract_lane` at number lanes, forward from V2

**`fwd_vextractLaneNum`**: in any environment with the facts of `ExtractEnv`, every V2 pure step
from `v128.const c; i32x4.extract_lane i` (or `i64x2`) is matched by rule 46 of `Step_pure`,
from the image of the source to the image of V2's successor.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (Fires)

/-- The only V2 step from `v128.const c; sh.extract_lane eps i`. -/
theorem pureStep_extract_inv {P : Numerics.Profile} {sh : Shape} {c : BitVec 128} {i : LaneIdx}
    {code' : List Admin} (h : PureStep P [vconst c, .plain (.vecExtractLane sh none i)] code') :
    i.val < sh.lanes ∧
      code' = [(Val.num ⟨sh.unpacked, VecExtractLane sh none i.val c⟩).toAdmin] := by
  generalize hl : [vconst c, Admin.plain (V2.Instr.vecExtractLane sh none i)] = l at h
  cases h with
  | vecExtractLane hi =>
    simp only [vconst, List.cons.injEq, Admin.plain.injEq, V2.Instr.vecConst.injEq,
      V2.Instr.vecExtractLane.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨hi, rfl⟩
  | trapVals hne =>
    exfalso
    have hm : Admin.trap ∈ [vconst c, Admin.plain (V2.Instr.vecExtractLane sh none i)] := by
      rw [hl]; simp
    simp [vconst] at hm
  | _ => simp_all [vals, vconst, aref]

/-- The integer shape whose lanes are of type `t`. -/
def numShape : IntType → IntShape
  | .i32 => .i32x4
  | .i64 => .i64x2

/-- The image of the source, at the shape of an integer type with number lanes. -/
theorem adminsToV_extract (t : IntType) (c : BitVec 128) (i : LaneIdx) :
    adminsToV [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)] =
      [adminToV (vconst c), .case "VEXTRACT_LANE" (.tuple [Whole.shapeV20 (numPack t), .opt none,
        pctV i.val])] := by
  cases t <;> rfl

/-- The image of V2's successor: `CONST nt` of the lane. -/
theorem adminsToV_extractRes (t : IntType) (c : BitVec 128) (i : LaneIdx) :
    adminsToV [(Val.num ⟨(Shape.int (numShape t)).unpacked,
      VecExtractLane (.int (numShape t)) none i.val c⟩).toAdmin] =
      [.case "CONST" (.tuple [numTypeV (.int t),
        pctV ((Numerics.lanes (numPack t).width (128 / (numPack t).width) c).getD i.val 0).toNat])] := by
  cases t <;> rfl

/-- **`vextract_lane` at `i32x4` and `i64x2`, forward**: rule 46 fires from the image of every V2
pure step's source to the image of its successor. -/
theorem fwd_vextractLaneNum {env : Env} (E : ExtractEnv env) {P : Numerics.Profile} (t : IntType)
    {c : BitVec 128} {i : LaneIdx} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecExtractLane
      (.int (numShape t)) none i)] code') :
    Fires env "Step_pure" 46 (.tuple [.list (adminsToV [vconst c, .plain (.vecExtractLane
      (.int (numShape t)) none i)]), .list (adminsToV code')]) := by
  obtain ⟨hi, rfl⟩ := pureStep_extract_inv h
  rw [adminsToV_extract]
  have hi' : i.val < 128 / (numPack t).width := by cases t <;> exact hi
  have hf := fires_vextractLaneNum E t c i hi'
  rw [adminsToV_extractRes]
  exact hf

end Silmaril.Wasm.SpecTec.Sim20.VecFix
