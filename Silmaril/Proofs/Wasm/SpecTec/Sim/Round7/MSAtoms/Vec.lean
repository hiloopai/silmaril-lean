module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.Values

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge: the non-memory SIMD encoders

`Vec.vecInstrV?` (the twenty-four non-memory SIMD instructions) and `Vec.convertInstrV` (the
scalar conversions) have no atom of `HStep.hAtoms`, and `vecInstrV?` answers every one of the
twenty-four (`vecInstrV?_some`), so `instrToV` never falls back to the schema reading on them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)
open HStep (hAtoms)
open Sim.Vec

theorem nh_vsxV (s : Signedness) : NH (Vec.sxV s) := by
  cases s <;> simp only [Vec.sxV, caseNilV] <;> nh_close

theorem nh_halfV (h : Half) : NH (halfV h) := by
  cases h <;> simp only [halfV, caseNilV] <;> nh_close

theorem nh_ishV (s : IntShape) : NH (ishV s) := by
  cases s <;> simp only [ishV, intLaneV, caseNilV, pctV] <;> nh_close

theorem nh_fshV (s : FloatShape) : NH (fshV s) := by
  cases s <;> simp only [fshV, floatLaneV, caseNilV, pctV] <;> nh_close

theorem nh_shapeV (s : Shape) : NH (shapeV s) := by
  cases s
  · exact nh_ishV _
  · exact nh_fshV _

theorem nh_ishapeV (s : IntShape) : NH (ishapeV s) := by
  have h := nh_ishV s
  simp only [ishapeV]
  nh_close

theorem nh_bshapeV : NH bshapeV := by
  have h := nh_ishV .i8x16
  simp only [bshapeV]
  nh_close

theorem nh_laneIdxV (i : LaneIdx) : NH (laneIdxV i) := nh_pctV _

theorem nh_vvunopV (o : VecUnOp) : NH (vvunopV o) := by
  cases o; simp only [vvunopV, caseNilV]; nh_close

theorem nh_vvbinopV (o : VecBinOp) : NH (vvbinopV o) := by
  cases o <;> simp only [vvbinopV, caseNilV] <;> nh_close

theorem nh_vvternopV (o : VecTernOp) : NH (vvternopV o) := by
  cases o; simp only [vvternopV, caseNilV]; nh_close

theorem nh_vvtestopV (o : VecTestOp) : NH (vvtestopV o) := by
  cases o; simp only [vvtestopV, caseNilV]; nh_close

theorem nh_vIntUnOpV (o : VecIntUnOp) : NH (vIntUnOpV o) := by
  cases o <;> simp only [vIntUnOpV, caseNilV] <;> nh_close [nh_vsxV]

theorem nh_vFloatUnOpV (o : FloatUnOp) : NH (vFloatUnOpV o) := by
  cases o <;> simp only [vFloatUnOpV, caseNilV] <;> nh_close [nh_vsxV]

theorem nh_vIntBinOpV (o : VecIntBinOp) : NH (vIntBinOpV o) := by
  cases o <;> simp only [vIntBinOpV, caseNilV] <;> nh_close [nh_vsxV]

theorem nh_vFloatBinOpV (o : VecFloatBinOp) : NH (vFloatBinOpV o) := by
  cases o <;> simp only [vFloatBinOpV, caseNilV] <;> nh_close [nh_vsxV]

theorem nh_vIntTernOpV (o : VecIntTernOp) : NH (vIntTernOpV o) := by
  cases o; simp only [vIntTernOpV, caseNilV]; nh_close [nh_vsxV]

theorem nh_vFloatTernOpV (o : VecFloatTernOp) : NH (vFloatTernOpV o) := by
  cases o <;> simp only [vFloatTernOpV, caseNilV] <;> nh_close [nh_vsxV]

theorem nh_vIntRelOpV (o : IntRelOp) : NH (vIntRelOpV o) := by
  cases o <;> simp only [vIntRelOpV, caseNilV] <;> nh_close [nh_vsxV]

theorem nh_vFloatRelOpV (o : FloatRelOp) : NH (vFloatRelOpV o) := by
  cases o <;> simp only [vFloatRelOpV, caseNilV] <;> nh_close [nh_vsxV]

theorem nh_vShiftOpV (o : VecShiftOp) : NH (vShiftOpV o) := by
  cases o <;> simp only [vShiftOpV, caseNilV] <;> nh_close [nh_vsxV]

theorem nh_vSwizzleOpV (o : VecSwizzleOp) : NH (vSwizzleOpV o) := by
  cases o <;> simp only [vSwizzleOpV, caseNilV] <;> nh_close [nh_vsxV]

theorem nh_vExtUnOpV (o : VecExtUnOp) : NH (vExtUnOpV o) := by
  cases o; simp only [vExtUnOpV]; nh_close [nh_vsxV, nh_halfV]

theorem nh_vExtBinOpV (o : VecExtBinOp) : NH (vExtBinOpV o) := by
  cases o <;> simp only [vExtBinOpV, caseNilV] <;> nh_close [nh_vsxV, nh_halfV]

theorem nh_vExtTernOpV (o : VecExtTernOp) : NH (vExtTernOpV o) := by
  cases o; simp only [vExtTernOpV, caseNilV]; nh_close [nh_vsxV, nh_halfV]

theorem nh_vConvertOpV (o : VecConvertOp) : NH (vConvertOpV o) := by
  cases o <;> simp only [vConvertOpV, caseNilV]
  case convert h s =>
    have h₁ : NH (.opt (h.map halfV)) := noAtoms_opt_map fun x _ => nh_halfV x
    have h₂ := nh_vsxV s
    nh_close
  all_goals (try split) <;> nh_close [nh_vsxV, nh_halfV]

/-- **`vecInstrV?` has no atom of `hAtoms`.** -/
theorem nh_vecInstrV? {i : Instr} {v : Value} (h : vecInstrV? i = some v) : NH v := by
  cases i <;> simp only [vecInstrV?, Option.some.injEq, reduceCtorEq] at h <;> subst h
  case vecShuffle ls =>
    have h₁ : NH (.list (ls.map laneIdxV)) := noAtoms_list_map fun x _ => nh_laneIdxV x
    have h₂ := nh_bshapeV
    nh_close
  case vecExtractLane s sx l =>
    have h₁ : NH (.opt (sx.map Vec.sxV)) := noAtoms_opt_map fun x _ => nh_vsxV x
    have h₂ := nh_shapeV s
    have h₃ := nh_laneIdxV l
    nh_close
  all_goals nh_close [nh_vvunopV, nh_vvbinopV, nh_vvternopV, nh_vvtestopV, nh_ishV, nh_fshV,
    nh_vIntUnOpV, nh_vFloatUnOpV, nh_vIntBinOpV, nh_vFloatBinOpV, nh_vIntTernOpV,
    nh_vFloatTernOpV, nh_vIntRelOpV, nh_vFloatRelOpV, nh_vShiftOpV, nh_ishapeV, nh_bshapeV,
    nh_vSwizzleOpV, nh_vExtUnOpV, nh_vExtBinOpV, nh_vExtTernOpV, nh_vsxV, nh_shapeV,
    nh_vConvertOpV, nh_laneIdxV, vecTypeV, caseNilV]

/-- **`convertInstrV` has no atom of `hAtoms`.** -/
theorem nh_convertInstrV (op : ConvertOp) : NH (convertInstrV op) := by
  have h₁ : ∀ t, NH (numTypeV t) := by
    intro t
    rcases t with t | t <;> cases t <;> simp only [numTypeV, caseNilV] <;> nh_close
  have h₂ : NH (cvtOpV op) := by
    cases op <;> simp only [cvtOpV, caseNilV] <;> nh_close [nh_vsxV]
  have h₃ := h₁ op.target
  have h₄ := h₁ op.source
  simp only [convertInstrV]
  nh_close

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
