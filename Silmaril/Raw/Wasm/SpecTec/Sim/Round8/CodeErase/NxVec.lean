module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.NxTypes

/-!
# Round 8 (copy of round 7 for `CODE` fields), encoder lemma: the SIMD and conversion encoders are free of `CODE` records

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).

Every operator encoder of `Sim/VecEncoding/Defs.lean` builds cases and tuples only.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim

@[simp] theorem ncB_sxV (a : Signedness) : ncB (Vec.sxV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_halfV (a : Half) : ncB (Vec.halfV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_intLaneV (a : IntShape) : ncB (Vec.intLaneV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_floatLaneV (a : FloatShape) : ncB (Vec.floatLaneV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_ishV (a : IntShape) : ncB (Vec.ishV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_fshV (a : FloatShape) : ncB (Vec.fshV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_shapeV (a : Shape) : ncB (Vec.shapeV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_ishapeV (a : IntShape) : ncB (Vec.ishapeV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem ncB_vvunopV (a : VecUnOp) : ncB (Vec.vvunopV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vvbinopV (a : VecBinOp) : ncB (Vec.vvbinopV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem ncB_vvternopV (a : VecTernOp) : ncB (Vec.vvternopV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem ncB_vvtestopV (a : VecTestOp) : ncB (Vec.vvtestopV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vIntUnOpV (a : VecIntUnOp) : ncB (Vec.vIntUnOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vFloatUnOpV (a : FloatUnOp) : ncB (Vec.vFloatUnOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vIntBinOpV (a : VecIntBinOp) : ncB (Vec.vIntBinOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vFloatBinOpV (a : VecFloatBinOp) : ncB (Vec.vFloatBinOpV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem ncB_vIntTernOpV (a : VecIntTernOp) : ncB (Vec.vIntTernOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vFloatTernOpV (a : VecFloatTernOp) : ncB (Vec.vFloatTernOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vIntRelOpV (a : IntRelOp) : ncB (Vec.vIntRelOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vFloatRelOpV (a : FloatRelOp) : ncB (Vec.vFloatRelOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vShiftOpV (a : VecShiftOp) : ncB (Vec.vShiftOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vSwizzleOpV (a : VecSwizzleOp) : ncB (Vec.vSwizzleOpV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem ncB_vExtUnOpV (a : VecExtUnOp) : ncB (Vec.vExtUnOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vExtBinOpV (a : VecExtBinOp) : ncB (Vec.vExtBinOpV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem ncB_vExtTernOpV (a : VecExtTernOp) : ncB (Vec.vExtTernOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_vConvertOpV (a : VecConvertOp) : ncB (Vec.vConvertOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_numTypeV (a : NumType) : ncB (Vec.numTypeV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem ncB_cvtOpV (a : ConvertOp) : ncB (Vec.cvtOpV a) = true := by
  cases a
  all_goals nxb_leaf

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
