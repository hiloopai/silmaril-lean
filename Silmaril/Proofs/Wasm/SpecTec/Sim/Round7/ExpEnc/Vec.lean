module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.Types

/-!
# Round 7, encoder lemma: the SIMD and conversion encoders are `EXPORTS`-free

Every operator encoder of `Sim/VecEncoding/Defs.lean` builds cases and tuples only.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim

@[simp] theorem efB_sxV (a : Signedness) : efB (Vec.sxV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_halfV (a : Half) : efB (Vec.halfV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_intLaneV (a : IntShape) : efB (Vec.intLaneV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_floatLaneV (a : FloatShape) : efB (Vec.floatLaneV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_ishV (a : IntShape) : efB (Vec.ishV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_fshV (a : FloatShape) : efB (Vec.fshV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_shapeV (a : Shape) : efB (Vec.shapeV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_ishapeV (a : IntShape) : efB (Vec.ishapeV a) = true := by
  cases a
  all_goals efb_leaf

set_option linter.unusedTactic false in
@[simp] theorem efB_vvunopV (a : VecUnOp) : efB (Vec.vvunopV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vvbinopV (a : VecBinOp) : efB (Vec.vvbinopV a) = true := by
  cases a
  all_goals efb_leaf

set_option linter.unusedTactic false in
@[simp] theorem efB_vvternopV (a : VecTernOp) : efB (Vec.vvternopV a) = true := by
  cases a
  all_goals efb_leaf

set_option linter.unusedTactic false in
@[simp] theorem efB_vvtestopV (a : VecTestOp) : efB (Vec.vvtestopV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vIntUnOpV (a : VecIntUnOp) : efB (Vec.vIntUnOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vFloatUnOpV (a : FloatUnOp) : efB (Vec.vFloatUnOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vIntBinOpV (a : VecIntBinOp) : efB (Vec.vIntBinOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vFloatBinOpV (a : VecFloatBinOp) : efB (Vec.vFloatBinOpV a) = true := by
  cases a
  all_goals efb_leaf

set_option linter.unusedTactic false in
@[simp] theorem efB_vIntTernOpV (a : VecIntTernOp) : efB (Vec.vIntTernOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vFloatTernOpV (a : VecFloatTernOp) : efB (Vec.vFloatTernOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vIntRelOpV (a : IntRelOp) : efB (Vec.vIntRelOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vFloatRelOpV (a : FloatRelOp) : efB (Vec.vFloatRelOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vShiftOpV (a : VecShiftOp) : efB (Vec.vShiftOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vSwizzleOpV (a : VecSwizzleOp) : efB (Vec.vSwizzleOpV a) = true := by
  cases a
  all_goals efb_leaf

set_option linter.unusedTactic false in
@[simp] theorem efB_vExtUnOpV (a : VecExtUnOp) : efB (Vec.vExtUnOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vExtBinOpV (a : VecExtBinOp) : efB (Vec.vExtBinOpV a) = true := by
  cases a
  all_goals efb_leaf

set_option linter.unusedTactic false in
@[simp] theorem efB_vExtTernOpV (a : VecExtTernOp) : efB (Vec.vExtTernOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_vConvertOpV (a : VecConvertOp) : efB (Vec.vConvertOpV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_numTypeV (a : NumType) : efB (Vec.numTypeV a) = true := by
  cases a
  all_goals efb_leaf

@[simp] theorem efB_cvtOpV (a : ConvertOp) : efB (Vec.cvtOpV a) = true := by
  cases a
  all_goals efb_leaf

end Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
