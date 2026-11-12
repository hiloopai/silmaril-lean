module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.NxTypes

/-!
# Round 7, encoder lemma: the SIMD and conversion encoders are free of `EXPORTS` records

Every operator encoder of `Sim/VecEncoding/Defs.lean` builds cases and tuples only.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim

@[simp] theorem nxB_sxV (a : Signedness) : nxB (Vec.sxV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_halfV (a : Half) : nxB (Vec.halfV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_intLaneV (a : IntShape) : nxB (Vec.intLaneV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_floatLaneV (a : FloatShape) : nxB (Vec.floatLaneV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_ishV (a : IntShape) : nxB (Vec.ishV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_fshV (a : FloatShape) : nxB (Vec.fshV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_shapeV (a : Shape) : nxB (Vec.shapeV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_ishapeV (a : IntShape) : nxB (Vec.ishapeV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem nxB_vvunopV (a : VecUnOp) : nxB (Vec.vvunopV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vvbinopV (a : VecBinOp) : nxB (Vec.vvbinopV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem nxB_vvternopV (a : VecTernOp) : nxB (Vec.vvternopV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem nxB_vvtestopV (a : VecTestOp) : nxB (Vec.vvtestopV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vIntUnOpV (a : VecIntUnOp) : nxB (Vec.vIntUnOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vFloatUnOpV (a : FloatUnOp) : nxB (Vec.vFloatUnOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vIntBinOpV (a : VecIntBinOp) : nxB (Vec.vIntBinOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vFloatBinOpV (a : VecFloatBinOp) : nxB (Vec.vFloatBinOpV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem nxB_vIntTernOpV (a : VecIntTernOp) : nxB (Vec.vIntTernOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vFloatTernOpV (a : VecFloatTernOp) : nxB (Vec.vFloatTernOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vIntRelOpV (a : IntRelOp) : nxB (Vec.vIntRelOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vFloatRelOpV (a : FloatRelOp) : nxB (Vec.vFloatRelOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vShiftOpV (a : VecShiftOp) : nxB (Vec.vShiftOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vSwizzleOpV (a : VecSwizzleOp) : nxB (Vec.vSwizzleOpV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem nxB_vExtUnOpV (a : VecExtUnOp) : nxB (Vec.vExtUnOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vExtBinOpV (a : VecExtBinOp) : nxB (Vec.vExtBinOpV a) = true := by
  cases a
  all_goals nxb_leaf

set_option linter.unusedTactic false in
@[simp] theorem nxB_vExtTernOpV (a : VecExtTernOp) : nxB (Vec.vExtTernOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_vConvertOpV (a : VecConvertOp) : nxB (Vec.vConvertOpV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_numTypeV (a : NumType) : nxB (Vec.numTypeV a) = true := by
  cases a
  all_goals nxb_leaf

@[simp] theorem nxB_cvtOpV (a : ConvertOp) : nxB (Vec.cvtOpV a) = true := by
  cases a
  all_goals nxb_leaf

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
