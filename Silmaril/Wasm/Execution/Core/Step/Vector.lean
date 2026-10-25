module

public import Silmaril.Wasm.Execution.Core.Store
public import Silmaril.Wasm.Numerics.VectorProfile

@[expose] public section

/-! # Reduction family: vector instructions (pure, profile-dependent)

Spec rules (all 25 present): `Step_pure/vvunop`, `vvbinop`, `vvternop`,
`vvtestop`, `vunop-val`, `vunop-trap`, `vbinop-val`, `vbinop-trap`, `vternop-val`,
`vternop-trap`, `vtestop`, `vrelop`, `vshiftop`, `vbitmask`, `vswizzlop`,
`vshuffle`, `vsplat`, `vextract_lane-num`, `vextract_lane-pack` (one constructor,
the sign decides), `vreplace_lane`, `vextunop`, `vextbinop`, `vextternop`,
`vnarrow`, `vcvtop`.

Integer-shape operators are deterministic functions; float-shape and the
extended/narrowing/conversion operators are result relations from
`Numerics/VectorProfile.lean` (the profile-aware packaging of the merged vector
numerics library). A `-trap` rule fires when the result set is empty.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics

/-- `VCONST V128 c`. -/
abbrev vconst (b : BitVec 128) : Admin := .plain (.vecConst b)

inductive VectorStep (P : Profile) : List Admin → List Admin → Prop where
  /-- `Step_pure/vvunop`. -/
  | vecUnOp (op : VecUnOp) (a : V128) :
      VectorStep P [vconst a, .plain (.vecUnOp op)] [vconst (vvunop op a)]
  /-- `Step_pure/vvbinop`. -/
  | vecBinOp (op : VecBinOp) (a b : V128) :
      VectorStep P [vconst a, vconst b, .plain (.vecBinOp op)] [vconst (vvbinop op a b)]
  /-- `Step_pure/vvternop`. -/
  | vecTernOp (op : VecTernOp) (a b c : V128) :
      VectorStep P [vconst a, vconst b, vconst c, .plain (.vecTernOp op)]
        [vconst (vvternop op a b c)]
  /-- `Step_pure/vvtestop`. -/
  | vecTestOp (op : VecTestOp) (a : V128) :
      VectorStep P [vconst a, .plain (.vecTestOp op)] [constI32 (vvtestop op a)]
  /-- `Step_pure/vunop-val` (integer shapes). -/
  | vecIntUnOp (sh : IntShape) (op : VecIntUnOp) (a : V128) :
      VectorStep P [vconst a, .plain (.vecIntUnOp sh op)] [vconst (vecIntUnOp sh op a)]
  /-- `Step_pure/vunop-val` (float shapes). -/
  | vecFloatUnOp {sh : FloatShape} {op : FloatUnOp} {a r : V128}
      (h : VecFloatUnOpRel P sh op a r) :
      VectorStep P [vconst a, .plain (.vecFloatUnOp sh op)] [vconst r]
  /-- `Step_pure/vunop-trap` (float shapes). -/
  | vecFloatUnOpTrap {sh : FloatShape} {op : FloatUnOp} {a : V128}
      (h : ∀ r, ¬ VecFloatUnOpRel P sh op a r) :
      VectorStep P [vconst a, .plain (.vecFloatUnOp sh op)] [.trap]
  /-- `Step_pure/vbinop-val` (integer shapes). -/
  | vecIntBinOp (sh : IntShape) (op : VecIntBinOp) (a b : V128) :
      VectorStep P [vconst a, vconst b, .plain (.vecIntBinOp sh op)]
        [vconst (vecIntBinOp P sh op a b)]
  /-- `Step_pure/vbinop-val` (float shapes). -/
  | vecFloatBinOp {sh : FloatShape} {op : VecFloatBinOp} {a b r : V128}
      (h : VecFloatBinOpRel P sh op a b r) :
      VectorStep P [vconst a, vconst b, .plain (.vecFloatBinOp sh op)] [vconst r]
  /-- `Step_pure/vbinop-trap` (float shapes). -/
  | vecFloatBinOpTrap {sh : FloatShape} {op : VecFloatBinOp} {a b : V128}
      (h : ∀ r, ¬ VecFloatBinOpRel P sh op a b r) :
      VectorStep P [vconst a, vconst b, .plain (.vecFloatBinOp sh op)] [.trap]
  /-- `Step_pure/vternop-val` (integer shapes: relaxed lane select). -/
  | vecIntTernOp (sh : IntShape) (op : VecIntTernOp) (a b c : V128) :
      VectorStep P [vconst a, vconst b, vconst c, .plain (.vecIntTernOp sh op)]
        [vconst (vecIntTernOp P sh op a b c)]
  /-- `Step_pure/vternop-val` (float shapes: relaxed madd/nmadd). -/
  | vecFloatTernOp {sh : FloatShape} {op : VecFloatTernOp} {a b c r : V128}
      (h : VecFloatTernOpRel P sh op a b c r) :
      VectorStep P [vconst a, vconst b, vconst c, .plain (.vecFloatTernOp sh op)] [vconst r]
  /-- `Step_pure/vternop-trap` (float shapes). -/
  | vecFloatTernOpTrap {sh : FloatShape} {op : VecFloatTernOp} {a b c : V128}
      (h : ∀ r, ¬ VecFloatTernOpRel P sh op a b c r) :
      VectorStep P [vconst a, vconst b, vconst c, .plain (.vecFloatTernOp sh op)] [.trap]
  /-- `Step_pure/vtestop`. -/
  | vecAllTrue (sh : IntShape) (a : V128) :
      VectorStep P [vconst a, .plain (.vecAllTrue sh)] [constI32 (vecAllTrue sh a)]
  /-- `Step_pure/vrelop` (integer shapes). -/
  | vecIntRelOp (sh : IntShape) (op : IntRelOp) (a b : V128) :
      VectorStep P [vconst a, vconst b, .plain (.vecIntRelOp sh op)]
        [vconst (vecIntRelOp sh op a b)]
  /-- `Step_pure/vrelop` (float shapes). -/
  | vecFloatRelOp (sh : FloatShape) (op : FloatRelOp) (a b : V128) :
      VectorStep P [vconst a, vconst b, .plain (.vecFloatRelOp sh op)]
        [vconst (vecFloatRelOp sh op a b)]
  /-- `Step_pure/vshiftop`. -/
  | vecShiftOp (sh : IntShape) (op : VecShiftOp) (a : V128) (n : BitVec 32) :
      VectorStep P [vconst a, constI32 n, .plain (.vecShiftOp sh op)]
        [vconst (vecShiftOp sh op a n)]
  /-- `Step_pure/vbitmask`. -/
  | vecBitmask (sh : IntShape) (a : V128) :
      VectorStep P [vconst a, .plain (.vecBitmask sh)] [constI32 (vecBitmask sh a)]
  /-- `Step_pure/vswizzlop` (`swizzle`). -/
  | vecSwizzle (a s : V128) :
      VectorStep P [vconst a, vconst s, .plain (.vecSwizzle .swizzle)] [vconst (vecSwizzle a s)]
  /-- `Step_pure/vswizzlop` (`relaxed_swizzle`). -/
  | vecRelaxedSwizzle (a s : V128) :
      VectorStep P [vconst a, vconst s, .plain (.vecSwizzle .relaxedSwizzle)]
        [vconst (vecRelaxedSwizzle P a s)]
  /-- `Step_pure/vshuffle`. The spec indexes `c_1 ++ c_2` (32 lanes) partially,
  so an index `≥ 32` is stuck. -/
  | vecShuffle (idx : List LaneIdx) (a b : V128) (hidx : ∀ j ∈ idx, j.val < 32) :
      VectorStep P [vconst a, vconst b, .plain (.vecShuffle idx)] [vconst (vecShuffle idx a b)]
  /-- `Step_pure/vsplat`. -/
  | vecSplat (sh : Shape) (x : BitVec sh.unpacked.width) :
      VectorStep P [(Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecSplat sh)]
        [vconst (vecSplat sh x)]
  /-- `Step_pure/vextract_lane-num` and `-pack`. `$lanes_(sh, c)[i]` is partial,
  so an out-of-range lane index is stuck. -/
  | vecExtractLane (sh : Shape) (sx : Option Signedness) (i : LaneIdx) (a : V128)
      (hi : i.val < sh.lanes) :
      VectorStep P [vconst a, .plain (.vecExtractLane sh sx i)]
        [(Val.num ⟨sh.unpacked, vecExtractLane sh sx i.val a⟩).toAdmin]
  /-- `Step_pure/vreplace_lane`. The update `$lanes_(sh, c)[[i] = ..]` is partial,
  so an out-of-range lane index is stuck. -/
  | vecReplaceLane (sh : Shape) (i : LaneIdx) (a : V128) (x : BitVec sh.unpacked.width)
      (hi : i.val < sh.lanes) :
      VectorStep P [vconst a, (Val.num ⟨sh.unpacked, x⟩).toAdmin, .plain (.vecReplaceLane sh i)]
        [vconst (vecReplaceLane sh i.val a x)]
  /-- `Step_pure/vextunop`. -/
  | vecExtUnOp {sh₁ sh₂ : IntShape} {op : VecExtUnOp} {a r : V128}
      (h : VecExtUnOpRel sh₁ sh₂ op a r) :
      VectorStep P [vconst a, .plain (.vecExtUnOp sh₁ sh₂ op)] [vconst r]
  /-- `Step_pure/vextbinop`. -/
  | vecExtBinOp {sh₁ sh₂ : IntShape} {op : VecExtBinOp} {a b r : V128}
      (h : VecExtBinOpRel P sh₁ sh₂ op a b r) :
      VectorStep P [vconst a, vconst b, .plain (.vecExtBinOp sh₁ sh₂ op)] [vconst r]
  /-- `Step_pure/vextternop`. -/
  | vecExtTernOp {sh₁ sh₂ : IntShape} {op : VecExtTernOp} {a b c r : V128}
      (h : VecExtTernOpRel P sh₁ sh₂ op a b c r) :
      VectorStep P [vconst a, vconst b, vconst c, .plain (.vecExtTernOp sh₁ sh₂ op)] [vconst r]
  /-- `Step_pure/vnarrow`. -/
  | vecNarrow {sh₁ sh₂ : IntShape} {sx : Signedness} {a b r : V128}
      (h : VecNarrowRel sh₁ sh₂ sx a b r) :
      VectorStep P [vconst a, vconst b, .plain (.vecNarrow sh₁ sh₂ sx)] [vconst r]
  /-- `Step_pure/vcvtop`. -/
  | vecConvert {sh₁ sh₂ : Shape} {op : VecConvertOp} {a r : V128}
      (h : VecConvertRel P sh₁ sh₂ op a r) :
      VectorStep P [vconst a, .plain (.vecConvert sh₁ sh₂ op)] [vconst r]

end Silmaril.Wasm.Execution.Core
