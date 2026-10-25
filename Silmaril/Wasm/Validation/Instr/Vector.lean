module

public import Silmaril.Wasm.Validation.TypeOk

@[expose] public section

/-! # Typing family: vector instructions, including relaxed SIMD (§2.3 "Vector instructions")

Spec rules (all 22 present): `Instr_ok/vconst`, `vvunop`, `vvbinop`, `vvternop`,
`vvtestop`, `vunop`, `vbinop`, `vternop`, `vtestop`, `vrelop`, `vshiftop`,
`vbitmask`, `vswizzlop`, `vshuffle`, `vsplat`, `vextract_lane`, `vreplace_lane`,
`vextunop`, `vextbinop`, `vextternop`, `vnarrow`, `vcvtop`.

Relaxed SIMD has no rules of its own: its operators are constructors of the
operator enums (`relaxedQ15mulrS`, `relaxedMin`, …). The grammar-level shape
constraints of SpecTec's operator families (for example `POPCNT` only at
`I8X16`) are the `valid` predicates of `Ops.lean`, taken as premises.
-/

namespace Silmaril.Wasm.Validation

inductive VectorInstrOk (C : Context) : Instr → InstrType → Prop where
  /-- `Instr_ok/vconst`. -/
  | vecConst (b : BitVec 128) : VectorInstrOk C (.vecConst b) (.plain [] [.v128])
  /-- `Instr_ok/vvunop`. -/
  | vecUnOp (op : VecUnOp) : VectorInstrOk C (.vecUnOp op) (.plain [.v128] [.v128])
  /-- `Instr_ok/vvbinop`. -/
  | vecBinOp (op : VecBinOp) : VectorInstrOk C (.vecBinOp op) (.plain [.v128, .v128] [.v128])
  /-- `Instr_ok/vvternop`. -/
  | vecTernOp (op : VecTernOp) :
      VectorInstrOk C (.vecTernOp op) (.plain [.v128, .v128, .v128] [.v128])
  /-- `Instr_ok/vvtestop`. -/
  | vecTestOp (op : VecTestOp) : VectorInstrOk C (.vecTestOp op) (.plain [.v128] [.i32])
  /-- `Instr_ok/vunop` (integer shapes). -/
  | vecIntUnOp {sh : IntShape} {op : VecIntUnOp} (h : op.valid sh = true) :
      VectorInstrOk C (.vecIntUnOp sh op) (.plain [.v128] [.v128])
  /-- `Instr_ok/vunop` (float shapes). -/
  | vecFloatUnOp (sh : FloatShape) (op : FloatUnOp) :
      VectorInstrOk C (.vecFloatUnOp sh op) (.plain [.v128] [.v128])
  /-- `Instr_ok/vbinop` (integer shapes). -/
  | vecIntBinOp {sh : IntShape} {op : VecIntBinOp} (h : op.valid sh = true) :
      VectorInstrOk C (.vecIntBinOp sh op) (.plain [.v128, .v128] [.v128])
  /-- `Instr_ok/vbinop` (float shapes). -/
  | vecFloatBinOp (sh : FloatShape) (op : VecFloatBinOp) :
      VectorInstrOk C (.vecFloatBinOp sh op) (.plain [.v128, .v128] [.v128])
  /-- `Instr_ok/vternop` (integer shapes: relaxed lane select). -/
  | vecIntTernOp (sh : IntShape) (op : VecIntTernOp) :
      VectorInstrOk C (.vecIntTernOp sh op) (.plain [.v128, .v128, .v128] [.v128])
  /-- `Instr_ok/vternop` (float shapes: relaxed madd/nmadd). -/
  | vecFloatTernOp (sh : FloatShape) (op : VecFloatTernOp) :
      VectorInstrOk C (.vecFloatTernOp sh op) (.plain [.v128, .v128, .v128] [.v128])
  /-- `Instr_ok/vtestop`. -/
  | vecAllTrue (sh : IntShape) : VectorInstrOk C (.vecAllTrue sh) (.plain [.v128] [.i32])
  /-- `Instr_ok/vrelop` (integer shapes). -/
  | vecIntRelOp {sh : IntShape} {op : IntRelOp} (h : op.validShape sh = true) :
      VectorInstrOk C (.vecIntRelOp sh op) (.plain [.v128, .v128] [.v128])
  /-- `Instr_ok/vrelop` (float shapes). -/
  | vecFloatRelOp (sh : FloatShape) (op : FloatRelOp) :
      VectorInstrOk C (.vecFloatRelOp sh op) (.plain [.v128, .v128] [.v128])
  /-- `Instr_ok/vshiftop`. -/
  | vecShiftOp (sh : IntShape) (op : VecShiftOp) :
      VectorInstrOk C (.vecShiftOp sh op) (.plain [.v128, .i32] [.v128])
  /-- `Instr_ok/vbitmask`. -/
  | vecBitmask (sh : IntShape) : VectorInstrOk C (.vecBitmask sh) (.plain [.v128] [.i32])
  /-- `Instr_ok/vswizzlop`. -/
  | vecSwizzle (op : VecSwizzleOp) :
      VectorInstrOk C (.vecSwizzle op) (.plain [.v128, .v128] [.v128])
  /-- `Instr_ok/vshuffle`: sixteen lane indices, each `< 2 * 16`. -/
  | vecShuffle {lanes : List LaneIdx} (hlen : lanes.length = 16)
      (h : ∀ i ∈ lanes, i.val < 32) :
      VectorInstrOk C (.vecShuffle lanes) (.plain [.v128, .v128] [.v128])
  /-- `Instr_ok/vsplat`. -/
  | vecSplat (sh : Shape) : VectorInstrOk C (.vecSplat sh) (.plain [.num sh.unpacked] [.v128])
  /-- `Instr_ok/vextract_lane`; the sign is present exactly for packed lanes. -/
  | vecExtractLane {sh : Shape} {sx : Option Signedness} {i : LaneIdx}
      (hi : i.val < sh.lanes) (hsx : sx.isSome = decide (sh.laneWidth < 32)) :
      VectorInstrOk C (.vecExtractLane sh sx i) (.plain [.v128] [.num sh.unpacked])
  /-- `Instr_ok/vreplace_lane`. -/
  | vecReplaceLane {sh : Shape} {i : LaneIdx} (hi : i.val < sh.lanes) :
      VectorInstrOk C (.vecReplaceLane sh i) (.plain [.v128, .num sh.unpacked] [.v128])
  /-- `Instr_ok/vextunop`. -/
  | vecExtUnOp {sh₁ sh₂ : IntShape} {op : VecExtUnOp} (h : op.valid sh₁ sh₂ = true) :
      VectorInstrOk C (.vecExtUnOp sh₁ sh₂ op) (.plain [.v128] [.v128])
  /-- `Instr_ok/vextbinop`. -/
  | vecExtBinOp {sh₁ sh₂ : IntShape} {op : VecExtBinOp} (h : op.valid sh₁ sh₂ = true) :
      VectorInstrOk C (.vecExtBinOp sh₁ sh₂ op) (.plain [.v128, .v128] [.v128])
  /-- `Instr_ok/vextternop`. -/
  | vecExtTernOp {sh₁ sh₂ : IntShape} {op : VecExtTernOp} (h : op.valid sh₁ sh₂ = true) :
      VectorInstrOk C (.vecExtTernOp sh₁ sh₂ op) (.plain [.v128, .v128, .v128] [.v128])
  /-- `Instr_ok/vnarrow`. -/
  | vecNarrow {sh₁ sh₂ : IntShape} {sx : Signedness}
      (h : sh₁.laneWidth = 2 * sh₂.laneWidth ∧ sh₁.laneWidth ≤ 32) :
      VectorInstrOk C (.vecNarrow sh₁ sh₂ sx) (.plain [.v128, .v128] [.v128])
  /-- `Instr_ok/vcvtop`. -/
  | vecConvert {sh₁ sh₂ : Shape} {op : VecConvertOp} (h : op.valid sh₁ sh₂ = true) :
      VectorInstrOk C (.vecConvert sh₁ sh₂ op) (.plain [.v128] [.v128])

end Silmaril.Wasm.Validation
