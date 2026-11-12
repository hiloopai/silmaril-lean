module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Execution
public import Silmaril.Raw.Wasm.SpecTec.Encode

/-!
# SpecTec ↔ Core 3.0: the IL encoding of SIMD instructions (family V)

The base encoding (`Sim.instrToV`) sent SIMD instructions through `schemaInstrV`, the schema of
`Silmaril.Wasm.SpecTec.encodeInstruction` read as an IL value. That reading is wrong wherever an
operator case carries a single non-tuple payload: `ADD_SAT sx`, `SUB_SAT sx`, `MIN sx`, `MAX sx`
(integer `vbinop_`), `SHR sx` (`vshiftop_`), `EXTADD_PAIRWISE sx` (`vextunop__`) and `DEMOTE zero`
(`vcvtop__`) carry the payload bare in the IL (their `TypCase` type is `varT`, not `tupT`), while
the schema reading wraps it in a one-element tuple. Conversely the integer `vrelop_` cases
`LT sx`, `GT sx`, `LE sx`, `GE sx` are declared with a one-binder `tupT` and do carry a tuple.

`vecInstrV` writes the twenty-four non-memory SIMD instructions directly against the IL type
`instr` of the fixed wasm-3.0 script (`Scripts/Wasm30/Original/Part1.lean`, definitions 222–246
and the `instr` variant), case by case. The memory SIMD instructions (`vecLoad`, `vecLoadLane`,
`vecStore`, `vecStoreLane`) stay on `schemaInstrV`; they belong to family M.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)

/-- `sx`: `U` or `S`. -/
def sxV : Signedness → Value
  | .unsigned => caseNilV "U"
  | .signed => caseNilV "S"

/-- `half`: `LOW` or `HIGH`. -/
def halfV : Half → Value
  | .low => caseNilV "LOW"
  | .high => caseNilV "HIGH"

/-- The lane type of an integer shape (`Jnn`). -/
def intLaneV : IntShape → Value
  | .i8x16 => caseNilV "I8"
  | .i16x8 => caseNilV "I16"
  | .i32x4 => caseNilV "I32"
  | .i64x2 => caseNilV "I64"

/-- The lane type of a float shape (`Fnn`). -/
def floatLaneV : FloatShape → Value
  | .f32x4 => caseNilV "F32"
  | .f64x2 => caseNilV "F64"

/-- An integer shape `Jnn X M`, as the IL type `shape` (`%X%` of a lane type and a `dim`). -/
def ishV (s : IntShape) : Value := .case "%X%" (.tuple [intLaneV s, pctV s.lanes])

/-- A float shape `Fnn X M`. -/
def fshV (s : FloatShape) : Value := .case "%X%" (.tuple [floatLaneV s, pctV s.lanes])

/-- A shape. -/
def shapeV : Shape → Value
  | .int s => ishV s
  | .float s => fshV s

/-- The lane type of a shape (`Lnn`). -/
def laneTypeV : Shape → Value
  | .int s => intLaneV s
  | .float s => floatLaneV s

/-- `ishape`: the one-field `%` wrapper around an integer shape. -/
def ishapeV (s : IntShape) : Value := .case "%" (.tuple [ishV s])

/-- `bshape`: the one-field `%` wrapper around `I8 X 16`. -/
def bshapeV : Value := .case "%" (.tuple [ishV .i8x16])

/-- `vvunop`. -/
def vvunopV : VecUnOp → Value
  | .not => caseNilV "NOT"

/-- `vvbinop`. -/
def vvbinopV : VecBinOp → Value
  | .and => caseNilV "AND"
  | .andnot => caseNilV "ANDNOT"
  | .or => caseNilV "OR"
  | .xor => caseNilV "XOR"

/-- `vvternop`. -/
def vvternopV : VecTernOp → Value
  | .bitselect => caseNilV "BITSELECT"

/-- `vvtestop`. -/
def vvtestopV : VecTestOp → Value
  | .anyTrue => caseNilV "ANY_TRUE"

/-- `vunop_(Jnn X M)`. -/
def vIntUnOpV : VecIntUnOp → Value
  | .abs => caseNilV "ABS"
  | .neg => caseNilV "NEG"
  | .popcnt => caseNilV "POPCNT"

/-- `vunop_(Fnn X M)`. -/
def vFloatUnOpV : FloatUnOp → Value
  | .abs => caseNilV "ABS"
  | .neg => caseNilV "NEG"
  | .sqrt => caseNilV "SQRT"
  | .ceil => caseNilV "CEIL"
  | .floor => caseNilV "FLOOR"
  | .trunc => caseNilV "TRUNC"
  | .nearest => caseNilV "NEAREST"

/-- `vbinop_(Jnn X M)`. `ADD_SAT`, `SUB_SAT`, `MIN` and `MAX` carry their `sx` bare (`varT`). -/
def vIntBinOpV : VecIntBinOp → Value
  | .add => caseNilV "ADD"
  | .sub => caseNilV "SUB"
  | .mul => caseNilV "MUL"
  | .addSat s => .case "ADD_SAT" (sxV s)
  | .subSat s => .case "SUB_SAT" (sxV s)
  | .avgrU => caseNilV "AVGRU"
  | .q15mulrSatS => caseNilV "Q15MULR_SATS"
  | .relaxedQ15mulrS => caseNilV "RELAXED_Q15MULRS"
  | .min s => .case "MIN" (sxV s)
  | .max s => .case "MAX" (sxV s)

/-- `vbinop_(Fnn X M)`. -/
def vFloatBinOpV : VecFloatBinOp → Value
  | .add => caseNilV "ADD"
  | .sub => caseNilV "SUB"
  | .mul => caseNilV "MUL"
  | .div => caseNilV "DIV"
  | .min => caseNilV "MIN"
  | .max => caseNilV "MAX"
  | .pmin => caseNilV "PMIN"
  | .pmax => caseNilV "PMAX"
  | .relaxedMin => caseNilV "RELAXED_MIN"
  | .relaxedMax => caseNilV "RELAXED_MAX"

/-- `vternop_(Jnn X M)`. -/
def vIntTernOpV : VecIntTernOp → Value
  | .relaxedLaneSelect => caseNilV "RELAXED_LANESELECT"

/-- `vternop_(Fnn X M)`. -/
def vFloatTernOpV : VecFloatTernOp → Value
  | .relaxedMadd => caseNilV "RELAXED_MADD"
  | .relaxedNmadd => caseNilV "RELAXED_NMADD"

/-- `vrelop_(Jnn X M)`: the signed comparisons are declared with a one-binder tuple. -/
def vIntRelOpV : IntRelOp → Value
  | .eq => caseNilV "EQ"
  | .ne => caseNilV "NE"
  | .lt s => .case "LT" (.tuple [sxV s])
  | .gt s => .case "GT" (.tuple [sxV s])
  | .le s => .case "LE" (.tuple [sxV s])
  | .ge s => .case "GE" (.tuple [sxV s])

/-- `vrelop_(Fnn X M)`. -/
def vFloatRelOpV : FloatRelOp → Value
  | .eq => caseNilV "EQ"
  | .ne => caseNilV "NE"
  | .lt => caseNilV "LT"
  | .gt => caseNilV "GT"
  | .le => caseNilV "LE"
  | .ge => caseNilV "GE"

/-- `vshiftop_(ishape)`: `SHR` carries its `sx` bare. -/
def vShiftOpV : VecShiftOp → Value
  | .shl => caseNilV "SHL"
  | .shr s => .case "SHR" (sxV s)

/-- `vswizzlop_(bshape)`. -/
def vSwizzleOpV : VecSwizzleOp → Value
  | .swizzle => caseNilV "SWIZZLE"
  | .relaxedSwizzle => caseNilV "RELAXED_SWIZZLE"

/-- `vextunop__`: `EXTADD_PAIRWISE` carries its `sx` bare. -/
def vExtUnOpV : VecExtUnOp → Value
  | .extaddPairwise s => .case "EXTADD_PAIRWISE" (sxV s)

/-- `vextbinop__`. -/
def vExtBinOpV : VecExtBinOp → Value
  | .extmul h s => .case "EXTMUL" (.tuple [halfV h, sxV s])
  | .dotS => caseNilV "DOTS"
  | .relaxedDotS => caseNilV "RELAXED_DOTS"

/-- `vextternop__`. -/
def vExtTernOpV : VecExtTernOp → Value
  | .relaxedDotAddS => caseNilV "RELAXED_DOT_ADDS"

/-- `vcvtop__`: `DEMOTE` carries its `zero` bare. -/
def vConvertOpV : VecConvertOp → Value
  | .extend h s => .case "EXTEND" (.tuple [halfV h, sxV s])
  | .convert h s => .case "CONVERT" (.tuple [.opt (h.map halfV), sxV s])
  | .truncSat s z =>
      .case "TRUNC_SAT" (.tuple [sxV s, .opt (if z then some (caseNilV "ZERO") else none)])
  | .relaxedTrunc s z =>
      .case "RELAXED_TRUNC" (.tuple [sxV s, .opt (if z then some (caseNilV "ZERO") else none)])
  | .demoteZero => .case "DEMOTE" (caseNilV "ZERO")
  | .promoteLow => caseNilV "PROMOTELOW"

/-- `V128`. -/
abbrev vecTypeV : Value := caseNilV "V128"

/-- A `laneidx` (`u8`). -/
def laneIdxV (i : LaneIdx) : Value := pctV i.val

/-- The twenty-four non-memory SIMD instructions other than `v128.const`, as IL `instr` values;
`none` for every other instruction. -/
def vecInstrV? : Instr → Option Value
  | .vecUnOp op => some (.case "VVUNOP" (.tuple [vecTypeV, vvunopV op]))
  | .vecBinOp op => some (.case "VVBINOP" (.tuple [vecTypeV, vvbinopV op]))
  | .vecTernOp op => some (.case "VVTERNOP" (.tuple [vecTypeV, vvternopV op]))
  | .vecTestOp op => some (.case "VVTESTOP" (.tuple [vecTypeV, vvtestopV op]))
  | .vecIntUnOp s op => some (.case "VUNOP" (.tuple [ishV s, vIntUnOpV op]))
  | .vecFloatUnOp s op => some (.case "VUNOP" (.tuple [fshV s, vFloatUnOpV op]))
  | .vecIntBinOp s op => some (.case "VBINOP" (.tuple [ishV s, vIntBinOpV op]))
  | .vecFloatBinOp s op => some (.case "VBINOP" (.tuple [fshV s, vFloatBinOpV op]))
  | .vecIntTernOp s op => some (.case "VTERNOP" (.tuple [ishV s, vIntTernOpV op]))
  | .vecFloatTernOp s op => some (.case "VTERNOP" (.tuple [fshV s, vFloatTernOpV op]))
  | .vecAllTrue s => some (.case "VTESTOP" (.tuple [ishV s, caseNilV "ALL_TRUE"]))
  | .vecIntRelOp s op => some (.case "VRELOP" (.tuple [ishV s, vIntRelOpV op]))
  | .vecFloatRelOp s op => some (.case "VRELOP" (.tuple [fshV s, vFloatRelOpV op]))
  | .vecShiftOp s op => some (.case "VSHIFTOP" (.tuple [ishapeV s, vShiftOpV op]))
  | .vecBitmask s => some (.case "VBITMASK" (ishapeV s))
  | .vecSwizzle op => some (.case "VSWIZZLOP" (.tuple [bshapeV, vSwizzleOpV op]))
  | .vecShuffle ls => some (.case "VSHUFFLE" (.tuple [bshapeV, .list (ls.map laneIdxV)]))
  | .vecExtUnOp s t op =>
      some (.case "VEXTUNOP" (.tuple [ishapeV t, ishapeV s, vExtUnOpV op]))
  | .vecExtBinOp s t op =>
      some (.case "VEXTBINOP" (.tuple [ishapeV t, ishapeV s, vExtBinOpV op]))
  | .vecExtTernOp s t op =>
      some (.case "VEXTTERNOP" (.tuple [ishapeV t, ishapeV s, vExtTernOpV op]))
  | .vecNarrow s t sx => some (.case "VNARROW" (.tuple [ishapeV t, ishapeV s, sxV sx]))
  | .vecConvert s t op => some (.case "VCVTOP" (.tuple [shapeV t, shapeV s, vConvertOpV op]))
  | .vecSplat s => some (.case "VSPLAT" (shapeV s))
  | .vecExtractLane s sx i =>
      some (.case "VEXTRACT_LANE" (.tuple [shapeV s, .opt (sx.map sxV), laneIdxV i]))
  | .vecReplaceLane s i => some (.case "VREPLACE_LANE" (.tuple [shapeV s, laneIdxV i]))
  | _ => none

/-! ## Scalar conversions

`Equiv.instrV` enumerates the scalar conversions one by one and has no clause for `TRUNC_SAT`
(`i32.trunc_sat_f32_s` and the other seven saturating truncations fall to its junk default
`.tuple []`). `convertInstrV` encodes every `ConvertOp` uniformly, agreeing with `Equiv.instrV` on
the ones it covers (`convertInstrV_eq_instrV` checks this case by case). -/

/-- A number type as an IL `numtype`. -/
def numTypeV : NumType → Value
  | .int .i32 => caseNilV "I32"
  | .int .i64 => caseNilV "I64"
  | .float .f32 => caseNilV "F32"
  | .float .f64 => caseNilV "F64"

/-- `cvtop__(nt_1, nt_2)`: every operator with a signedness carries it bare (`varT sx`). -/
def cvtOpV : ConvertOp → Value
  | .wrap => caseNilV "WRAP"
  | .extend s => .case "EXTEND" (sxV s)
  | .trunc _ _ s => .case "TRUNC" (sxV s)
  | .truncSat _ _ s => .case "TRUNC_SAT" (sxV s)
  | .convert _ _ s => .case "CONVERT" (sxV s)
  | .demote => caseNilV "DEMOTE"
  | .promote => caseNilV "PROMOTE"
  | .reinterpretInt _ => caseNilV "REINTERPRET"
  | .reinterpretFloat _ => caseNilV "REINTERPRET"

/-- `CVTOP nt_2 nt_1 cvtop`: target type first. -/
def convertInstrV (op : ConvertOp) : Value :=
  .case "CVTOP" (.tuple [numTypeV op.target, numTypeV op.source, cvtOpV op])

end Silmaril.Wasm.SpecTec.Sim.Vec
