module

public import Silmaril.Wasm.Instructions

/-!
# Core 3.0 instruction keywords

The keyword of every instruction without immediates, as listed in SpecTec
`6.3-text.instructions.spectec` (`Tplaininstr_/num-*`, `/vec-*`, `/parametric`,
`/ref`, `/i31`, `/extern`, …), computed from the abstract syntax.  Operator
families are named compositionally (`i32` `.` `add`); `nullaryName i = none`
exactly for instructions with immediates and for operator/shape combinations
that have no text form (the `;; does not exist!` lines of the SpecTec source
coincide with the shape-validity predicates of `Silmaril.Wasm.Ops`; the one
extra case without a text form is `f32x4.convert_low_i16x8`).
-/

@[expose] public section

namespace Silmaril.Wasm.Text.Core

open Silmaril.Wasm

def itName : IntType → String
  | .i32 => "i32"
  | .i64 => "i64"

def ftName : FloatType → String
  | .f32 => "f32"
  | .f64 => "f64"

def sxName : Signedness → String
  | .signed => "s"
  | .unsigned => "u"

def ishName : IntShape → String
  | .i8x16 => "i8x16"
  | .i16x8 => "i16x8"
  | .i32x4 => "i32x4"
  | .i64x2 => "i64x2"

def fshName : FloatShape → String
  | .f32x4 => "f32x4"
  | .f64x2 => "f64x2"

def shName : Shape → String
  | .int s => ishName s
  | .float s => fshName s

def halfName : Half → String
  | .low => "low"
  | .high => "high"

def intUnName (t : IntType) : IntUnOp → Option String
  | .clz => some "clz"
  | .ctz => some "ctz"
  | .popcnt => some "popcnt"
  | .extend size =>
      if size.width < t.width then some ("extend" ++ toString size.width ++ "_s") else none

def intBinName : IntBinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div s => "div_" ++ sxName s
  | .rem s => "rem_" ++ sxName s
  | .and => "and"
  | .or => "or"
  | .xor => "xor"
  | .shl => "shl"
  | .shr s => "shr_" ++ sxName s
  | .rotl => "rotl"
  | .rotr => "rotr"

def intRelName : IntRelOp → String
  | .eq => "eq"
  | .ne => "ne"
  | .lt s => "lt_" ++ sxName s
  | .gt s => "gt_" ++ sxName s
  | .le s => "le_" ++ sxName s
  | .ge s => "ge_" ++ sxName s

def floatUnName : FloatUnOp → String
  | .abs => "abs"
  | .neg => "neg"
  | .sqrt => "sqrt"
  | .ceil => "ceil"
  | .floor => "floor"
  | .trunc => "trunc"
  | .nearest => "nearest"

def floatBinName : FloatBinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .min => "min"
  | .max => "max"
  | .copysign => "copysign"

def floatRelName : FloatRelOp → String
  | .eq => "eq"
  | .ne => "ne"
  | .lt => "lt"
  | .gt => "gt"
  | .le => "le"
  | .ge => "ge"

/-- Full keywords of the scalar conversions (`Tplaininstr_/num-cvt-*`). -/
def convertName : ConvertOp → String
  | .wrap => "i32.wrap_i64"
  | .extend s => "i64.extend_i32_" ++ sxName s
  | .trunc src dst s => itName dst ++ ".trunc_" ++ ftName src ++ "_" ++ sxName s
  | .truncSat src dst s => itName dst ++ ".trunc_sat_" ++ ftName src ++ "_" ++ sxName s
  | .convert src dst s => ftName dst ++ ".convert_" ++ itName src ++ "_" ++ sxName s
  | .demote => "f32.demote_f64"
  | .promote => "f64.promote_f32"
  | .reinterpretInt .f32 => "i32.reinterpret_f32"
  | .reinterpretInt .f64 => "i64.reinterpret_f64"
  | .reinterpretFloat .i32 => "f32.reinterpret_i32"
  | .reinterpretFloat .i64 => "f64.reinterpret_i64"

def vecIntUnName : VecIntUnOp → String
  | .abs => "abs"
  | .neg => "neg"
  | .popcnt => "popcnt"

def vecIntBinName : VecIntBinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .addSat s => "add_sat_" ++ sxName s
  | .subSat s => "sub_sat_" ++ sxName s
  | .avgrU => "avgr_u"
  | .q15mulrSatS => "q15mulr_sat_s"
  | .relaxedQ15mulrS => "relaxed_q15mulr_s"
  | .min s => "min_" ++ sxName s
  | .max s => "max_" ++ sxName s

def vecFloatBinName : VecFloatBinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .min => "min"
  | .max => "max"
  | .pmin => "pmin"
  | .pmax => "pmax"
  | .relaxedMin => "relaxed_min"
  | .relaxedMax => "relaxed_max"

/-- Keywords of the vector conversions (`Tplaininstr_/vec-cvt-*`). -/
def vecConvertName (src dst : Shape) (op : VecConvertOp) : Option String :=
  if !op.valid src dst then none else
  match op, src, dst with
  | .extend h s, .int si, .int di =>
      some (ishName di ++ ".extend_" ++ halfName h ++ "_" ++ ishName si ++ "_" ++ sxName s)
  | .convert none s, _, _ => some ("f32x4.convert_i32x4_" ++ sxName s)
  | .convert (some .low) s, .int .i32x4, .float .f64x2 =>
      some ("f64x2.convert_low_i32x4_" ++ sxName s)
  | .truncSat s false, _, _ => some ("i32x4.trunc_sat_f32x4_" ++ sxName s)
  | .truncSat s true, _, _ => some ("i32x4.trunc_sat_f64x2_" ++ sxName s ++ "_zero")
  | .relaxedTrunc s false, _, _ => some ("i32x4.relaxed_trunc_f32x4_" ++ sxName s)
  | .relaxedTrunc s true, _, _ => some ("i32x4.relaxed_trunc_f64x2_" ++ sxName s ++ "_zero")
  | .demoteZero, _, _ => some "f32x4.demote_f64x2_zero"
  | .promoteLow, _, _ => some "f64x2.promote_low_f32x4"
  | _, _, _ => none

/-- The keyword of an instruction without immediates. -/
def nullaryName : Instr → Option String
  | .nop => some "nop"
  | .unreachable => some "unreachable"
  | .drop => some "drop"
  | .return_ => some "return"
  | .throwRef => some "throw_ref"
  | .refIsNull => some "ref.is_null"
  | .refAsNonNull => some "ref.as_non_null"
  | .refEq => some "ref.eq"
  | .refI31 => some "ref.i31"
  | .i31Get s => some ("i31.get_" ++ sxName s)
  | .arrayLen => some "array.len"
  | .externConvertAny => some "extern.convert_any"
  | .anyConvertExtern => some "any.convert_extern"
  | .intUnOp t op => (intUnName t op).map (itName t ++ "." ++ ·)
  | .intBinOp t op => some (itName t ++ "." ++ intBinName op)
  | .intTestOp t .eqz => some (itName t ++ ".eqz")
  | .intRelOp t op => some (itName t ++ "." ++ intRelName op)
  | .floatUnOp t op => some (ftName t ++ "." ++ floatUnName op)
  | .floatBinOp t op => some (ftName t ++ "." ++ floatBinName op)
  | .floatRelOp t op => some (ftName t ++ "." ++ floatRelName op)
  | .convert op => some (convertName op)
  | .vecUnOp .not => some "v128.not"
  | .vecBinOp .and => some "v128.and"
  | .vecBinOp .andnot => some "v128.andnot"
  | .vecBinOp .or => some "v128.or"
  | .vecBinOp .xor => some "v128.xor"
  | .vecTernOp .bitselect => some "v128.bitselect"
  | .vecTestOp .anyTrue => some "v128.any_true"
  | .vecIntUnOp sh op => if op.valid sh then some (ishName sh ++ "." ++ vecIntUnName op) else none
  | .vecFloatUnOp sh op => some (fshName sh ++ "." ++ floatUnName op)
  | .vecIntBinOp sh op =>
      if op.valid sh then some (ishName sh ++ "." ++ vecIntBinName op) else none
  | .vecFloatBinOp sh op => some (fshName sh ++ "." ++ vecFloatBinName op)
  | .vecIntTernOp sh .relaxedLaneSelect => some (ishName sh ++ ".relaxed_laneselect")
  | .vecFloatTernOp sh .relaxedMadd => some (fshName sh ++ ".relaxed_madd")
  | .vecFloatTernOp sh .relaxedNmadd => some (fshName sh ++ ".relaxed_nmadd")
  | .vecAllTrue sh => some (ishName sh ++ ".all_true")
  | .vecIntRelOp sh op =>
      if op.validShape sh then some (ishName sh ++ "." ++ intRelName op) else none
  | .vecFloatRelOp sh op => some (fshName sh ++ "." ++ floatRelName op)
  | .vecShiftOp sh .shl => some (ishName sh ++ ".shl")
  | .vecShiftOp sh (.shr s) => some (ishName sh ++ ".shr_" ++ sxName s)
  | .vecBitmask sh => some (ishName sh ++ ".bitmask")
  | .vecSwizzle .swizzle => some "i8x16.swizzle"
  | .vecSwizzle .relaxedSwizzle => some "i8x16.relaxed_swizzle"
  | .vecExtUnOp src dst (.extaddPairwise s) =>
      if VecExtUnOp.valid src dst (.extaddPairwise s) then
        some (ishName dst ++ ".extadd_pairwise_" ++ ishName src ++ "_" ++ sxName s)
      else none
  | .vecExtBinOp src dst op =>
      if !op.valid src dst then none else
      match op with
      | .extmul h s =>
          some (ishName dst ++ ".extmul_" ++ halfName h ++ "_" ++ ishName src ++ "_" ++ sxName s)
      | .dotS => some "i32x4.dot_i16x8_s"
      | .relaxedDotS => some "i16x8.relaxed_dot_i8x16_i7x16_s"
  | .vecExtTernOp src dst .relaxedDotAddS =>
      if VecExtTernOp.valid src dst .relaxedDotAddS then
        some "i32x4.relaxed_dot_i8x16_i7x16_add_s"
      else none
  | .vecNarrow src dst s =>
      if src.laneWidth == 2 * dst.laneWidth && src.laneWidth ≤ 32 then
        some (ishName dst ++ ".narrow_" ++ ishName src ++ "_" ++ sxName s)
      else none
  | .vecConvert src dst op => vecConvertName src dst op
  | .vecSplat sh => some (shName sh ++ ".splat")
  | _ => none

/-! ## Injectivity of `nullaryName`

`nullaryName` is inverted by `NullaryDecode.decode`, which looks the keyword up
among a short list of candidates selected by the dot-free prefix (`i32`,
`i8x16`, `v128`, `ref`, …) of the keyword.  `decode (nullaryName i) = some i` is
then checked by evaluation for each of the finitely many instructions without
immediates; injectivity follows without any pairwise comparison of
instructions.  `toString` on `Nat` does not reduce by evaluation, so the
evaluated name function `nullaryName'` spells the sign-extension widths out. -/

namespace NullaryDecode

/-- The decimal spelling of a packed width. -/
def packWidthName : PackSize → String
  | .i8 => "8"
  | .i16 => "16"
  | .i32 => "32"
  | .i64 => "64"

theorem repr_width (p : PackSize) : p.width.repr = packWidthName p := by
  rw [← String.toList_inj]
  cases p <;> simp [PackSize.width, packWidthName, Nat.toDigits_eq_ite]

/-- `nullaryName` with `toString` evaluated away. -/
def nullaryName' : Instr → Option String
  | .intUnOp t (.extend size) =>
      if size.width < t.width then
        some (itName t ++ "." ++ ("extend" ++ packWidthName size ++ "_s"))
      else none
  | i => nullaryName i

theorem nullaryName'_eq (i : Instr) : nullaryName' i = nullaryName i := by
  cases i <;> try rfl
  case intUnOp t op =>
    cases op <;> try rfl
    case extend size =>
      by_cases h : size.width < t.width <;>
        simp [nullaryName', nullaryName, intUnName, repr_width, h]

def sxs : List Signedness := [.signed, .unsigned]
def intUnOps : List IntUnOp := [.clz, .ctz, .popcnt, .extend .i8, .extend .i16, .extend .i32]
def intBinOps : List IntBinOp :=
  [.add, .sub, .mul, .and, .or, .xor, .shl, .rotl, .rotr] ++
    sxs.flatMap fun s => [.div s, .rem s, .shr s]
def intRelOps : List IntRelOp := [.eq, .ne] ++ sxs.flatMap fun s => [.lt s, .gt s, .le s, .ge s]
def floatUnOps : List FloatUnOp := [.abs, .neg, .sqrt, .ceil, .floor, .trunc, .nearest]
def floatBinOps : List FloatBinOp := [.add, .sub, .mul, .div, .min, .max, .copysign]
def floatRelOps : List FloatRelOp := [.eq, .ne, .lt, .gt, .le, .ge]
def intTypes : List IntType := [.i32, .i64]
def floatTypes : List FloatType := [.f32, .f64]
def convertOps : List ConvertOp :=
  [.wrap, .demote, .promote, .reinterpretInt .f32, .reinterpretInt .f64,
    .reinterpretFloat .i32, .reinterpretFloat .i64] ++
  sxs.flatMap fun s => [ConvertOp.extend s] ++
    floatTypes.flatMap fun f => intTypes.flatMap fun t =>
      [ConvertOp.trunc f t s, .truncSat f t s, .convert t f s]
def intShapes : List IntShape := [.i8x16, .i16x8, .i32x4, .i64x2]
def floatShapes : List FloatShape := [.f32x4, .f64x2]
def vecIntBinOps : List VecIntBinOp :=
  [.add, .sub, .mul, .avgrU, .q15mulrSatS, .relaxedQ15mulrS] ++
    sxs.flatMap fun s => [.addSat s, .subSat s, .min s, .max s]
def vecFloatBinOps : List VecFloatBinOp :=
  [.add, .sub, .mul, .div, .min, .max, .pmin, .pmax, .relaxedMin, .relaxedMax]

def scalarInt (t : IntType) : List Instr :=
  intUnOps.map (.intUnOp t) ++ intBinOps.map (.intBinOp t) ++ [.intTestOp t .eqz] ++
    intRelOps.map (.intRelOp t) ++ convertOps.map .convert

def scalarFloat (t : FloatType) : List Instr :=
  floatUnOps.map (.floatUnOp t) ++ floatBinOps.map (.floatBinOp t) ++
    floatRelOps.map (.floatRelOp t) ++ convertOps.map .convert

def vecInt (sh : IntShape) : List Instr :=
  [.vecIntUnOp sh .abs, .vecIntUnOp sh .neg, .vecIntUnOp sh .popcnt,
    .vecIntTernOp sh .relaxedLaneSelect, .vecAllTrue sh, .vecShiftOp sh .shl,
    .vecShiftOp sh (.shr .signed), .vecShiftOp sh (.shr .unsigned), .vecBitmask sh,
    .vecSplat (.int sh), .vecSwizzle .swizzle, .vecSwizzle .relaxedSwizzle] ++
  vecIntBinOps.map (.vecIntBinOp sh) ++ intRelOps.map (.vecIntRelOp sh) ++
  intShapes.flatMap (fun src =>
    [.vecExtTernOp src sh .relaxedDotAddS, .vecExtBinOp src sh .dotS,
      .vecExtBinOp src sh .relaxedDotS] ++
    sxs.flatMap fun s =>
      [.vecExtUnOp src sh (.extaddPairwise s), .vecNarrow src sh s,
        .vecExtBinOp src sh (.extmul .low s), .vecExtBinOp src sh (.extmul .high s),
        .vecConvert (.int src) (.int sh) (.extend .low s),
        .vecConvert (.int src) (.int sh) (.extend .high s)]) ++
  floatShapes.flatMap fun src => sxs.flatMap fun s =>
    [false, true].flatMap fun z =>
      [.vecConvert (.float src) (.int sh) (.truncSat s z),
        .vecConvert (.float src) (.int sh) (.relaxedTrunc s z)]

def vecFloat (sh : FloatShape) : List Instr :=
  [.vecFloatTernOp sh .relaxedMadd, .vecFloatTernOp sh .relaxedNmadd, .vecSplat (.float sh),
    .vecConvert (.float .f64x2) (.float sh) .demoteZero,
    .vecConvert (.float .f32x4) (.float sh) .promoteLow] ++
  floatUnOps.map (.vecFloatUnOp sh) ++ vecFloatBinOps.map (.vecFloatBinOp sh) ++
  floatRelOps.map (.vecFloatRelOp sh) ++
  intShapes.flatMap fun src => sxs.flatMap fun s =>
    [none, some .low, some .high].map fun h => .vecConvert (.int src) (.float sh) (.convert h s)

/-- Candidate instructions for a dot-free keyword prefix. -/
def candidates : String → List Instr
  | "i32" => scalarInt .i32
  | "i64" => scalarInt .i64
  | "f32" => scalarFloat .f32
  | "f64" => scalarFloat .f64
  | "i8x16" => vecInt .i8x16
  | "i16x8" => vecInt .i16x8
  | "i32x4" => vecInt .i32x4
  | "i64x2" => vecInt .i64x2
  | "f32x4" => vecFloat .f32x4
  | "f64x2" => vecFloat .f64x2
  | "v128" => [.vecUnOp .not, .vecBinOp .and, .vecBinOp .andnot, .vecBinOp .or,
      .vecBinOp .xor, .vecTernOp .bitselect, .vecTestOp .anyTrue]
  | "ref" => [.refIsNull, .refAsNonNull, .refEq, .refI31]
  | "i31" => [.i31Get .signed, .i31Get .unsigned]
  | "array" => [.arrayLen]
  | "extern" => [.externConvertAny]
  | "any" => [.anyConvertExtern]
  | _ => [.nop, .unreachable, .drop, .return_, .throwRef]

/-- A left inverse of `nullaryName` (`decode_of_nullaryName`). -/
def decode (s : String) : Option Instr :=
  (candidates (String.ofList (s.toList.takeWhile (· ≠ '.')))).find? (nullaryName' · == some s)

/-- Split every hypothesis of a finite operator type. -/
local macro "split_ops" : tactic => `(tactic|
  cases_type* IntType FloatType Signedness PackSize IntUnOp IntBinOp
    IntTestOp IntRelOp FloatUnOp FloatBinOp FloatRelOp ConvertOp IntShape
    FloatShape Shape Half VecUnOp VecBinOp VecTernOp VecTestOp VecIntUnOp
    VecIntBinOp VecFloatBinOp VecIntTernOp VecFloatTernOp VecShiftOp VecSwizzleOp
    VecExtUnOp VecExtBinOp VecExtTernOp VecConvertOp Bool Option)

set_option maxHeartbeats 4000000 in
/-- Checked by evaluation, one instruction at a time. -/
theorem bind_decode (i : Instr) :
    (nullaryName' i).bind decode = (nullaryName' i).map (fun _ => i) := by
  cases i <;> (try split_ops) <;> rfl

theorem decode_of_nullaryName {i : Instr} {s : String} (h : nullaryName i = some s) :
    decode s = some i := by
  have := bind_decode i
  rwa [nullaryName'_eq, h] at this

end NullaryDecode

/-- Distinct nullary instructions have distinct keywords. -/
theorem nullaryName_injective {i j : Instr} {s : String} (hi : nullaryName i = some s)
    (hj : nullaryName j = some s) : i = j := by
  exact Option.some.inj <|
    (NullaryDecode.decode_of_nullaryName hi).symm.trans (NullaryDecode.decode_of_nullaryName hj)

/-! Spot checks against `6.3-text.instructions.spectec`.  The full keyword set
of `nullaryName` was compared against the 368 nullary `Tplaininstr_`
productions of that file (equal as sets). -/

example : nullaryName (.vecIntBinOp .i16x8 .relaxedQ15mulrS) = some "i16x8.relaxed_q15mulr_s" := by
  decide
example : nullaryName (.vecExtBinOp .i8x16 .i16x8 .relaxedDotS) =
    some "i16x8.relaxed_dot_i8x16_i7x16_s" := by decide
example : nullaryName (.vecExtTernOp .i8x16 .i32x4 .relaxedDotAddS) =
    some "i32x4.relaxed_dot_i8x16_i7x16_add_s" := by decide
example : nullaryName (.vecConvert (.float .f64x2) (.int .i32x4) (.relaxedTrunc .unsigned true)) =
    some "i32x4.relaxed_trunc_f64x2_u_zero" := by decide
example : nullaryName (.vecFloatTernOp .f64x2 .relaxedNmadd) = some "f64x2.relaxed_nmadd" := by
  decide
example : nullaryName (.vecSwizzle .relaxedSwizzle) = some "i8x16.relaxed_swizzle" := by decide
example : nullaryName (.vecExtUnOp .i16x8 .i32x4 (.extaddPairwise .unsigned)) =
    some "i32x4.extadd_pairwise_i16x8_u" := by decide
example : nullaryName (.vecConvert (.int .i32x4) (.float .f64x2) (.convert (some .low) .signed)) =
    some "f64x2.convert_low_i32x4_s" := by decide
example : nullaryName (.vecConvert (.float .f32x4) (.float .f64x2) .promoteLow) =
    some "f64x2.promote_low_f32x4" := by decide
example : nullaryName (.vecIntRelOp .i64x2 (.lt .unsigned)) = none := by decide
example : nullaryName (.vecIntUnOp .i16x8 .popcnt) = none := by decide

end Silmaril.Wasm.Text.Core
