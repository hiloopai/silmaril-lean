module

public import Silmaril.Wasm.Types

@[expose] public section

/-! # WebAssembly Core 3.0 operator families

These are source operators, not host operations. Shape restrictions are explicit
predicates so raw syntax and validation stay separate. The authoritative grammar
is [SpecTec's instruction syntax](https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0/1.3-syntax.instructions.spectec).
-/

namespace Silmaril.Wasm

inductive Signedness where
  | signed | unsigned
  deriving DecidableEq, Repr

inductive PackSize where
  | i8 | i16 | i32 | i64
  deriving DecidableEq, Repr

def PackSize.width : PackSize → Nat
  | .i8 => 8 | .i16 => 16 | .i32 => 32 | .i64 => 64

inductive IntUnOp where
  | clz | ctz | popcnt
  | extend (size : PackSize)
  deriving DecidableEq, Repr

def IntUnOp.valid (t : IntType) : IntUnOp → Bool
  | .extend size => size.width < t.width
  | _ => true

inductive IntBinOp where
  | add | sub | mul
  | div (sign : Signedness)
  | rem (sign : Signedness)
  | and | or | xor | shl
  | shr (sign : Signedness)
  | rotl | rotr
  deriving DecidableEq, Repr

inductive IntTestOp where
  | eqz
  deriving DecidableEq, Repr

inductive IntRelOp where
  | eq | ne
  | lt (sign : Signedness)
  | gt (sign : Signedness)
  | le (sign : Signedness)
  | ge (sign : Signedness)
  deriving DecidableEq, Repr

inductive FloatUnOp where
  | abs | neg | sqrt | ceil | floor | trunc | nearest
  deriving DecidableEq, Repr

inductive FloatBinOp where
  | add | sub | mul | div | min | max | copysign
  deriving DecidableEq, Repr

inductive FloatRelOp where
  | eq | ne | lt | gt | le | ge
  deriving DecidableEq, Repr

/-- Scalar conversions fix their source and target, including reinterpretation widths. -/
inductive ConvertOp where
  | wrap
  | extend (sign : Signedness)
  | trunc (source : FloatType) (target : IntType) (sign : Signedness)
  | truncSat (source : FloatType) (target : IntType) (sign : Signedness)
  | convert (source : IntType) (target : FloatType) (sign : Signedness)
  | demote | promote
  | reinterpretInt (source : FloatType)
  | reinterpretFloat (source : IntType)
  deriving DecidableEq, Repr

def ConvertOp.source : ConvertOp → NumType
  | .wrap => .int .i64
  | .extend _ => .int .i32
  | .trunc t _ _ | .truncSat t _ _ | .reinterpretInt t => .float t
  | .convert t _ _ | .reinterpretFloat t => .int t
  | .demote => .float .f64
  | .promote => .float .f32

def ConvertOp.target : ConvertOp → NumType
  | .wrap => .int .i32
  | .extend _ => .int .i64
  | .trunc _ t _ | .truncSat _ t _ => .int t
  | .convert _ t _ => .float t
  | .demote => .float .f32
  | .promote => .float .f64
  | .reinterpretInt .f32 => .int .i32
  | .reinterpretInt .f64 => .int .i64
  | .reinterpretFloat .i32 => .float .f32
  | .reinterpretFloat .i64 => .float .f64

inductive IntShape where
  | i8x16 | i16x8 | i32x4 | i64x2
  deriving DecidableEq, Repr

def IntShape.laneWidth : IntShape → Nat
  | .i8x16 => 8 | .i16x8 => 16 | .i32x4 => 32 | .i64x2 => 64

def IntShape.lanes : IntShape → Nat
  | .i8x16 => 16 | .i16x8 => 8 | .i32x4 => 4 | .i64x2 => 2

inductive FloatShape where
  | f32x4 | f64x2
  deriving DecidableEq, Repr

def FloatShape.laneWidth : FloatShape → Nat
  | .f32x4 => 32 | .f64x2 => 64

def FloatShape.lanes : FloatShape → Nat
  | .f32x4 => 4 | .f64x2 => 2

inductive Shape where
  | int (shape : IntShape)
  | float (shape : FloatShape)
  deriving DecidableEq, Repr

def Shape.lanes : Shape → Nat
  | .int s => s.lanes | .float s => s.lanes

def Shape.laneWidth : Shape → Nat
  | .int s => s.laneWidth | .float s => s.laneWidth

def Shape.unpacked : Shape → NumType
  | .int .i64x2 => .int .i64
  | .int _ => .int .i32
  | .float .f32x4 => .float .f32
  | .float .f64x2 => .float .f64

inductive Half where
  | low | high
  deriving DecidableEq, Repr

inductive VecUnOp where
  | not
  deriving DecidableEq, Repr

inductive VecBinOp where
  | and | andnot | or | xor
  deriving DecidableEq, Repr

inductive VecTernOp where
  | bitselect
  deriving DecidableEq, Repr

inductive VecTestOp where
  | anyTrue
  deriving DecidableEq, Repr

inductive VecIntUnOp where
  | abs | neg | popcnt
  deriving DecidableEq, Repr

def VecIntUnOp.valid (s : IntShape) : VecIntUnOp → Bool
  | .popcnt => s == .i8x16
  | _ => true

inductive VecIntBinOp where
  | add | sub | mul
  | addSat (sign : Signedness)
  | subSat (sign : Signedness)
  | avgrU | q15mulrSatS | relaxedQ15mulrS
  | min (sign : Signedness)
  | max (sign : Signedness)
  deriving DecidableEq, Repr

def VecIntBinOp.valid (s : IntShape) : VecIntBinOp → Bool
  | .add | .sub => true
  | .mul => s.laneWidth ≥ 16
  | .addSat _ | .subSat _ | .avgrU => s.laneWidth ≤ 16
  | .q15mulrSatS | .relaxedQ15mulrS => s == .i16x8
  | .min _ | .max _ => s.laneWidth ≤ 32

inductive VecFloatBinOp where
  | add | sub | mul | div | min | max | pmin | pmax | relaxedMin | relaxedMax
  deriving DecidableEq, Repr

inductive VecIntTernOp where
  | relaxedLaneSelect
  deriving DecidableEq, Repr

inductive VecFloatTernOp where
  | relaxedMadd | relaxedNmadd
  deriving DecidableEq, Repr

/-- Integer vector comparisons at 64-bit lane width have only signed ordering. -/
def IntRelOp.validShape (s : IntShape) : IntRelOp → Bool
  | .eq | .ne => true
  | .lt sign | .gt sign | .le sign | .ge sign => s != .i64x2 || sign == .signed

inductive VecShiftOp where
  | shl
  | shr (sign : Signedness)
  deriving DecidableEq, Repr

inductive VecSwizzleOp where
  | swizzle | relaxedSwizzle
  deriving DecidableEq, Repr

inductive VecExtUnOp where
  | extaddPairwise (sign : Signedness)
  deriving DecidableEq, Repr

def VecExtUnOp.valid (source target : IntShape) (_op : VecExtUnOp) : Bool :=
  target.laneWidth == 2 * source.laneWidth && target.laneWidth ≤ 32

inductive VecExtBinOp where
  | extmul (half : Half) (sign : Signedness)
  | dotS | relaxedDotS
  deriving DecidableEq, Repr

def VecExtBinOp.valid (source target : IntShape) : VecExtBinOp → Bool
  | .extmul _ _ => target.laneWidth == 2 * source.laneWidth
  | .dotS => source == .i16x8 && target == .i32x4
  | .relaxedDotS => source == .i8x16 && target == .i16x8

inductive VecExtTernOp where
  | relaxedDotAddS
  deriving DecidableEq, Repr

def VecExtTernOp.valid (source target : IntShape) (_op : VecExtTernOp) : Bool :=
  source == .i8x16 && target == .i32x4

inductive VecConvertOp where
  | extend (half : Half) (sign : Signedness)
  | convert (half : Option Half) (sign : Signedness)
  | truncSat (sign : Signedness) (zero : Bool)
  | relaxedTrunc (sign : Signedness) (zero : Bool)
  | demoteZero | promoteLow
  deriving DecidableEq, Repr

/-- Shape validity of `vcvtop__(sh_1, sh_2)` (the grammar side conditions of
`1.3-syntax.instructions.spectec`, used as the `Instr_ok/vcvtop` premise).

`convert` admits exactly the spec's pairs: `sizenn(Fnn_2) = lsizenn(Jnn_1) = 32`
without a half (`i32x4 → f32x4`), or `sizenn(Fnn_2) = 2 * lsizenn(Jnn_1)` with
`LOW` (`i32x4 → f64x2`, and the unencodable `i16x8 → f32x4`).

`trunc_sat`/`relaxed_trunc` admit only the two encodable pairs. The grammar also
admits `f32x4 → i16x8` with `ZERO`, but `$lcvtop__` is defined only for an
`Inn` target (`I32`/`I64`), so that instruction has no semantics in the spec
(execution stuck); it is rejected here instead (Silmaril.Wasm.Execution.Core.Instantiation, deviations). -/
def VecConvertOp.valid (source target : Shape) : VecConvertOp → Bool
  | .extend _ _ => match source, target with
    | .int s, .int t => t.laneWidth == 2 * s.laneWidth
    | _, _ => false
  | .convert half _ => match source, target with
    | .int .i32x4, .float .f32x4 => half.isNone
    | .int .i32x4, .float .f64x2 => half == some .low
    | .int .i16x8, .float .f32x4 => half == some .low
    | _, _ => false
  | .truncSat _ zero | .relaxedTrunc _ zero => match source, target with
    | .float .f32x4, .int .i32x4 => !zero
    | .float .f64x2, .int .i32x4 => zero
    | _, _ => false
  | .demoteZero => source == .float .f64x2 && target == .float .f32x4
  | .promoteLow => source == .float .f32x4 && target == .float .f64x2

/-- Exact vector load variants, including the three widening loads. -/
inductive VecLoadOp where
  | full
  | extend8x8 (sign : Signedness)
  | extend16x4 (sign : Signedness)
  | extend32x2 (sign : Signedness)
  | splat (size : PackSize)
  | zero32 | zero64
  deriving DecidableEq, Repr

end Silmaril.Wasm
