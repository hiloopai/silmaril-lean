module

-- Kernel computation uses the body of the upstream derived instance.
import all Batteries.Data.Except

public import Silmaril.Wasm.Numerics.Integer
public import Silmaril.Numeric.Ieee754.Relations
public import Silmaril.Numeric.Integer
public import Batteries.Data.Except

@[expose] public section

/-!
# WebAssembly scalar floating-point execution

This adapter connects Core floating operators and conversions to the independent
numeric scalar model. Arithmetic uses RNE and gradual underflow, preserving raw
NaN payloads for bit operations. Unary/binary result relations include Core's
allowed nondeterministic NaN payloads; executable functions choose canonical
arithmetic NaNs. Integer truncation distinguishes invalid NaN conversion from
range overflow, while `trunc_sat` clamps and maps NaN to zero.

See <https://www.w3.org/TR/wasm-core/#floating-point-operations> and
<https://www.w3.org/TR/wasm-core/#conversions>.
-/

namespace Silmaril.Wasm.Numerics

open Silmaril.Numeric.Ieee754

abbrev FloatValue (t : FloatType) := BitVec t.width
abbrev NumValue (t : NumType) := BitVec t.width

/-- Lossless reinterpretation as the scalar wrapper. -/
def asF32 (x : FloatValue .f32) : F32 := ⟨UInt32.ofBitVec x⟩
/-- Lossless reinterpretation as the scalar wrapper. -/
def asF64 (x : FloatValue .f64) : F64 := ⟨UInt64.ofBitVec x⟩

def floatUnOp32 : FloatUnOp → F32 → F32
  | .abs => F32.abs | .neg => F32.neg | .sqrt => F32.sqrt
  | .ceil => F32.ceil | .floor => F32.floor | .trunc => F32.trunc | .nearest => F32.nearest

def floatUnOp64 : FloatUnOp → F64 → F64
  | .abs => F64.abs | .neg => F64.neg | .sqrt => F64.sqrt
  | .ceil => F64.ceil | .floor => F64.floor | .trunc => F64.trunc | .nearest => F64.nearest

def floatBinOp32 : FloatBinOp → F32 → F32 → F32
  | .add => F32.add | .sub => F32.sub | .mul => F32.mul | .div => F32.div
  | .min => F32.minimum | .max => F32.maximum | .copysign => F32.copySign

def floatBinOp64 : FloatBinOp → F64 → F64 → F64
  | .add => F64.add | .sub => F64.sub | .mul => F64.mul | .div => F64.div
  | .min => F64.minimum | .max => F64.maximum | .copysign => F64.copySign

def floatRelOp32 : FloatRelOp → F32 → F32 → Bool
  | .eq => F32.equal | .ne => F32.notEqual | .lt => F32.lessThan
  | .le => F32.lessEqual | .gt => F32.greaterThan | .ge => F32.greaterEqual

def floatRelOp64 : FloatRelOp → F64 → F64 → Bool
  | .eq => F64.equal | .ne => F64.notEqual | .lt => F64.lessThan
  | .le => F64.lessEqual | .gt => F64.greaterThan | .ge => F64.greaterEqual

def floatUnOp (t : FloatType) (op : FloatUnOp) : FloatValue t → FloatValue t :=
  match t with
  | .f32 => fun x => (floatUnOp32 op (asF32 x)).bits.toBitVec
  | .f64 => fun x => (floatUnOp64 op (asF64 x)).bits.toBitVec

def floatBinOp (t : FloatType) (op : FloatBinOp) : FloatValue t → FloatValue t → FloatValue t :=
  match t with
  | .f32 => fun x y => (floatBinOp32 op (asF32 x) (asF32 y)).bits.toBitVec
  | .f64 => fun x y => (floatBinOp64 op (asF64 x) (asF64 y)).bits.toBitVec

def floatRelOp (t : FloatType) (op : FloatRelOp) : FloatValue t → FloatValue t → BitVec 32 :=
  match t with
  | .f32 => fun x y => bool32 (floatRelOp32 op (asF32 x) (asF32 y))
  | .f64 => fun x y => bool32 (floatRelOp64 op (asF64 x) (asF64 y))

/-- Sign operations are exact bit operations, including on signaling NaNs. -/
def floatUnOpRel (t : FloatType) (op : FloatUnOp) (x z : FloatValue t) : Prop :=
  match op with
  | .abs | .neg => z = floatUnOp t op x
  | _ => match t with
    | .f32 => F32.unaryResult (floatUnOp32 op) (asF32 x) (asF32 z)
    | .f64 => F64.unaryResult (floatUnOp64 op) (asF64 x) (asF64 z)

/-- Copysign preserves magnitude payload bits; arithmetic permits Core NaN choices. -/
def floatBinOpRel (t : FloatType) (op : FloatBinOp) (x y z : FloatValue t) : Prop :=
  match op with
  | .copysign => z = floatBinOp t op x y
  | _ => match t with
    | .f32 => F32.binaryResult (floatBinOp32 op) (asF32 x) (asF32 y) (asF32 z)
    | .f64 => F64.binaryResult (floatBinOp64 op) (asF64 x) (asF64 y) (asF64 z)

instance (t : FloatType) (op : FloatUnOp) (x z : FloatValue t) :
    Decidable (floatUnOpRel t op x z) := by cases op <;> cases t <;> unfold floatUnOpRel <;> infer_instance
instance (t : FloatType) (op : FloatBinOp) (x y z : FloatValue t) :
    Decidable (floatBinOpRel t op x y z) := by
  cases op <;> cases t <;> unfold floatBinOpRel <;> infer_instance

inductive FloatTrap where
  | invalidConversion
  | integerOverflow
  deriving DecidableEq, Repr

/-- Destination integer range and signedness at the generic scalar boundary. -/
def integerFormat (t : IntType) (sign : Signedness) : Silmaril.Numeric.IntFormat where
  width := t.width
  signedness := match sign with | .signed => .signed | .unsigned => .unsigned
  positive := by cases t <;> decide

def unpackFloat (t : FloatType) : FloatValue t → Float.Model.UnpackedFloat :=
  match t with
  | .f32 => fun x => (asF32 x).model.unpack
  | .f64 => fun x => (asF64 x).model.unpack

/-- Truncate first, then range-check, as required even for values between -1 and 0. -/
def truncFloat (source : FloatType) (target : IntType) (sign : Signedness)
    (x : FloatValue source) : Except FloatTrap (IntValue target) :=
  let unpacked := unpackFloat source x
  match Silmaril.Numeric.Integer.fromFloat? (integerFormat target sign) unpacked with
  | some result => .ok result.bits
  | none => if unpacked.isNaN then .error .invalidConversion else .error .integerOverflow

def truncSatFloat (source : FloatType) (target : IntType) (sign : Signedness)
    (x : FloatValue source) : IntValue target :=
  (Silmaril.Numeric.Integer.fromFloatSaturating (integerFormat target sign)
    (unpackFloat source x)).bits

def convertInt (source : IntType) (target : FloatType) (sign : Signedness)
    (x : IntValue source) : FloatValue target :=
  let n : Int := match sign with | .signed => x.toInt | .unsigned => x.toNat
  match target with
  | .f32 => (F32.ofInt n).bits.toBitVec
  | .f64 => (F64.ofInt n).bits.toBitVec

/-- All scalar Core conversions, with source and destination widths in the type. -/
def convert : (op : ConvertOp) → NumValue op.source → Except FloatTrap (NumValue op.target)
  | .wrap, x => .ok (x.setWidth 32)
  | .extend .signed, x => .ok (x.signExtend 64)
  | .extend .unsigned, x => .ok (x.setWidth 64)
  | .trunc source target sign, x => truncFloat source target sign x
  | .truncSat source target sign, x => .ok (truncSatFloat source target sign x)
  | .convert source target sign, x => .ok (convertInt source target sign x)
  | .demote, x => .ok ((asF64 x).toF32.bits.toBitVec)
  | .promote, x => .ok ((asF32 x).toF64.bits.toBitVec)
  | .reinterpretInt .f32, x => .ok x
  | .reinterpretInt .f64, x => .ok x
  | .reinterpretFloat .i32, x => .ok x
  | .reinterpretFloat .i64, x => .ok x

/-- Core conversion relation. Width-changing floating conversions permit the
same canonical/arithmetic NaN classes as arithmetic; reinterpretation remains
an exact bit operation, and integer conversions retain their specified traps. -/
def convertRel : (op : ConvertOp) → NumValue op.source →
    Except FloatTrap (NumValue op.target) → Prop
  | .demote, x, .ok y =>
    let input := asF64 x
    let result := input.toF32
    if result.IsNaN then
      if input.IsNonNaNOrCanonicalNaN then (asF32 y).IsCanonicalNaN
      else (asF32 y).IsArithmeticNaN
    else asF32 y = result
  | .promote, x, .ok y =>
    let input := asF32 x
    let result := input.toF64
    if result.IsNaN then
      if input.IsNonNaNOrCanonicalNaN then (asF64 y).IsCanonicalNaN
      else (asF64 y).IsArithmeticNaN
    else asF64 y = result
  | op, x, result => result = convert op x

instance (op : ConvertOp) (x : NumValue op.source) (result : Except FloatTrap (NumValue op.target)) :
    Decidable (convertRel op x result) := by
  cases op <;> cases result <;> simp only [convertRel] <;> infer_instance

@[simp] theorem asF32_bits (x : FloatValue .f32) : (asF32 x).bits.toBitVec = x := rfl
@[simp] theorem asF64_bits (x : FloatValue .f64) : (asF64 x).bits.toBitVec = x := rfl

theorem floatRelOp_toNat_le_one (t : FloatType) (op : FloatRelOp) (x y : FloatValue t) :
    (floatRelOp t op x y).toNat ≤ 1 := by cases t <;> exact bool32_toNat_le_one _

/-- Every deterministic unary result is admitted by Core's NaN policy. -/
theorem floatUnOpRel_self (t : FloatType) (op : FloatUnOp) (x : FloatValue t) :
    floatUnOpRel t op x (floatUnOp t op x) := by
  cases t with
  | f32 =>
    cases op with
    | abs => rfl
    | neg => rfl
    | sqrt => exact F32.sqrtRel_self _
    | ceil => exact F32.roundIntegralRel_self .towardPositive _
    | floor => exact F32.roundIntegralRel_self .towardNegative _
    | trunc => exact F32.roundIntegralRel_self .towardZero _
    | nearest => exact F32.roundIntegralRel_self .nearestTiesToEven _
  | f64 =>
    cases op with
    | abs => rfl
    | neg => rfl
    | sqrt => exact F64.sqrtRel_self _
    | ceil => exact F64.roundIntegralRel_self .towardPositive _
    | floor => exact F64.roundIntegralRel_self .towardNegative _
    | trunc => exact F64.roundIntegralRel_self .towardZero _
    | nearest => exact F64.roundIntegralRel_self .nearestTiesToEven _

/-- Every deterministic binary result is admitted by Core's NaN policy. -/
theorem floatBinOpRel_self (t : FloatType) (op : FloatBinOp) (x y : FloatValue t) :
    floatBinOpRel t op x y (floatBinOp t op x y) := by
  cases t with
  | f32 =>
    cases op with
    | add => exact F32.addRel_self _ _
    | sub => exact F32.subRel_self _ _
    | mul => exact F32.mulRel_self _ _
    | div => exact F32.divRel_self _ _
    | min => exact F32.minimumRel_self _ _
    | max => exact F32.maximumRel_self _ _
    | copysign => rfl
  | f64 =>
    cases op with
    | add => exact F64.addRel_self _ _
    | sub => exact F64.subRel_self _ _
    | mul => exact F64.mulRel_self _ _
    | div => exact F64.divRel_self _ _
    | min => exact F64.minimumRel_self _ _
    | max => exact F64.maximumRel_self _ _
    | copysign => rfl

/-- The deterministic conversions refine the complete permitted NaN relation. -/
theorem convertRel_self (op : ConvertOp) (x : NumValue op.source) :
    convertRel op x (convert op x) := by
  cases op <;> try rfl
  case demote =>
    simp only [convert, convertRel]
    split
    next h =>
      split
      · exact F64.toF32_isCanonicalNaN _ _ h
      · exact (F64.toF32_isCanonicalNaN _ _ h).isArithmeticNaN
    next => rfl
  case promote =>
    simp only [convert, convertRel]
    split
    next h =>
      split
      · exact F32.toF64_isCanonicalNaN _ h
      · exact (F32.toF64_isCanonicalNaN _ h).isArithmeticNaN
    next => rfl

example : floatBinOp .f32 .add (0x3f800000#32) (0x40000000#32) = (0x40400000#32) := by rfl
example : floatUnOp .f32 .neg (0x7f800001#32) = (0xff800001#32) := by rfl
example : floatBinOp .f64 .min (0#64) (0x8000000000000000#64) =
    (0x8000000000000000#64) := by rfl
example : floatRelOp .f32 .eq (0#32) (0x80000000#32) = (1#32) := by decide
example : floatBinOpRel .f32 .add (0x7f800000#32) (0xff800000#32) (0xffc00000#32) := by
  unfold floatBinOpRel
  decide
example : convert (.trunc .f32 .i32 .unsigned) (0xbf000000#32) = .ok (0#32) := by decide
example : convert (.trunc .f32 .i32 .signed) (0x7fc00000#32) = .error .invalidConversion := by decide
example : convert (.trunc .f32 .i32 .signed) (0x4f000000#32) = .error .integerOverflow := by decide
example : convert (.truncSat .f32 .i32 .signed) (0x7f800000#32) = .ok (0x7fffffff#32) := by decide
example : convert (.reinterpretInt .f32) (0xff800001#32) = .ok (0xff800001#32) := by decide

example : convertRel .promote (0xffc00000#32) (.ok (0xfff8000000000000#64)) := by
  simp only [convertRel]
  decide
example : convertRel .demote (0x7ff8000000000001#64) (.ok (0x7fc00001#32)) := by
  simp only [convertRel]
  decide

example : convert (.convert .i64 .f32 .unsigned) (-1#64) = .ok (0x5f800000#32) := by decide
example : convert (.convert .i64 .f64 .unsigned) (-1#64) = .ok (0x43f0000000000000#64) := by decide
example : convert (.trunc .f32 .i32 .signed) (0xcf000000#32) = .ok (0x80000000#32) := by decide

end Silmaril.Wasm.Numerics
