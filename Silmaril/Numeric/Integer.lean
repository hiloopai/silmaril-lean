module

public import Silmaril.Numeric.Ieee754.Rounding

/-!
# Bounded integers at the floating-point boundary

Widths and signedness are explicit. Conversion rounds before checking bounds;
there is no implicit modular wrapping of an out-of-range floating-point value.
`fromFloat?` rejects NaNs, infinities, and out-of-range rounded values.
`fromFloatSaturating` is a separate, total policy: NaN becomes zero and
infinities/overflow clamp to the appropriate endpoint. A target instruction's
invalid-conversion policy must be selected by its semantics.

IEEE 754-2019 §5.8 specifies integer conversions; §7.2 describes invalid
conversions. PTX `cvt` adds instruction-specific saturation and NaN behavior:
<https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#data-movement-and-conversion-instructions-cvt>.
-/

@[expose] public section

namespace Silmaril.Numeric

inductive Signedness where
  | unsigned | signed
  deriving DecidableEq, Repr

/-- A nonempty fixed-width integer representation, including sub-byte integers. -/
structure IntFormat where
  width : Nat
  signedness : Signedness
  positive : 0 < width := by decide
  deriving DecidableEq, Repr

namespace IntFormat

def minValue (f : IntFormat) : Int :=
  match f.signedness with
  | .unsigned => 0
  | .signed => -(2 ^ (f.width - 1) : Int)

def maxValue (f : IntFormat) : Int :=
  match f.signedness with
  | .unsigned => 2 ^ f.width - 1
  | .signed => 2 ^ (f.width - 1) - 1

abbrev u1 : IntFormat := ⟨1, .unsigned, by decide⟩
abbrev u4 : IntFormat := ⟨4, .unsigned, by decide⟩
abbrev i4 : IntFormat := ⟨4, .signed, by decide⟩
abbrev u8 : IntFormat := ⟨8, .unsigned, by decide⟩
abbrev i8 : IntFormat := ⟨8, .signed, by decide⟩
abbrev u16 : IntFormat := ⟨16, .unsigned, by decide⟩
abbrev i16 : IntFormat := ⟨16, .signed, by decide⟩
abbrev u32 : IntFormat := ⟨32, .unsigned, by decide⟩
abbrev i32 : IntFormat := ⟨32, .signed, by decide⟩
abbrev u64 : IntFormat := ⟨64, .unsigned, by decide⟩
abbrev i64 : IntFormat := ⟨64, .signed, by decide⟩

end IntFormat

/-- Lossless integer storage; numeric casts are distinct from bit reinterpretation. -/
structure Integer (format : IntFormat) where
  bits : BitVec format.width
  deriving DecidableEq, Repr

namespace Integer

variable {format : IntFormat}

/-- Lossless bridges from Lean's machine integers, preserving their bits. -/
def ofUInt8 (x : UInt8) : Integer .u8 := ⟨x.toBitVec⟩
def ofInt8 (x : Int8) : Integer .i8 := ⟨x.toBitVec⟩
def ofUInt16 (x : UInt16) : Integer .u16 := ⟨x.toBitVec⟩
def ofInt16 (x : Int16) : Integer .i16 := ⟨x.toBitVec⟩
def ofUInt32 (x : UInt32) : Integer .u32 := ⟨x.toBitVec⟩
def ofInt32 (x : Int32) : Integer .i32 := ⟨x.toBitVec⟩
def ofUInt64 (x : UInt64) : Integer .u64 := ⟨x.toBitVec⟩
def ofInt64 (x : Int64) : Integer .i64 := ⟨x.toBitVec⟩

def asUInt8 (x : Integer .u8) : UInt8 := UInt8.ofBitVec x.bits
def asInt8 (x : Integer .i8) : Int8 := Int8.ofBitVec x.bits
def asUInt16 (x : Integer .u16) : UInt16 := UInt16.ofBitVec x.bits
def asInt16 (x : Integer .i16) : Int16 := Int16.ofBitVec x.bits
def asUInt32 (x : Integer .u32) : UInt32 := UInt32.ofBitVec x.bits
def asInt32 (x : Integer .i32) : Int32 := Int32.ofBitVec x.bits
def asUInt64 (x : Integer .u64) : UInt64 := UInt64.ofBitVec x.bits
def asInt64 (x : Integer .i64) : Int64 := Int64.ofBitVec x.bits

@[simp] theorem asUInt8_ofUInt8 (x : UInt8) : (ofUInt8 x).asUInt8 = x := rfl
@[simp] theorem asInt8_ofInt8 (x : Int8) : (ofInt8 x).asInt8 = x := rfl
@[simp] theorem asUInt16_ofUInt16 (x : UInt16) : (ofUInt16 x).asUInt16 = x := rfl
@[simp] theorem asInt16_ofInt16 (x : Int16) : (ofInt16 x).asInt16 = x := rfl
@[simp] theorem asUInt32_ofUInt32 (x : UInt32) : (ofUInt32 x).asUInt32 = x := rfl
@[simp] theorem asInt32_ofInt32 (x : Int32) : (ofInt32 x).asInt32 = x := rfl
@[simp] theorem asUInt64_ofUInt64 (x : UInt64) : (ofUInt64 x).asUInt64 = x := rfl
@[simp] theorem asInt64_ofInt64 (x : Int64) : (ofInt64 x).asInt64 = x := rfl

def toInt (x : Integer format) : Int :=
  match format.signedness with
  | .unsigned => x.bits.toNat
  | .signed => x.bits.toInt

/-- Checked construction from a mathematical integer. -/
def ofInt? (format : IntFormat) (n : Int) : Option (Integer format) :=
  if format.minValue ≤ n ∧ n ≤ format.maxValue then
    some ⟨BitVec.ofInt format.width n⟩
  else none

/-- Explicit modular construction, for integer operations and bit-level models. -/
def ofIntWrapping (format : IntFormat) (n : Int) : Integer format :=
  ⟨BitVec.ofInt format.width n⟩

/-- Clamp to the integer destination range before encoding. -/
def ofIntSaturating (format : IntFormat) (n : Int) : Integer format :=
  ofIntWrapping format (max format.minValue (min format.maxValue n))

/-- An exact unpacked value: no intermediate floating-point rounding. -/
def unpack (x : Integer format) : Float.Model.UnpackedFloat :=
  Ieee754.Rounding.ofInt x.toInt

def fromFloat? (format : IntFormat) (x : Float.Model.UnpackedFloat)
    (mode : Ieee754.RoundingMode := .towardZero) : Option (Integer format) :=
  (Ieee754.Rounding.toInt? mode x).bind (ofInt? format)

/-- Explicit saturation profile, with NaN mapped to zero. -/
def fromFloatSaturating (format : IntFormat) (x : Float.Model.UnpackedFloat)
    (mode : Ieee754.RoundingMode := .towardZero) : Integer format :=
  match x with
  | .notANumber => ofIntWrapping format 0
  | .infinity .negative => ofIntWrapping format format.minValue
  | .infinity .positive => ofIntWrapping format format.maxValue
  | _ => ofIntSaturating format ((Ieee754.Rounding.toInt? mode x).getD 0)

/-- Round directly into the destination precision, even for 64-bit integers. -/
def toF32 (x : Integer format) (mode : Ieee754.RoundingMode := .nearestTiesToEven) :
    Ieee754.F32 :=
  ⟨UInt32.ofBitVec (Ieee754.Rounding.packRounded .binary32 mode x.unpack)⟩

def toF64 (x : Integer format) (mode : Ieee754.RoundingMode := .nearestTiesToEven) :
    Ieee754.F64 :=
  ⟨UInt64.ofBitVec (Ieee754.Rounding.packRounded .binary64 mode x.unpack)⟩

/-- A successful checked conversion preserved the rounded mathematical integer. -/
theorem ofInt?_value {f : IntFormat} {n : Int} {x : Integer f}
    (h : ofInt? f n = some x) : x.toInt = n := by
  unfold ofInt? at h
  split at h
  next bounds =>
    cases Option.some.inj h
    cases hs : f.signedness with
    | signed =>
      simp only [toInt, hs]
      apply BitVec.toInt_ofInt_eq_self f.positive
      · simpa [IntFormat.minValue, hs] using bounds.1
      · have hb := bounds.2
        simp only [IntFormat.maxValue, hs] at hb
        omega
    | unsigned =>
      simp only [toInt, hs, BitVec.toNat_ofInt]
      have hn : 0 ≤ n := by simpa [IntFormat.minValue, hs] using bounds.1
      have hu : n < (2 : Int) ^ f.width := by
        have hb := bounds.2
        simp only [IntFormat.maxValue, hs] at hb
        omega
      simp only [Int.natCast_pow, Int.cast_ofNat_Int]
      rw [Int.emod_eq_of_lt hn hu, Int.toNat_of_nonneg hn]
  next => contradiction

theorem ofInt?_bounds {f : IntFormat} {n : Int} {x : Integer f}
    (h : ofInt? f n = some x) : f.minValue ≤ n ∧ n ≤ f.maxValue := by
  unfold ofInt? at h
  split at h
  next hb => exact hb
  next => contradiction

/-- Every stored integer lies within its format's range, at any positive width. -/
theorem toInt_bounds (x : Integer format) :
    format.minValue ≤ x.toInt ∧ x.toInt ≤ format.maxValue := by
  cases hs : format.signedness with
  | signed =>
    simp only [toInt, IntFormat.minValue, IntFormat.maxValue, hs]
    exact ⟨BitVec.le_toInt _, BitVec.toInt_le⟩
  | unsigned =>
    simp only [toInt, IntFormat.minValue, IntFormat.maxValue, hs]
    have hx := x.bits.isLt
    constructor
    · omega
    · exact Int.le_sub_one_of_lt (by exact_mod_cast hx)

/-- Checked construction recovers the original bits, for every width and signedness. -/
@[simp] theorem ofInt?_toInt (x : Integer format) :
    ofInt? format x.toInt = some x := by
  unfold ofInt?
  rw [ite_eq_left x.toInt_bounds]
  congr 1
  cases hs : format.signedness with
  | signed => simp [toInt, hs]
  | unsigned => simp [toInt, hs]

/-- Exact unpacking followed by integer conversion is a round trip in every
rounding direction. This does not insert a bounded floating-point format. -/
@[simp] theorem fromFloat?_unpack (x : Integer format) (mode : Ieee754.RoundingMode) :
    fromFloat? format x.unpack mode = some x := by
  simp [fromFloat?, unpack]

/-- A successful floating-point conversion represents exactly the integer
selected by the requested rounding direction. -/
theorem fromFloat?_value {f : IntFormat} {value : Float.Model.UnpackedFloat}
    {mode : Ieee754.RoundingMode} {x : Integer f}
    (h : fromFloat? f value mode = some x) :
    Ieee754.Rounding.toInt? mode value = some x.toInt := by
  unfold fromFloat? at h
  cases hv : Ieee754.Rounding.toInt? mode value with
  | none => simp [hv] at h
  | some n =>
    simp only [hv, Option.bind_some] at h
    rw [ofInt?_value h]

end Integer

namespace Ieee754.F32

/-- Checked conversion to an explicitly sized and signed integer destination. -/
def toInteger? (x : F32) (target : IntFormat) (mode : RoundingMode := .towardZero) :
    Option (Integer target) := Integer.fromFloat? target x.model.unpack mode

/-- Saturating integer conversion, with the explicit NaN-to-zero policy. -/
def toIntegerSaturating (x : F32) (target : IntFormat) (mode : RoundingMode := .towardZero) :
    Integer target := Integer.fromFloatSaturating target x.model.unpack mode

/-- Round a bounded integer directly to binary32. -/
def ofInteger {source : IntFormat} (x : Integer source)
    (mode : RoundingMode := .nearestTiesToEven) : F32 := x.toF32 mode

end Ieee754.F32

namespace Ieee754.F64

/-- Checked conversion to an explicitly sized and signed integer destination. -/
def toInteger? (x : F64) (target : IntFormat) (mode : RoundingMode := .towardZero) :
    Option (Integer target) := Integer.fromFloat? target x.model.unpack mode

/-- Saturating integer conversion, with the explicit NaN-to-zero policy. -/
def toIntegerSaturating (x : F64) (target : IntFormat) (mode : RoundingMode := .towardZero) :
    Integer target := Integer.fromFloatSaturating target x.model.unpack mode

/-- Round a bounded integer directly to binary64. -/
def ofInteger {source : IntFormat} (x : Integer source)
    (mode : RoundingMode := .nearestTiesToEven) : F64 := x.toF64 mode

end Ieee754.F64

end Silmaril.Numeric
