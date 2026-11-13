module

public import Silmaril.Wasm.Component.Reference.ABI.Memory.Defs

/-!
# Canonical floats and chars

Canonical ABI adapters for the WIT primitives `f32`, `f64`, and `char`, following
`definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b/design/mvp/canonical-abi/definitions.py>)
and `CanonicalABI.md` §"Loading", §"Storing", §"Flat Lifting", and §"Flat Lowering".

Floats are raw IEEE-754 interchange bits (`BitVec t.width`), the same carrier as
`Silmaril.Wasm.Numerics.FloatValue` and `Execution.Runtime.Value.float`. With this
carrier the reference's `core_f32_reinterpret_i32`, `core_i32_reinterpret_f32`, and
their 64-bit forms are bit casts (`reinterpretIntAsFloat`, `reinterpretFloatAsInt`).

* `CANONICAL_FLOAT32_NAN` and `CANONICAL_FLOAT64_NAN` are `canonicalNaN`.
  `canonicalize_nan32` and `canonicalize_nan64` are `canonicalizeNaN`.
  `decode_i32_as_float` and `decode_i64_as_float` are `decodeFloat`.
* `maybe_scramble_nan32` and `maybe_scramble_nan64` are the relation `ScrambleNaN`.
  With `deterministic := true` (`DETERMINISTIC_PROFILE`), a NaN becomes exactly the
  canonical NaN. With `deterministic := false`, a NaN may become *any* NaN. This is
  what the `CanonicalABI.md` §"Storing" prose permits ("Hosts may instead chose to
  canonicalize to an arbitrary fixed NaN value, or even to the original value of the
  NaN before lifting"). It is a strict superset of the image of the Python
  `random_nan_bits`, which never produces the canonical NaN (it always sets a
  fraction bit below the quiet bit). `RandomNaNBits` states that image exactly.
  `encode_float_as_i32` and `encode_float_as_i64` are `EncodeFloat`.
* `lift_flat` (`F32Type`/`F64Type`) is `liftFloatFlat`. `lower_flat` is
  `LowerFloatFlat`. `load` is `loadFloat`. `store` is `StoreFloat`. The
  deterministic executable choices are `lowerFloatFlatCanonical` and
  `storeFloatCanonical`.
* `convert_i32_to_char` is `convertI32ToChar?` (`none` is a trap), and `char_to_i32`
  is `charToI32`. Chars are Lean `Char`, whose invariant is exactly "Unicode scalar
  value". `liftCharFlat`, `lowerCharFlat`, `loadChar`, and `storeChar` are the
  corresponding `lift_flat`, `lower_flat`, `load`, and `store` cases.

As in `ABI.Memory`, memory helpers allow unaligned access and fail (`none`) out of
bounds. Alignment and pointer-width checks belong to the enclosing adapter. For
`loadChar`, `none` merges an out-of-bounds access and an invalid scalar value, and
both trap in the reference.

**wasmtime** (`a7b4f29`). `crates/wasmtime/src/runtime/component/func/typed.rs`
(`floats!`) lifts and lowers host `f32`/`f64` by `from_bits`/`to_bits`, and
`crates/environ/src/fact/trampoline.rs` (`translate_f32`, `translate_f64`) copies
float bits between components unchanged. wasmtime therefore neither canonicalizes on
lift nor scrambles on lower. Its end-to-end identity on bits is admitted by the
nondeterministic profile, since lift then `ScrambleNaN false` may return the original
NaN (`scrambleNaN_canonicalizeNaN_self` in `FloatChar/Properties`). It is *not* the
deterministic profile. A wasmtime host can also observe non-canonical NaN payloads
that the reference's lift would have erased. wasmtime's `char` lift is
`char::try_from(u32)`. The adapter's inline check in `translate_char` is transcribed
as `wasmtimeCharCheck` and proved equivalent to `convertI32ToChar?` succeeding.

**Integration note.** `ABI.Scalar.Scalar`/`ScalarValue` cover only booleans and
integers, and they are not modified here. The proposed extension adds the cases
`f32 | f64 | char` to `Scalar`, with `width` 32/64/32 and `coreType` generalised
from `IntType` to `NumType`. Float `bits` would be raw bits (lift: `decodeFloat`,
lower: `ScrambleNaN`), and a char's bits would carry the proof
`bits.toNat.isValidChar`, or the value type would become an inductive with a `Char`
case. Lowering then becomes a relation (because of NaN nondeterminism) with the
deterministic function as a witness.

Not modelled: the Python float type itself (the reference's `math.isnan` is the bit
predicate `isNaN` here), and the `latin1+utf16` string machinery that also
uses `char`. No conformance claim beyond the theorems in `FloatChar/Properties` is
made.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

open Silmaril.Wasm.Execution

/-! ## Floating-point bits -/

/-- Trailing-significand (fraction) width: 23 for binary32, 52 for binary64. -/
def floatFractionWidth : FloatType → Nat
  | .f32 => 23
  | .f64 => 52

/-- Biased exponent width: 8 for binary32, 11 for binary64. -/
def floatExponentWidth : FloatType → Nat
  | .f32 => 8
  | .f64 => 11

/-- Bytes occupied in linear memory (`elem_size` of `F32Type`/`F64Type`). -/
def floatByteCount : FloatType → Nat
  | .f32 => 4
  | .f64 => 8

theorem width_eq_floatByteCount (t : FloatType) : t.width = 8 * floatByteCount t := by
  cases t <;> rfl

/-- The core integer type used by `reinterpret` for this float type. -/
def floatIntType : FloatType → IntType
  | .f32 => .i32
  | .f64 => .i64

theorem floatIntType_width (t : FloatType) : (floatIntType t).width = t.width := by
  cases t <;> rfl

/-- IEEE-754 NaN on raw interchange bits: all-ones exponent, nonzero fraction.
This is `math.isnan` of the reinterpreted Python float. -/
def isNaN (t : FloatType) (x : BitVec t.width) : Bool :=
  x.extractLsb' (floatFractionWidth t) (floatExponentWidth t) ==
      BitVec.allOnes (floatExponentWidth t) &&
    x.extractLsb' 0 (floatFractionWidth t) != 0

/-- `CANONICAL_FLOAT32_NAN = 0x7fc00000`, `CANONICAL_FLOAT64_NAN = 0x7ff8000000000000`. -/
def canonicalNaN : (t : FloatType) → BitVec t.width
  | .f32 => 0x7fc00000#32
  | .f64 => 0x7ff8000000000000#64

/-- `canonicalize_nan32` / `canonicalize_nan64`. -/
def canonicalizeNaN (t : FloatType) (x : BitVec t.width) : BitVec t.width :=
  if isNaN t x then canonicalNaN t else x

/-- A component-level float: at most one NaN bit pattern (Explainer: "with a single
NaN value"). Every lifted float satisfies this (`decodeFloat_canonical`). -/
def IsCanonicalFloat (t : FloatType) (x : BitVec t.width) : Prop :=
  isNaN t x = true → x = canonicalNaN t

/-- `core_f32_reinterpret_i32` / `core_f64_reinterpret_i64` on raw bits. -/
def reinterpretIntAsFloat (t : FloatType) (i : BitVec (floatIntType t).width) : BitVec t.width :=
  i.cast (floatIntType_width t)

/-- `core_i32_reinterpret_f32` / `core_i64_reinterpret_f64` on raw bits. -/
def reinterpretFloatAsInt (t : FloatType) (x : BitVec t.width) : BitVec (floatIntType t).width :=
  x.cast (floatIntType_width t).symm

/-- `decode_i32_as_float` / `decode_i64_as_float`. -/
def decodeFloat (t : FloatType) (i : BitVec (floatIntType t).width) : BitVec t.width :=
  canonicalizeNaN t (reinterpretIntAsFloat t i)

/-- `maybe_scramble_nan32` / `maybe_scramble_nan64` as a relation. Non-NaN bits are
preserved. In the deterministic profile a NaN becomes the canonical NaN; otherwise it
may become any NaN. -/
inductive ScrambleNaN (deterministic : Bool) (t : FloatType) :
    BitVec t.width → BitVec t.width → Prop
  | nonNaN (x : BitVec t.width) (notNaN : isNaN t x = false) : ScrambleNaN deterministic t x x
  | canonical (x : BitVec t.width) (nan : isNaN t x = true) (profile : deterministic = true) :
      ScrambleNaN deterministic t x (canonicalNaN t)
  | scrambled (x y : BitVec t.width) (nan : isNaN t x = true) (profile : deterministic = false)
      (chosen : isNaN t y = true) : ScrambleNaN deterministic t x y

/-- The exact image of the Python `random_nan_bits(total_bits, exponent_bits)`: an
all-ones exponent and some fraction bit strictly below the quiet bit. -/
def RandomNaNBits (t : FloatType) (y : BitVec t.width) : Prop :=
  y.extractLsb' (floatFractionWidth t) (floatExponentWidth t) =
      BitVec.allOnes (floatExponentWidth t) ∧
    ∃ i, i + 1 < floatFractionWidth t ∧ y.getLsbD i = true

/-- Scrambling with an explicit choice of replacement NaN (a scheduler/oracle
parameter); `pick` is used only when `x` is a NaN. -/
def scrambleNaNWith (t : FloatType) (pick : BitVec t.width) (x : BitVec t.width) :
    BitVec t.width :=
  if isNaN t x then pick else x

/-- `encode_float_as_i32` / `encode_float_as_i64`. -/
def EncodeFloat (deterministic : Bool) (t : FloatType) (x : BitVec t.width)
    (i : BitVec (floatIntType t).width) : Prop :=
  ∃ y, ScrambleNaN deterministic t x y ∧ i = reinterpretFloatAsInt t y

/-! ## Flat and memory adapters for floats -/

/-- `lift_flat` for `F32Type`/`F64Type`: `canonicalize_nan32(vi.next('f32'))`. A
core value of the wrong type is rejected (`none`); validation excludes that case in
the reference. -/
def liftFloatFlat (t : FloatType) (v : Runtime.Value) : Option (BitVec t.width) :=
  if h : v.type = .float t then some (canonicalizeNaN t (v.bits.cast (congrArg NumType.width h)))
  else none

/-- `lower_flat` for `F32Type`/`F64Type`: `[maybe_scramble_nan32(v)]`. -/
def LowerFloatFlat (deterministic : Bool) (t : FloatType) (x : BitVec t.width)
    (v : Runtime.Value) : Prop :=
  ∃ y, ScrambleNaN deterministic t x y ∧ v = .float t y

/-- The deterministic-profile lowering, which is admitted by both profiles. -/
def lowerFloatFlatCanonical (t : FloatType) (x : BitVec t.width) : Runtime.Value :=
  .float t (canonicalizeNaN t x)

/-- Raw little-endian float bits, before NaN canonicalization. -/
def loadFloatBits (t : FloatType) (memory : ByteArray) (start : Nat) :
    Option (BitVec t.width) :=
  (Memory.load memory start (floatByteCount t)).map fun bits =>
    bits.cast (width_eq_floatByteCount t).symm

/-- Raw little-endian float bits, with no NaN scrambling. -/
def storeFloatBits (t : FloatType) (memory : ByteArray) (start : Nat) (x : BitVec t.width) :
    Option ByteArray :=
  Memory.store memory start (x.cast (width_eq_floatByteCount t))

/-- `load` for `F32Type`/`F64Type`: `decode_i32_as_float(load_int(cx, ptr, 4))`. -/
def loadFloat (t : FloatType) (memory : ByteArray) (start : Nat) : Option (BitVec t.width) :=
  (loadFloatBits t memory start).map (canonicalizeNaN t)

/-- `store` for `F32Type`/`F64Type`: `store_int(cx, encode_float_as_i32(v), ptr, 4)`.
`after = none` is an out-of-bounds trap. -/
def StoreFloat (deterministic : Bool) (t : FloatType) (memory : ByteArray) (start : Nat)
    (x : BitVec t.width) (after : Option ByteArray) : Prop :=
  ∃ y, ScrambleNaN deterministic t x y ∧ after = storeFloatBits t memory start y

/-- The deterministic-profile store. -/
def storeFloatCanonical (t : FloatType) (memory : ByteArray) (start : Nat)
    (x : BitVec t.width) : Option ByteArray :=
  storeFloatBits t memory start (canonicalizeNaN t x)

/-! ## Chars -/

/-- A Unicode scalar value: below `0x110000` and not a surrogate. -/
def IsUnicodeScalar (n : Nat) : Prop := n < 0x110000 ∧ ¬ (0xD800 ≤ n ∧ n ≤ 0xDFFF)

instance (n : Nat) : Decidable (IsUnicodeScalar n) := by
  unfold IsUnicodeScalar
  infer_instance

theorem isUnicodeScalar_iff_isValidChar (n : Nat) : IsUnicodeScalar n ↔ n.isValidChar := by
  simp only [IsUnicodeScalar, Nat.isValidChar]
  omega

/-- `convert_i32_to_char`. `none` is a trap (`trap_if(i >= 0x110000)` or
`trap_if(0xD800 <= i <= 0xDFFF)`). -/
def convertI32ToChar? (i : BitVec 32) : Option Char :=
  if h : IsUnicodeScalar i.toNat then
    some (Char.ofNatAux i.toNat ((isUnicodeScalar_iff_isValidChar _).mp h))
  else none

/-- `char_to_i32`. -/
def charToI32 (c : Char) : BitVec 32 := c.val.toBitVec

/-- `lift_flat` for `CharType`: `convert_i32_to_char(cx, vi.next('i32'))`. -/
def liftCharFlat (v : Runtime.Value) : Option Char :=
  if h : v.type = .int .i32 then convertI32ToChar? (v.bits.cast (congrArg NumType.width h))
  else none

/-- `lower_flat` for `CharType`: `[char_to_i32(v)]`. -/
def lowerCharFlat (c : Char) : Runtime.Value := .int .i32 (charToI32 c)

/-- `load` for `CharType`: `convert_i32_to_char(cx, load_int(cx, ptr, 4))`. -/
def loadChar (memory : ByteArray) (start : Nat) : Option Char :=
  (Memory.load memory start 4).bind convertI32ToChar?

/-- `store` for `CharType`: `store_int(cx, char_to_i32(v), ptr, 4)`. -/
def storeChar (memory : ByteArray) (start : Nat) (c : Char) : Option ByteArray :=
  Memory.store memory start (count := 4) (charToI32 c)

/-- The inline validity test emitted by wasmtime's FACT `translate_char`
(`crates/environ/src/fact/trampoline.rs` at `a7b4f29`). The first `br_if` takes the
trap path when `((x ^ 0xd800) + -0x110000) <u -0x10f800`. Otherwise the value is
accepted iff `x ≠ 0x110000`. -/
def wasmtimeCharCheck (x : BitVec 32) : Bool :=
  !(BitVec.ult ((x ^^^ 0xd800#32) + (-0x110000 : BitVec 32)) (-0x10f800 : BitVec 32)) &&
    x != 0x110000#32

end Silmaril.Wasm.Component.ABI
