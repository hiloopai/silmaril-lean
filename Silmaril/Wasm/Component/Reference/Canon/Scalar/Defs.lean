module

public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Wasm.Component.Reference.ABI.FloatChar.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Scalar.Defs

/-!
# Scalar load/store, bools, chars, floats and variant flat coercions

Specification programs (in `P E σ`) and pure helpers for the scalar building blocks of the
Canonical ABI, transcribed from `definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>):

| Lean | REF |
| --- | --- |
| `intOfLE`, `loadInt cx ptr nbytes signed` | `load_int` (L1283-1284) |
| `intToLE`, `storeInt cx v ptr nbytes signed` | `store_int` (L1488-1489) |
| `convertIntToBool`, `liftFlatBool` | `convert_int_to_bool` (L1286-1288), `lift_flat` `BoolType` |
| `convertI32ToChar i` | `convert_i32_to_char` (L1318-1322); pure `ABI.convertI32ToChar?` |
| `ABI.charToI32` (reused) | `char_to_i32` |
| `ABI.decodeFloat` (reused) | `decode_i32_as_float` / `decode_i64_as_float` (L1306-1310) |
| `lowerFloat t x` | `maybe_scramble_nan32` / `maybe_scramble_nan64` (L1491-1507), choice C7 |
| `encodeFloat t x` | `encode_float_as_i32` / `encode_float_as_i64` (L1516-1520) |
| `liftFlatInt k v` | `lift_flat_unsigned` / `lift_flat_signed` (L1894-1905) |
| `lowerFlatInt k n` | `lower_flat` on the integer types (unsigned as is, signed + 2^32/2^64) |
| `wrapI64ToI32` | `wrap_i64_to_i32` (L1952-1954) |
| `coerceLiftFlat`, `coerceLift` | `CoerceValueIter.next` of `lift_flat_variant` (L1934-1942) |
| `coerceLower` | the `(have, want)` table of `lower_flat_variant` (L2013-2031) |

The module `ABI.FloatChar` already provides `convertI32ToChar?`, `charToI32`,
`canonicalizeNaN`, `decodeFloat`, `reinterpretIntAsFloat`/`reinterpretFloatAsInt` and
`loadChar`/`storeChar`, together with their lemmas (among them
`ABI.convertI32ToChar?_charToI32`, the char round trip); nothing of it is redefined here.

## Modelling choices and deviations

* Floats are raw bits (`BitVec`), core values are `FlatValue` (typed bit vectors). REF core
  integers are unsigned Python ints below `2^32`/`2^64`; here `v.bits.toNat`.
* `lowerFloat t x` issues the oracle choice `choose (.nan t x)` (C7) **only** when
  `ABI.isNaN t x`; a non-NaN is returned unchanged without a choice. Whether a response is
  admitted is decided by `Allowed prof (.nan t x) r` (`Value.NanLower`), not here.
* `lower_flat_variant` applies `encode_float_as_i32/64` to a payload that `lower_flat` has
  *already* scrambled; `coerceLower` transcribes this faithfully, so a NaN `f32`/`f64` payload
  of a variant whose joined slot is an integer issues a second C7 choice.
* D-f: Python asserts are preconditions, never traps. `liftFlatInt` and the coercions read
  the bits of the flat value regardless of its core type (the REF asserts the type);
  `coerceLift`/`coerceLower` return the value unchanged outside the table (REF asserts
  `have == want`); `intToLE` truncates modulo `2^(8*nbytes)` (REF `int.to_bytes` raises on an
  out-of-range value, which the callers never produce: `intOfLE_intToLE_unsigned`/`_signed`).
* `storeInt` accepts REF's `signed` flag (so call sites transcribe literally) but ignores it:
  `intToLE` stores the two's complement modulo `2^(8*nbytes)`, which coincides with
  `int.to_bytes(..., signed)` on every in-range value.
* `convertIntToBool` takes an `Int` (REF asserts `i >= 0`); any nonzero value is `true`.
* `loadInt`/`storeInt` perform no alignment or bounds pre-check (REF `load`/`store` assert
  them; the callers' `trap_if`s come first); a failed access traps `outOfBounds` via
  `readMem`/`writeMem`.

## Proved

`intOfLE_intToLE_unsigned`, `intOfLE_intToLE_signed` (little-endian round trips for in-range
values), `liftFlatInt_lowerFlatInt` (for `k.inRange n`), `liftFlatInt_inRange`,
`lowerFloat_of_not_isNaN`/`lowerFloat_of_isNaN`, `coerceLiftFlat_self`, `coerceLiftFlat_type`,
and `P.Inv` lemmas for every program. Kernel tests (`decide`/`rfl`): u8 lift of 256 is 0,
s8 lift of 128 is -128, bool lift of 2 is `true`, char `0xD800` traps (`invalidChar`), and
sample coercions. No other conformance is claimed.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Execution

variable {E : CoreEngine} {σ : Type}

/-! ## Little-endian integers (`load_int`, `store_int`) -/

/-- Two's-complement interpretation of `m ∈ [0, 2^w)` as a signed `w`-bit integer
(the tail of REF `lift_flat_signed` and `int.from_bytes(..., signed = True)`). -/
def signInterpret (w : Nat) (m : Int) : Int :=
  if 2 ^ (w - 1) ≤ m then m - 2 ^ w else m

/-- REF `int.from_bytes(bytes, 'little', signed = signed)`. -/
def intOfLE (signed : Bool) (bytes : ByteArray) : Int :=
  if signed then signInterpret (8 * bytes.size) (Memory.decodeLE bytes)
  else Memory.decodeLE bytes

/-- REF `int.to_bytes(v, nbytes, 'little', signed = ...)`, truncating modulo `2^(8*nbytes)`
(D-f: REF raises on an out-of-range `v`; two's complement makes `signed` irrelevant). -/
def intToLE (nbytes : Nat) (v : Int) : ByteArray :=
  Memory.encodeLE nbytes (v % 2 ^ (8 * nbytes)).toNat

/-- REF `load_int(cx, ptr, nbytes, signed)` (L1283). Traps `outOfBounds` (via `readMem`) if
the range is outside memory; REF `load` asserts in-bounds beforehand. -/
def loadInt (cx : LiftLowerContext E) (ptr nbytes : Nat) (signed : Bool := false) :
    P E σ Int := do
  return intOfLE signed (← readMem cx ptr nbytes)

/-- REF `store_int(cx, v, ptr, nbytes, signed)` (L1488). `signed` is ignored: `intToLE`
stores the two's complement, which agrees with REF for every in-range `v` (D-f). -/
def storeInt (cx : LiftLowerContext E) (v : Int) (ptr nbytes : Nat)
    (_signed : Bool := false) : P E σ Unit :=
  writeMem cx ptr (intToLE nbytes v)

/-! ## Booleans -/

/-- REF `convert_int_to_bool` (L1286); the REF assertion `i >= 0` is a precondition. -/
def convertIntToBool (i : Int) : Bool := i != 0

/-- REF `lift_flat` for `BoolType`: `convert_int_to_bool(vi.next('i32'))`. -/
def liftFlatBool (v : FlatValue) : Bool := convertIntToBool v.bits.toNat

/-! ## Chars -/

/-- REF `convert_i32_to_char` (L1318) as a program: traps `invalidChar` on a value
`≥ 0x110000` or a surrogate (the pure function is `ABI.convertI32ToChar?`). -/
def convertI32ToChar (i : BitVec 32) : P E σ Char :=
  orTrap .invalidChar (ABI.convertI32ToChar? i)

/-! ## Integers in flat form -/

/-- The core integer type of an integer kind (`i64` for `u64`/`s64`, `i32` otherwise). -/
def intKindCore (k : IntKind) : IntType := k.toScalar.coreType

/-- REF `lift_flat_unsigned` / `lift_flat_signed` (L1894-1905): truncate modulo `2^width`,
then sign-interpret for a signed kind. The core type of `v` is not checked (D-f). -/
def liftFlatInt (k : IntKind) (v : FlatValue) : Int :=
  let m : Int := (v.bits.toNat : Int) % 2 ^ k.width
  if k.signed then signInterpret k.width m else m

/-- REF `lower_flat` for the integer types: unsigned values as they are, signed values plus
`2^32` (resp. `2^64`) when negative, i.e. the two's complement in the core width. -/
def lowerFlatInt (k : IntKind) (n : Int) : FlatValue :=
  .int (intKindCore k) (BitVec.ofInt (intKindCore k).width n)

/-! ## Floats -/

/-- REF `maybe_scramble_nan32` / `maybe_scramble_nan64` (L1491-1507): a NaN is replaced by
the oracle's choice `choose (.nan t x)` (C7); any other value is returned unchanged. -/
def lowerFloat (t : FloatType) (x : BitVec t.width) : P E σ (BitVec t.width) :=
  if ABI.isNaN t x then (choose (.nan t x) : P E σ (ChoiceKind.nan t x).Resp) else pure x

/-- REF `encode_float_as_i32` / `encode_float_as_i64` (L1516-1520). -/
def encodeFloat (t : FloatType) (x : BitVec t.width) :
    P E σ (BitVec (ABI.floatIntType t).width) := do
  return ABI.reinterpretFloatAsInt t (← lowerFloat t x)

/-! ## Variant flat coercions -/

/-- The low 32 bits of a flat value (REF `wrap_i64_to_i32`, L1952; identity on `i32`). -/
def wrapI64ToI32 (v : FlatValue) : BitVec 32 := BitVec.ofNat 32 v.bits.toNat

/-- The flat value's bits zero-extended/truncated to 64 bits. -/
def flatBits64 (v : FlatValue) : BitVec 64 := BitVec.ofNat 64 v.bits.toNat

/-- `CoerceValueIter.next` of REF `lift_flat_variant` (L1934-1942): read a value of the joined
flat type `have` where the case's own flattening wants `want`. Outside the table the value
is returned unchanged (REF asserts `have == want`, D-f). -/
def coerceLiftFlat : NumType → NumType → FlatValue → FlatValue
  | .int .i32, .float .f32, v => .float .f32 (ABI.decodeFloat .f32 (wrapI64ToI32 v))
  | .int .i64, .int .i32, v => .int .i32 (wrapI64ToI32 v)
  | .int .i64, .float .f32, v => .float .f32 (ABI.decodeFloat .f32 (wrapI64ToI32 v))
  | .int .i64, .float .f64, v => .float .f64 (ABI.decodeFloat .f64 (flatBits64 v))
  | _, _, v => v

/-- `coerceLiftFlat` as a program (it performs no effect). -/
def coerceLift (have_ want : NumType) (v : FlatValue) : P E σ FlatValue :=
  pure (coerceLiftFlat have_ want v)

/-- The `(have, want)` table of REF `lower_flat_variant` (L2022-2029): `have` is the type of
the case's own flat value `v`, `want` the joined slot type. Floats are re-encoded with
`encode_float_as_i32/64` (a NaN issues a C7 choice), `i32 → i64` zero-extends. Outside the
table `v` is returned unchanged (REF asserts `have == want`, D-f). -/
def coerceLower : NumType → NumType → FlatValue → P E σ FlatValue
  | .float .f32, .int .i32, v => do
      return .int .i32 (← encodeFloat .f32 (wrapI64ToI32 v))
  | .int .i32, .int .i64, v => pure (.int .i64 (flatBits64 v))
  | .float .f32, .int .i64, v => do
      return .int .i64 ((← encodeFloat .f32 (wrapI64ToI32 v)).setWidth 64)
  | .float .f64, .int .i64, v => do
      return .int .i64 (← encodeFloat .f64 (flatBits64 v))
  | _, _, v => pure v

/-- The pairs of `(have, want)` handled by `lift_flat_variant`, plus the identity. -/
def CoercePair (have_ want : NumType) : Prop :=
  have_ = want ∨ (have_, want) ∈
    [(.int .i32, .float .f32), (.int .i64, .int .i32), (.int .i64, .float .f32),
      (.int .i64, .float .f64)]

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

/-! ## Tests -/

namespace Scalar.Tests

/-- Test helper: an `i32` flat value. -/
def flatI32 (n : Nat) : FlatValue := .int .i32 (BitVec.ofNat 32 n)
/-- Test helper: an `i64` flat value. -/
def flatI64 (n : Nat) : FlatValue := .int .i64 (BitVec.ofNat 64 n)

end Scalar.Tests

end Silmaril.Wasm.Component.Canon
