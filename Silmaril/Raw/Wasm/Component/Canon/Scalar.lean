module

public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Context
public import Silmaril.Raw.Wasm.Component.ABI.FloatChar
public import Silmaril.Raw.Wasm.Component.ABI.Scalar

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

private theorem emod_of_range (B v : Int) (hB : 0 < B) (h1 : -B ≤ v) (h2 : v < B) :
    v % (2 * B) = if 0 ≤ v then v else v + 2 * B := by
  split
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · rw [← Int.add_mul_emod_self_right v 1 (2 * B), Int.one_mul]
    exact Int.emod_eq_of_lt (by omega) (by omega)

private theorem two_pow_pred (w : Nat) (hw : 0 < w) : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Int.pow_succ]
  omega

/-- A signed in-range value survives reduction modulo `2^w` and sign interpretation. -/
theorem signInterpret_emod (w : Nat) (hw : 0 < w) (v : Int)
    (h1 : -(2 ^ (w - 1) : Int) ≤ v) (h2 : v < 2 ^ (w - 1)) :
    signInterpret w (v % 2 ^ w) = v := by
  have hB : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
  unfold signInterpret
  rw [two_pow_pred w hw]
  generalize (2 : Int) ^ (w - 1) = B at *
  rw [emod_of_range B v hB h1 h2]
  split <;> split <;> omega

/-- `signInterpret` lands in the signed range. -/
theorem signInterpret_range (w : Nat) (hw : 0 < w) (m : Int) (h0 : 0 ≤ m) (h1 : m < 2 ^ w) :
    -(2 ^ (w - 1) : Int) ≤ signInterpret w m ∧ signInterpret w m < 2 ^ (w - 1) := by
  unfold signInterpret
  rw [two_pow_pred w hw] at *
  generalize (2 : Int) ^ (w - 1) = B at *
  split <;> omega

private theorem decodeLE_intToLE (nbytes : Nat) (v : Int) :
    (Memory.decodeLE (intToLE nbytes v) : Int) = v % 2 ^ (8 * nbytes) := by
  have hpos : (0 : Int) < 2 ^ (8 * nbytes) := Int.pow_pos (by decide)
  have hn : 0 ≤ v % 2 ^ (8 * nbytes) := Int.emod_nonneg _ (by omega)
  have hlt : v % 2 ^ (8 * nbytes) < 2 ^ (8 * nbytes) := Int.emod_lt_of_pos _ hpos
  unfold intToLE
  rw [Memory.decodeLE_encodeLE, show (256 : Nat) ^ nbytes = 2 ^ (8 * nbytes) by
    rw [Nat.pow_mul]]
  have hlt' : (v % 2 ^ (8 * nbytes)).toNat < 2 ^ (8 * nbytes) :=
    (Int.toNat_lt hn).2 (by exact_mod_cast hlt)
  rw [Nat.mod_eq_of_lt hlt', Int.toNat_of_nonneg hn]

/-- `load_int ∘ store_int` for an unsigned in-range value. -/
theorem intOfLE_intToLE_unsigned (nbytes : Nat) (v : Int) (h0 : 0 ≤ v)
    (h1 : v < 2 ^ (8 * nbytes)) : intOfLE false (intToLE nbytes v) = v := by
  simp only [intOfLE, Bool.false_eq_true, ite_false]
  rw [decodeLE_intToLE]
  exact Int.emod_eq_of_lt h0 h1

/-- `load_int ∘ store_int` for a signed in-range value. -/
theorem intOfLE_intToLE_signed (nbytes : Nat) (hn : 0 < nbytes) (v : Int)
    (h0 : -(2 ^ (8 * nbytes - 1) : Int) ≤ v) (h1 : v < 2 ^ (8 * nbytes - 1)) :
    intOfLE true (intToLE nbytes v) = v := by
  simp only [intOfLE, ite_true, intToLE, Memory.encodeLE_size]
  rw [← intToLE, decodeLE_intToLE]
  exact signInterpret_emod _ (by omega) v h0 h1

/-! ## Booleans -/

/-! ## Chars -/

/-! ## Integers in flat form -/

private theorem width_pos (k : IntKind) : 0 < k.width := by cases k <;> decide

private theorem width_le (k : IntKind) : k.width ≤ (intKindCore k).width := by
  cases k <;> decide

/-- Lifting a lowered in-range integer gives it back. -/
theorem liftFlatInt_lowerFlatInt (k : IntKind) (n : Int) (h : k.inRange n = true) :
    liftFlatInt k (lowerFlatInt k n) = n := by
  have hdvd : (2 : Int) ^ k.width ∣ 2 ^ (intKindCore k).width :=
    pow_dvd_pow 2 (width_le k)
  have hW : (0 : Int) < 2 ^ (intKindCore k).width := Int.pow_pos (by decide)
  have hm : ((lowerFlatInt k n).bits.toNat : Int) % 2 ^ k.width = n % 2 ^ k.width := by
    change ((BitVec.ofInt (intKindCore k).width n).toNat : Int) % _ = _
    rw [BitVec.toNat_ofInt]
    push_cast
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hW.ne'), Int.emod_emod_of_dvd _ hdvd]
  simp only [IntKind.inRange, IntKind.minValue, IntKind.bound, Bool.and_eq_true] at h
  unfold liftFlatInt
  simp only [hm]
  split
  · rename_i hs
    simp only [hs, ite_true, decide_eq_true_eq] at h
    exact signInterpret_emod _ (width_pos k) n h.1 h.2
  · rename_i hs
    simp only [hs, Bool.false_eq_true, ite_false, decide_eq_true_eq] at h
    exact Int.emod_eq_of_lt h.1 h.2

/-- Every lifted flat integer is in range for its kind. -/
theorem liftFlatInt_inRange (k : IntKind) (v : FlatValue) :
    k.inRange (liftFlatInt k v) = true := by
  have hpos : (0 : Int) < 2 ^ k.width := Int.pow_pos (by decide)
  have h0 : 0 ≤ (v.bits.toNat : Int) % 2 ^ k.width := Int.emod_nonneg _ (by omega)
  have h1 : (v.bits.toNat : Int) % 2 ^ k.width < 2 ^ k.width := Int.emod_lt_of_pos _ hpos
  simp only [IntKind.inRange, IntKind.minValue, IntKind.bound, Bool.and_eq_true, liftFlatInt]
  split
  · simp only [decide_eq_true_eq]
    exact signInterpret_range _ (width_pos k) _ h0 h1
  · simp only [decide_eq_true_eq]
    exact ⟨h0, h1⟩

/-! ## Floats -/

theorem lowerFloat_of_not_isNaN {t : FloatType} {x : BitVec t.width}
    (h : ABI.isNaN t x = false) : (lowerFloat t x : P E σ _) = pure x := by
  simp only [lowerFloat, h, Bool.false_eq_true, ite_false]

theorem lowerFloat_of_isNaN {t : FloatType} {x : BitVec t.width}
    (h : ABI.isNaN t x = true) :
    (lowerFloat t x : P E σ _) = (choose (.nan t x) : P E σ (ChoiceKind.nan t x).Resp) := by
  simp only [lowerFloat, h, ite_true]

/-! ## Variant flat coercions -/

theorem coerceLiftFlat_self (t : NumType) (v : FlatValue) : coerceLiftFlat t t v = v := by
  rcases t with (_ | _) | (_ | _) <;> rfl

/-- A coerced value has the wanted type. -/
theorem coerceLiftFlat_type {have_ want : NumType} {v : FlatValue} (hv : v.type = have_)
    (h : CoercePair have_ want) : (coerceLiftFlat have_ want v).type = want := by
  rcases h with rfl | h
  · rw [coerceLiftFlat_self]; exact hv
  · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

theorem coerceLift (have_ want : NumType) (v : FlatValue) :
    P.Inv I (Canon.coerceLift have_ want v : P E σ FlatValue) := pure _

end P.Inv

/-! ## Tests -/

namespace Scalar.Tests

/-- `lift_flat_unsigned`: u8 lift of 256 is 0 (high bits silently truncated). -/
theorem liftFlatInt_u8_256 : liftFlatInt .u8 (flatI32 256) = 0 := by decide

/-- u8 lift of `0xFFFFFFFF` is 255. -/
theorem liftFlatInt_u8_max : liftFlatInt .u8 (flatI32 0xFFFFFFFF) = 255 := by decide

/-- `lift_flat_signed`: s8 lift of 128 is -128. -/
theorem liftFlatInt_s8_128 : liftFlatInt .s8 (flatI32 128) = -128 := by decide

/-- s64 lift of `2^64 - 1` is -1. -/
theorem liftFlatInt_s64_max : liftFlatInt .s64 (flatI64 (2 ^ 64 - 1)) = -1 := by decide

/-- s32 lowering adds `2^32` to a negative value. -/
theorem lowerFlatInt_s32_neg : lowerFlatInt .s32 (-1) = flatI32 0xFFFFFFFF := by decide

/-- `convert_int_to_bool`: bool lift of 2 is `true`. -/
theorem liftFlatBool_two : liftFlatBool (flatI32 2) = true := by decide

/-- `convert_i32_to_char` traps on the surrogate `0xD800`. -/
theorem convertI32ToChar_surrogate :
    (convertI32ToChar 0xD800#32 : P E σ Char) = trap .invalidChar := rfl

/-- `convert_i32_to_char` traps on `0x110000`. -/
theorem convertI32ToChar_tooBig :
    (convertI32ToChar 0x110000#32 : P E σ Char) = trap .invalidChar := rfl

/-- `convert_i32_to_char` accepts `'a'`. -/
theorem convertI32ToChar_a : (convertI32ToChar 0x61#32 : P E σ Char) = pure 'a' := rfl

/-- Little-endian `store_int`/`load_int` of s16 `-2`. -/
theorem intToLE_s16_neg : (intToLE 2 (-2)).data = #[0xFE, 0xFF] := by decide

theorem intOfLE_s16_neg : intOfLE true (intToLE 2 (-2)) = -2 := by decide

/-- `(i64, i32)`: `wrap_i64_to_i32`. -/
theorem coerceLiftFlat_wrap :
    coerceLiftFlat (.int .i64) (.int .i32) (flatI64 0x100000005) = flatI32 5 := by decide

/-- `(i32, f32)`: reinterpret plus NaN canonicalization. -/
theorem coerceLiftFlat_nan :
    coerceLiftFlat (.int .i32) (.float .f32) (flatI32 0x7fc00001) =
      .float .f32 (ABI.canonicalNaN .f32) := by decide

/-- `(i64, f64)`: a non-NaN is reinterpreted unchanged. -/
theorem coerceLiftFlat_f64 :
    coerceLiftFlat (.int .i64) (.float .f64) (flatI64 0x3ff0000000000000) =
      .float .f64 0x3ff0000000000000#64 := by decide

/-- `(i32, i64)` lowering zero-extends. -/
theorem coerceLower_zext :
    (coerceLower (.int .i32) (.int .i64) (flatI32 0xFFFFFFFF) : P E σ FlatValue) =
      pure (flatI64 0xFFFFFFFF) := rfl

/-- `(f32, i32)` lowering of a non-NaN (`1.0f`) makes no choice. -/
theorem coerceLower_f32_one :
    (coerceLower (.float .f32) (.int .i32) (.float .f32 0x3f800000#32) : P E σ FlatValue) =
      pure (flatI32 0x3f800000) := rfl

end Scalar.Tests

end Silmaril.Wasm.Component.Canon
