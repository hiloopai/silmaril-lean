module

public import Silmaril.Wasm.Component.Reference.ABI.FloatChar.Properties.Defs

public import Silmaril.Raw.Wasm.Component.ABI.FloatChar
public import Silmaril.Wasm.Numerics.Float

/-!
# Properties of canonical floats and chars

Theorems about `ABI.FloatChar`:

* `isNaN` agrees with `Silmaril.Numeric.Ieee754` classification (`isNaN_f32_iff`,
  `isNaN_f64_iff`).
* NaN canonicalization is idempotent. A lifted float is either the unchanged non-NaN
  input or the canonical NaN.
* `ScrambleNaN` preserves NaN-ness and non-NaN bits. It always admits the
  deterministic choice `canonicalizeNaN`. It is functional in the deterministic
  profile. In the nondeterministic profile it contains every image of the Python
  `random_nan_bits`, and it admits wasmtime's bit-preserving pass-through after a lift.
* Flat and memory float round trips hold up to NaN canonicalization, and exactly for
  raw bits.
* Char round trips are exact. `convertI32ToChar?` traps exactly on non-scalar values,
  and wasmtime's FACT char check agrees with it on all 2^32 inputs. The proof uses
  bit-field arithmetic, not `bv_decide`, which at this toolchain adds a
  `_native.bv_decide` axiom.
* Concrete checks follow the reference constants and trap boundaries.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

open Silmaril.Wasm.Execution
open Silmaril.Numeric.Ieee754

/-! ## NaN predicate -/

private theorem extractLsb'_eq_allOnes_iff {w : Nat} (x : BitVec w) (s n : Nat) :
    x.extractLsb' s n = BitVec.allOnes n ↔ x.toNat / 2 ^ s % 2 ^ n = 2 ^ n - 1 := by
  rw [← BitVec.toNat_inj, BitVec.extractLsb'_toNat, BitVec.toNat_allOnes,
    Nat.shiftRight_eq_div_pow]

private theorem extractLsb'_zero_eq_zero_iff {w : Nat} (x : BitVec w) (n : Nat) :
    x.extractLsb' 0 n = 0 ↔ x.toNat % 2 ^ n = 0 := by
  rw [← BitVec.toNat_inj, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rfl

/-- `isNaN` as a proposition about the exponent and fraction fields. -/
theorem isNaN_eq_true_iff (t : FloatType) (x : BitVec t.width) :
    isNaN t x = true ↔
      x.extractLsb' (floatFractionWidth t) (floatExponentWidth t) =
        BitVec.allOnes (floatExponentWidth t) ∧
      x.extractLsb' 0 (floatFractionWidth t) ≠ 0 := by
  simp only [isNaN, BitVec.ofNat_eq_ofNat, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]

private theorem classify_eq_nan_iff (w t : Nat) (d : Decoded) (hw : 0 < w) :
    classify w t d = .nan ↔
      d.exponent = maxExponentField w ∧ d.trailingSignificand ≠ 0 := by
  have : maxExponentField w ≠ 0 := by
    unfold maxExponentField
    have := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hw)
    omega
  unfold classify
  by_cases a : d.exponent = 0 <;> by_cases b : d.exponent = maxExponentField w <;>
    by_cases c : d.trailingSignificand = 0 <;> simp_all

/-- `isNaN` agrees with the repository's IEEE-754 classification (`F32.IsNaN`). -/
theorem isNaN_f32_iff (x : Numerics.FloatValue .f32) :
    isNaN .f32 x = true ↔ (Numerics.asF32 x).IsNaN := by
  simp only [F32.IsNaN, classify32,
    classify_eq_nan_iff _ _ _ (by decide : 0 < binary32ExponentBits)]
  refine (isNaN_eq_true_iff _ x).trans ?_
  simp only [ne_eq, extractLsb'_eq_allOnes_iff, decode32, decode, field,
    Numerics.asF32, maxExponentField, floatFractionWidth, floatExponentWidth,
    binary32ExponentBits, binary32SignificandBits, Nat.pow_zero, Nat.div_one]
  exact and_congr Iff.rfl (not_congr (extractLsb'_zero_eq_zero_iff _ _))

/-- `isNaN` agrees with the repository's IEEE-754 classification (`F64.IsNaN`). -/
theorem isNaN_f64_iff (x : Numerics.FloatValue .f64) :
    isNaN .f64 x = true ↔ (Numerics.asF64 x).IsNaN := by
  simp only [F64.IsNaN, classify64,
    classify_eq_nan_iff _ _ _ (by decide : 0 < binary64ExponentBits)]
  refine (isNaN_eq_true_iff _ x).trans ?_
  simp only [ne_eq, extractLsb'_eq_allOnes_iff, decode64, decode, field,
    Numerics.asF64, maxExponentField, floatFractionWidth, floatExponentWidth,
    binary64ExponentBits, binary64SignificandBits, Nat.pow_zero, Nat.div_one]
  exact and_congr Iff.rfl (not_congr (extractLsb'_zero_eq_zero_iff _ _))

/-! ## NaN canonicalization -/

/-- Canonicalization leaves non-NaN bits unchanged and sends every NaN to the
canonical NaN. -/
theorem canonicalizeNaN_cases (t : FloatType) (x : BitVec t.width) :
    (isNaN t x = false ∧ canonicalizeNaN t x = x) ∨
      (isNaN t x = true ∧ canonicalizeNaN t x = canonicalNaN t) := by
  cases h : isNaN t x
  · exact .inl ⟨rfl, canonicalizeNaN_of_not_isNaN h⟩
  · exact .inr ⟨rfl, canonicalizeNaN_of_isNaN h⟩

theorem isCanonicalFloat_canonicalizeNaN (t : FloatType) (x : BitVec t.width) :
    IsCanonicalFloat t (canonicalizeNaN t x) := by
  intro h
  rw [isNaN_canonicalizeNaN] at h
  exact canonicalizeNaN_of_isNaN h

theorem canonicalizeNaN_eq_self_iff (t : FloatType) (x : BitVec t.width) :
    canonicalizeNaN t x = x ↔ IsCanonicalFloat t x := by
  constructor
  · intro h
    rw [← h]
    exact isCanonicalFloat_canonicalizeNaN t x
  · intro h
    cases hn : isNaN t x
    · exact canonicalizeNaN_of_not_isNaN hn
    · rw [canonicalizeNaN_of_isNaN hn, h hn]

/-! ## Reinterpretation and decoding -/

/-- Every decoded float is a component-level float (at most one NaN pattern). -/
theorem decodeFloat_canonical (t : FloatType) (i : BitVec (floatIntType t).width) :
    IsCanonicalFloat t (decodeFloat t i) :=
  isCanonicalFloat_canonicalizeNaN t _

/-- `decode_i32_as_float`: non-NaN bit patterns are unchanged; NaNs become canonical. -/
theorem decodeFloat_cases (t : FloatType) (i : BitVec (floatIntType t).width) :
    (isNaN t (reinterpretIntAsFloat t i) = false ∧
        decodeFloat t i = reinterpretIntAsFloat t i) ∨
      (isNaN t (reinterpretIntAsFloat t i) = true ∧ decodeFloat t i = canonicalNaN t) :=
  canonicalizeNaN_cases t _

/-! ## NaN scrambling -/

/-- Scrambling is invisible after canonicalization: lifting a lowered float gives
the canonicalization of the original, in both profiles. -/
theorem ScrambleNaN.canonicalizeNaN_eq {d : Bool} {t : FloatType} {x y : BitVec t.width}
    (h : ScrambleNaN d t x y) : canonicalizeNaN t y = canonicalizeNaN t x := by
  cases hn : isNaN t x
  · rw [h.eq_of_not_isNaN hn]
  · have hy : isNaN t y = true := h.isNaN_eq.trans hn
    rw [canonicalizeNaN_of_isNaN hn, canonicalizeNaN_of_isNaN hy]

/-- wasmtime's host and FACT paths return the original float bits. After a lift,
this is an admitted nondeterministic lowering (the original is a NaN whenever the
lifted value is). -/
theorem scrambleNaN_canonicalizeNaN_self (t : FloatType) (x : BitVec t.width) :
    ScrambleNaN false t (canonicalizeNaN t x) x := by
  rw [scrambleNaN_false_iff, isNaN_canonicalizeNaN]
  cases hn : isNaN t x
  · exact .inl ⟨rfl, (canonicalizeNaN_of_not_isNaN hn).symm⟩
  · exact .inr ⟨rfl, rfl⟩

/-- Every output of Python `random_nan_bits` is a NaN. -/
theorem RandomNaNBits.isNaN_eq_true {t : FloatType} {y : BitVec t.width} (h : RandomNaNBits t y) :
    isNaN t y = true := by
  obtain ⟨exponent, i, hi, bit⟩ := h
  unfold isNaN
  rw [exponent, beq_self_eq_true, Bool.true_and, bne_iff_ne]
  intro zero
  have := congrArg (fun z => z.getLsbD i) zero
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, BitVec.ofNat_eq_ofNat,
    BitVec.getLsbD_zero] at this
  simp only [show i < floatFractionWidth t by omega, decide_true, Bool.true_and, bit] at this
  contradiction

/-- `random_nan_bits` values are admitted by the nondeterministic relation. -/
theorem scrambleNaN_of_randomNaNBits {t : FloatType} {x y : BitVec t.width}
    (nan : isNaN t x = true) (h : RandomNaNBits t y) : ScrambleNaN false t x y :=
  .scrambled x y nan rfl h.isNaN_eq_true

/-- The canonical NaN is *not* in the image of Python `random_nan_bits`: the reference
nondeterministic generator is strictly narrower than the prose-permitted relation. -/
theorem not_randomNaNBits_canonicalNaN (t : FloatType) : ¬ RandomNaNBits t (canonicalNaN t) := by
  rintro ⟨-, i, hi, bit⟩
  cases t
  · have hi' : i < 22 := by simp only [floatFractionWidth] at hi; omega
    clear hi; revert bit; revert hi'; revert i; decide
  · have hi' : i < 51 := by simp only [floatFractionWidth] at hi; omega
    clear hi; revert bit; revert hi'; revert i; decide

theorem scrambleNaNWith_spec (t : FloatType) (pick x : BitVec t.width)
    (pickNaN : isNaN t pick = true) : ScrambleNaN false t x (scrambleNaNWith t pick x) := by
  unfold scrambleNaNWith
  cases hn : isNaN t x
  · exact .nonNaN x hn
  · exact .scrambled x pick hn rfl pickNaN

theorem EncodeFloat.decodeFloat {d : Bool} {t : FloatType} {x : BitVec t.width}
    {i : BitVec (floatIntType t).width} (h : EncodeFloat d t x i) :
    ABI.decodeFloat t i = canonicalizeNaN t x := by
  obtain ⟨y, scramble, rfl⟩ := h
  simp only [ABI.decodeFloat, reinterpretIntAsFloat_reinterpretFloatAsInt,
    scramble.canonicalizeNaN_eq]

/-! ## Flat float adapters -/

/-- A lifted flat float is either the unchanged non-NaN core value or the canonical
NaN. -/
theorem liftFloatFlat_cases (t : FloatType) (x : BitVec t.width) :
    (isNaN t x = false ∧ liftFloatFlat t (.float t x) = some x) ∨
      (isNaN t x = true ∧ liftFloatFlat t (.float t x) = some (canonicalNaN t)) := by
  rw [liftFloatFlat_float]
  rcases canonicalizeNaN_cases t x with ⟨hn, he⟩ | ⟨hn, he⟩
  · exact .inl ⟨hn, by rw [he]⟩
  · exact .inr ⟨hn, by rw [he]⟩

theorem liftFloatFlat_canonical {t : FloatType} {v : Runtime.Value} {x : BitVec t.width}
    (h : liftFloatFlat t v = some x) : IsCanonicalFloat t x := by
  unfold liftFloatFlat at h
  split at h
  · cases h
    exact isCanonicalFloat_canonicalizeNaN t _
  · contradiction

theorem lowerFloatFlatCanonical_spec (d : Bool) (t : FloatType) (x : BitVec t.width) :
    LowerFloatFlat d t x (lowerFloatFlatCanonical t x) :=
  ⟨_, scrambleNaN_canonicalizeNaN d t x, rfl⟩

/-- Lifting any admitted lowering yields the canonicalized original, in both profiles. -/
theorem liftFloatFlat_of_lowerFloatFlat {d : Bool} {t : FloatType} {x : BitVec t.width}
    {v : Runtime.Value} (h : LowerFloatFlat d t x v) :
    liftFloatFlat t v = some (canonicalizeNaN t x) := by
  obtain ⟨y, scramble, rfl⟩ := h
  rw [liftFloatFlat_float, scramble.canonicalizeNaN_eq]

/-- Flat round trip for component-level floats. -/
theorem liftFloatFlat_of_lowerFloatFlat_canonical {d : Bool} {t : FloatType}
    {x : BitVec t.width} {v : Runtime.Value} (canonical : IsCanonicalFloat t x)
    (h : LowerFloatFlat d t x v) : liftFloatFlat t v = some x := by
  rw [liftFloatFlat_of_lowerFloatFlat h, (canonicalizeNaN_eq_self_iff t x).mpr canonical]

/-! ## Float memory -/

/-- Little-endian raw float bits round-trip through memory. -/
theorem loadFloatBits_storeFloatBits (t : FloatType) (memory after : ByteArray) (start : Nat)
    (x : BitVec t.width) (h : storeFloatBits t memory start x = some after) :
    loadFloatBits t after start = some x := by
  unfold loadFloatBits
  rw [Memory.load_store memory after start _ _ h]
  simp only [Option.map_some, BitVec.cast_cast, BitVec.cast_eq]

theorem storeFloatBits_size (t : FloatType) (memory after : ByteArray) (start : Nat)
    (x : BitVec t.width) (h : storeFloatBits t memory start x = some after) :
    after.size = memory.size :=
  Memory.writeBytes_size memory _ after start h

/-- Loading after any admitted store gives the canonicalized original. -/
theorem loadFloat_of_storeFloat {d : Bool} {t : FloatType} {memory after : ByteArray}
    {start : Nat} {x : BitVec t.width} (h : StoreFloat d t memory start x (some after)) :
    loadFloat t after start = some (canonicalizeNaN t x) := by
  obtain ⟨y, scramble, stored⟩ := h
  unfold loadFloat
  rw [loadFloatBits_storeFloatBits t memory after start y stored.symm, Option.map_some,
    scramble.canonicalizeNaN_eq]

theorem storeFloatCanonical_spec (d : Bool) (t : FloatType) (memory : ByteArray) (start : Nat)
    (x : BitVec t.width) :
    StoreFloat d t memory start x (storeFloatCanonical t memory start x) :=
  ⟨_, scrambleNaN_canonicalizeNaN d t x, rfl⟩

/-- `StoreFloat` factors through `EncodeFloat` exactly as the reference `store` does:
`store_int(cx, encode_float_as_i32(v), ptr, 4)` (and the `f64` analogue), i.e. an admitted
float store is an integer store of an admitted encoding. -/
theorem storeFloat_iff_encodeFloat (d : Bool) (t : FloatType) (memory : ByteArray)
    (start : Nat) (x : BitVec t.width) (after : Option ByteArray) :
    StoreFloat d t memory start x after ↔
      ∃ i, EncodeFloat d t x i ∧
        after = storeFloatBits t memory start (reinterpretIntAsFloat t i) := by
  constructor
  · rintro ⟨y, scramble, rfl⟩
    exact ⟨reinterpretFloatAsInt t y, ⟨y, scramble, rfl⟩,
      by rw [reinterpretIntAsFloat_reinterpretFloatAsInt]⟩
  · rintro ⟨i, ⟨y, scramble, rfl⟩, rfl⟩
    exact ⟨y, scramble, by rw [reinterpretIntAsFloat_reinterpretFloatAsInt]⟩

/-- Store failure (out of bounds) does not depend on the NaN choice. -/
theorem storeFloatBits_isSome (t : FloatType) (memory : ByteArray) (start : Nat)
    (x y : BitVec t.width) :
    (storeFloatBits t memory start x).isSome = (storeFloatBits t memory start y).isSome := by
  simp only [storeFloatBits, Memory.store, Memory.writeBytes, Memory.encodeLE_size]
  split <;> rfl

/-! ## Chars -/

theorem convertI32ToChar?_eq_none_iff (i : BitVec 32) :
    convertI32ToChar? i = none ↔
      0x110000 ≤ i.toNat ∨ (0xD800 ≤ i.toNat ∧ i.toNat ≤ 0xDFFF) := by
  unfold convertI32ToChar?
  split
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    unfold IsUnicodeScalar at h
    omega
  · rename_i h
    simp only [true_iff]
    unfold IsUnicodeScalar at h
    omega

theorem charToI32_toNat (c : Char) : (charToI32 c).toNat = c.toNat := rfl

theorem charToI32_of_convertI32ToChar? {i : BitVec 32} {c : Char}
    (h : convertI32ToChar? i = some c) : charToI32 c = i := by
  rcases convertI32ToChar?_spec i with ⟨-, hn⟩ | ⟨-, c', hc, hv⟩
  · rw [hn] at h; contradiction
  · rw [hc] at h
    cases h
    apply BitVec.eq_of_toNat_eq
    rw [charToI32_toNat, hv]

theorem liftCharFlat_lowerCharFlat (c : Char) : liftCharFlat (lowerCharFlat c) = some c := by
  simp only [lowerCharFlat, liftCharFlat_int, convertI32ToChar?_charToI32]

theorem loadChar_storeChar (memory after : ByteArray) (start : Nat) (c : Char)
    (h : storeChar memory start c = some after) : loadChar after start = some c := by
  unfold loadChar
  rw [Memory.load_store memory after start 4 _ h, Option.bind_some,
    convertI32ToChar?_charToI32]

theorem storeChar_size (memory after : ByteArray) (start : Nat) (c : Char)
    (h : storeChar memory start c = some after) : after.size = memory.size :=
  Memory.writeBytes_size memory _ after start h

/-- wasmtime's inline FACT char check accepts exactly the Unicode scalar values. -/
theorem wasmtimeCharCheck_iff (x : BitVec 32) :
    wasmtimeCharCheck x = true ↔ IsUnicodeScalar x.toNat := by
  have hi : (x.toNat ^^^ 55296) / 2 ^ 16 = x.toNat / 2 ^ 16 := by
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib]
    simp only [Nat.reduceShiftRight, Nat.xor_zero]
  have lo : (x.toNat ^^^ 55296) / 2 ^ 11 = 0 ↔ x.toNat / 2 ^ 11 = 27 := by
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib]
    simp only [Nat.reduceShiftRight]
    constructor
    · intro h
      rw [← Nat.xor_zero (x.toNat >>> 11), ← Nat.xor_self 27, ← Nat.xor_assoc, h,
        Nat.zero_xor]
    · intro h
      rw [h, Nat.xor_self]
  have hy : (x ^^^ 0xd800#32).toNat = x.toNat ^^^ 55296 := BitVec.toNat_xor ..
  have c1 : (-0x110000 : BitVec 32).toNat = 4293853184 := by decide
  have c2 : (-0x10f800 : BitVec 32).toNat = 4293855232 := by decide
  have hadd : ((x ^^^ 0xd800#32) + (-0x110000 : BitVec 32)).toNat =
      ((x.toNat ^^^ 55296) + 4293853184) % 4294967296 := by
    rw [BitVec.toNat_add, hy, c1]
  have hne : (x != 0x110000#32) = true ↔ x.toNat ≠ 1114112 := by
    rw [bne_iff_ne, ne_eq, ne_eq, ← BitVec.toNat_inj]; rfl
  have bound := x.isLt
  generalize x.toNat ^^^ 55296 = m at hi lo hadd
  unfold wasmtimeCharCheck
  rw [Bool.and_eq_true, hne, Bool.not_eq_true', BitVec.ult, hadd, c2, decide_eq_false_iff_not]
  unfold IsUnicodeScalar
  omega

theorem wasmtimeCharCheck_eq_isSome (x : BitVec 32) :
    wasmtimeCharCheck x = (convertI32ToChar? x).isSome := by
  rcases convertI32ToChar?_spec x with ⟨bad, hn⟩ | ⟨good, c, hc, -⟩
  · rw [hn, Option.isSome_none, Bool.eq_false_iff, ne_eq, wasmtimeCharCheck_iff]
    exact bad
  · rw [hc, Option.isSome_some, wasmtimeCharCheck_iff]
    exact good

/-! ## Concrete checks -/

theorem canonicalNaN_f32 : canonicalNaN .f32 = 0x7fc00000#32 := rfl
theorem canonicalNaN_f64 : canonicalNaN .f64 = 0x7ff8000000000000#64 := rfl

/-- Positive signalling binary32 NaN (`0x7fa00000`) canonicalizes. -/
example : canonicalizeNaN .f32 0x7fa00000#32 = 0x7fc00000#32 := rfl
/-- Smallest-payload signalling NaN and a negative quiet NaN with payload. -/
example : canonicalizeNaN .f32 0x7f800001#32 = 0x7fc00000#32 := rfl
example : canonicalizeNaN .f32 0xffc00001#32 = 0x7fc00000#32 := rfl
/-- Infinity and `1.0` are not NaNs and pass through. -/
example : canonicalizeNaN .f32 0x7f800000#32 = 0x7f800000#32 := rfl
example : canonicalizeNaN .f32 0x3f800000#32 = 0x3f800000#32 := rfl
/-- Binary64 signalling NaN and negative canonical-payload NaN. -/
example : canonicalizeNaN .f64 0x7ff0000000000001#64 = 0x7ff8000000000000#64 := rfl
example : canonicalizeNaN .f64 0xfff8000000000000#64 = 0x7ff8000000000000#64 := rfl
example : canonicalizeNaN .f64 0xfff0000000000000#64 = 0xfff0000000000000#64 := rfl
/-- A flat lift of a signalling NaN core value. -/
example : liftFloatFlat .f32 (.float .f32 0x7f800001#32) = some 0x7fc00000#32 := rfl
example : liftFloatFlat .f64 (.int .i64 0) = none := rfl

/-- Char trap boundaries of `convert_i32_to_char`. -/
example : convertI32ToChar? 0xD800#32 = none := by decide
example : convertI32ToChar? 0xDFFF#32 = none := by decide
example : convertI32ToChar? 0x110000#32 = none := by decide
example : convertI32ToChar? 0xFFFFFFFF#32 = none := by decide
example : convertI32ToChar? 0x10FFFF#32 = some (Char.ofNat 0x10FFFF) := by decide
example : convertI32ToChar? 0xD7FF#32 = some (Char.ofNat 0xD7FF) := by decide
example : convertI32ToChar? 0xE000#32 = some (Char.ofNat 0xE000) := by decide
example : convertI32ToChar? 0x41#32 = some 'A' := by decide
example : charToI32 'A' = 0x41#32 := by decide
example : wasmtimeCharCheck 0xD800#32 = false := by decide
example : wasmtimeCharCheck 0x10FFFF#32 = true := by decide
example : wasmtimeCharCheck 0x110000#32 = false := by decide

end Silmaril.Wasm.Component.ABI
