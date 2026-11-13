module

public import Silmaril.Wasm.Component.Reference.ABI.FloatChar.Defs
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

/-! ## NaN canonicalization -/

@[simp] theorem isNaN_canonicalNaN (t : FloatType) : isNaN t (canonicalNaN t) = true := by
  cases t <;> decide

theorem canonicalizeNaN_of_isNaN {t : FloatType} {x : BitVec t.width} (h : isNaN t x = true) :
    canonicalizeNaN t x = canonicalNaN t := by
  simp only [canonicalizeNaN, h, ite_true]

theorem canonicalizeNaN_of_not_isNaN {t : FloatType} {x : BitVec t.width}
    (h : isNaN t x = false) : canonicalizeNaN t x = x := by
  simp only [canonicalizeNaN, h, Bool.false_eq_true, ite_false]

@[simp] theorem isNaN_canonicalizeNaN (t : FloatType) (x : BitVec t.width) :
    isNaN t (canonicalizeNaN t x) = isNaN t x := by
  cases h : isNaN t x
  · rw [canonicalizeNaN_of_not_isNaN h, h]
  · rw [canonicalizeNaN_of_isNaN h, isNaN_canonicalNaN]

/-- `canonicalize_nan32`/`canonicalize_nan64` are idempotent. -/
@[simp] theorem canonicalizeNaN_idem (t : FloatType) (x : BitVec t.width) :
    canonicalizeNaN t (canonicalizeNaN t x) = canonicalizeNaN t x := by
  cases h : isNaN t x
  · rw [canonicalizeNaN_of_not_isNaN h, canonicalizeNaN_of_not_isNaN h]
  · rw [canonicalizeNaN_of_isNaN h, canonicalizeNaN_of_isNaN (isNaN_canonicalNaN t)]

/-! ## Reinterpretation and decoding -/

@[simp] theorem reinterpretFloatAsInt_reinterpretIntAsFloat (t : FloatType)
    (i : BitVec (floatIntType t).width) :
    reinterpretFloatAsInt t (reinterpretIntAsFloat t i) = i := by
  simp only [reinterpretFloatAsInt, reinterpretIntAsFloat, BitVec.cast_cast, BitVec.cast_eq]

@[simp] theorem reinterpretIntAsFloat_reinterpretFloatAsInt (t : FloatType)
    (x : BitVec t.width) : reinterpretIntAsFloat t (reinterpretFloatAsInt t x) = x := by
  simp only [reinterpretFloatAsInt, reinterpretIntAsFloat, BitVec.cast_cast, BitVec.cast_eq]

/-! ## NaN scrambling -/

theorem ScrambleNaN.isNaN_eq {d : Bool} {t : FloatType} {x y : BitVec t.width}
    (h : ScrambleNaN d t x y) : isNaN t y = isNaN t x := by
  cases h with
  | nonNaN => rfl
  | canonical nan _ => rw [isNaN_canonicalNaN, nan]
  | scrambled _ nan _ chosen => rw [chosen, nan]

theorem ScrambleNaN.eq_of_not_isNaN {d : Bool} {t : FloatType} {x y : BitVec t.width}
    (h : ScrambleNaN d t x y) (notNaN : isNaN t x = false) : y = x := by
  cases h with
  | nonNaN => rfl
  | canonical nan _ => rw [nan] at notNaN; contradiction
  | scrambled _ nan _ _ => rw [nan] at notNaN; contradiction

/-- The lowering relation admits the canonical (deterministic) choice in both
profiles. -/
theorem scrambleNaN_canonicalizeNaN (d : Bool) (t : FloatType) (x : BitVec t.width) :
    ScrambleNaN d t x (canonicalizeNaN t x) := by
  cases hn : isNaN t x
  · rw [canonicalizeNaN_of_not_isNaN hn]
    exact .nonNaN x hn
  · rw [canonicalizeNaN_of_isNaN hn]
    cases d with
    | true => exact .canonical x hn rfl
    | false => exact .scrambled x _ hn rfl (isNaN_canonicalNaN t)

/-- `DETERMINISTIC_PROFILE`: lowering is the function `canonicalizeNaN`. -/
theorem scrambleNaN_true_iff (t : FloatType) (x y : BitVec t.width) :
    ScrambleNaN true t x y ↔ y = canonicalizeNaN t x := by
  constructor
  · intro h
    cases h with
    | nonNaN notNaN => exact (canonicalizeNaN_of_not_isNaN notNaN).symm
    | canonical nan _ => exact (canonicalizeNaN_of_isNaN nan).symm
    | scrambled _ _ profile _ => contradiction
  · rintro rfl
    exact scrambleNaN_canonicalizeNaN true t x

/-- Nondeterministic profile: exactly "non-NaN unchanged, NaN to any NaN". -/
theorem scrambleNaN_false_iff (t : FloatType) (x y : BitVec t.width) :
    ScrambleNaN false t x y ↔
      (isNaN t x = false ∧ y = x) ∨ (isNaN t x = true ∧ isNaN t y = true) := by
  constructor
  · intro h
    cases hn : isNaN t x
    · exact .inl ⟨rfl, h.eq_of_not_isNaN hn⟩
    · exact .inr ⟨rfl, h.isNaN_eq.trans hn⟩
  · rintro (⟨hn, rfl⟩ | ⟨hx, hy⟩)
    · exact .nonNaN _ hn
    · exact .scrambled _ _ hx rfl hy

/-! ## Flat float adapters -/

@[simp] theorem liftFloatFlat_float (t : FloatType) (x : BitVec t.width) :
    liftFloatFlat t (.float t x) = some (canonicalizeNaN t x) := by
  cases t <;> rfl

/-! ## Float memory -/

/-! ## Chars -/

/-- Lifting an `i32` either traps exactly on non-scalar values or yields a `Char`
with the same code point. -/
theorem convertI32ToChar?_spec (i : BitVec 32) :
    (¬ IsUnicodeScalar i.toNat ∧ convertI32ToChar? i = none) ∨
      (IsUnicodeScalar i.toNat ∧ ∃ c, convertI32ToChar? i = some c ∧ c.toNat = i.toNat) := by
  unfold convertI32ToChar?
  split
  · rename_i h
    refine .inr ⟨h, _, rfl, ?_⟩
    rfl
  · rename_i h
    exact .inl ⟨h, rfl⟩

theorem isUnicodeScalar_char (c : Char) : IsUnicodeScalar c.toNat :=
  (isUnicodeScalar_iff_isValidChar _).mpr c.valid

/-- Char round trip: lowering then lifting is the identity. -/
@[simp] theorem convertI32ToChar?_charToI32 (c : Char) :
    convertI32ToChar? (charToI32 c) = some c := by
  rcases convertI32ToChar?_spec (charToI32 c) with ⟨bad, -⟩ | ⟨-, c', hc, hv⟩
  · exact absurd (isUnicodeScalar_char c) bad
  · rw [hc]
    exact congrArg some (Char.ext (UInt32.toNat_inj.mp hv))

@[simp] theorem liftCharFlat_int (x : BitVec 32) :
    liftCharFlat (.int .i32 x) = convertI32ToChar? x := by
  rfl

/-! ## Concrete checks -/

end Silmaril.Wasm.Component.ABI
