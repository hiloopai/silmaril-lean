module

public import Silmaril.Wasm.Det.NaN.Defs
public import Silmaril.Numeric.Ieee754.EncodingCorrectness

/-!
# Float operators do not see NaN payloads (proofs)

silmaril-lean's float model `F32.model` (Lean's `Float32.Model.ofBits`) canonicalises NaN
payloads, so two encodings that are both NaN have the same model (`model_nan32`). Every scalar
float operator of the fragment depends on its operands only through the model or through an
`isNaN` test, so it gives the same deterministic result on operands that are equal or both NaN
(`binOp32_congr`, `unOp32_congr`, `relOp32_congr`, and the `f64` versions). The result sets of
the specification (`floatBinOpRel`, `floatUnOpRel`, `convertRel`) contain only NaNs when the
deterministic result is a NaN, and only that result otherwise; so every allowed result has the
canonical image of the deterministic one (`canon_floatBinOpP`, `canon_floatUnOpP`,
`convertP_canon`). `neg` and `abs` are exact bit operations that keep NaNs NaNs
(`isNaN_neg32`, `isNaN_abs32`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NaN

open Silmaril.Wasm Silmaril.Numeric.Ieee754 Float.Model
open Silmaril.Wasm.Numerics (Profile asF32 asF64 floatBinOp floatUnOp floatRelOp floatBinOpP
  floatUnOpP floatBinOpRel floatUnOpRel convertP convertRel convert)
open Silmaril.Wasm.Det.NaN

/-! ## The model forgets NaN payloads -/

theorem model32_ext {a b : Float32.Model} (h : a.toBits = b.toBits) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem model64_ext {a b : Float.Model} (h : a.toBits = b.toBits) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- **Every `f32` NaN has the model's NaN.** -/
theorem model_nan32 {x : F32} (hx : x.IsNaN) : x.model = Float32.Model.nan := by
  apply model32_ext
  by_cases hC : UnpackedFloat.unpackExponent (spec := .binary32) x.bits.toBitVec = -1#_ ∧
      UnpackedFloat.unpackMantissa (spec := .binary32) x.bits.toBitVec ≠ 0#_
  · apply UInt32.eq_of_toBitVec_eq
    have h₁ : x.model.toBits.toBitVec = UnpackedFloat.packedNaN .binary32 := by
      change UnpackedFloat.pack .binary32 (UnpackedFloat.unpack .binary32 x.bits.toBitVec) = _
      rw [Conformance.pack_unpack]; exact ite_eq_left hC
    rw [h₁]
    decide
  · have h₁ : x.model.toBits = x.bits := by
      apply UInt32.eq_of_toBitVec_eq
      change UnpackedFloat.pack .binary32 (UnpackedFloat.unpack .binary32 x.bits.toBitVec) = _
      rw [Conformance.pack_unpack]; exact ite_eq_right hC
    have h₂ : F32.ofModel x.model = x := by
      show (⟨x.model.toBits⟩ : F32) = x
      rw [h₁]
    have h₃ : (F32.ofModel x.model).IsNaN := by rw [h₂]; exact hx
    have h₄ : F32.ofModel x.model = F32.canonicalNaN := F32.ofModel_nan_eq _ h₃
    exact congrArg F32.bits h₄

/-- **Every `f64` NaN has the model's NaN.** -/
theorem model_nan64 {x : F64} (hx : x.IsNaN) : x.model = Float.Model.nan := by
  apply model64_ext
  by_cases hC : UnpackedFloat.unpackExponent (spec := .binary64) x.bits.toBitVec = -1#_ ∧
      UnpackedFloat.unpackMantissa (spec := .binary64) x.bits.toBitVec ≠ 0#_
  · apply UInt64.eq_of_toBitVec_eq
    have h₁ : x.model.toBits.toBitVec = UnpackedFloat.packedNaN .binary64 := by
      change UnpackedFloat.pack .binary64 (UnpackedFloat.unpack .binary64 x.bits.toBitVec) = _
      rw [Conformance.pack_unpack]; exact ite_eq_left hC
    rw [h₁]
    decide
  · have h₁ : x.model.toBits = x.bits := by
      apply UInt64.eq_of_toBitVec_eq
      change UnpackedFloat.pack .binary64 (UnpackedFloat.unpack .binary64 x.bits.toBitVec) = _
      rw [Conformance.pack_unpack]; exact ite_eq_right hC
    have h₂ : F64.ofModel x.model = x := by
      show (⟨x.model.toBits⟩ : F64) = x
      rw [h₁]
    have h₃ : (F64.ofModel x.model).IsNaN := by rw [h₂]; exact hx
    have h₄ : F64.ofModel x.model = F64.canonicalNaN := F64.ofModel_nan_eq _ h₃
    exact congrArg F64.bits h₄


/-! ## Equal up to NaN -/

/-- `a'` is `a`, or both are NaNs. -/
def Sim32 (a a' : F32) : Prop := a' = a ∨ (a.IsNaN ∧ a'.IsNaN)

/-- `a'` is `a`, or both are NaNs. -/
def Sim64 (a a' : F64) : Prop := a' = a ∨ (a.IsNaN ∧ a'.IsNaN)

theorem Sim32.model {a a' : F32} (h : Sim32 a a') : a'.model = a.model := by
  rcases h with rfl | ⟨h₁, h₂⟩
  · rfl
  · rw [model_nan32 h₁, model_nan32 h₂]

theorem Sim64.model {a a' : F64} (h : Sim64 a a') : a'.model = a.model := by
  rcases h with rfl | ⟨h₁, h₂⟩
  · rfl
  · rw [model_nan64 h₁, model_nan64 h₂]

theorem Sim32.isNaN {a a' : F32} (h : Sim32 a a') : a'.isNaN = a.isNaN := by
  rcases h with rfl | ⟨h₁, h₂⟩
  · rfl
  · simp only [F32.isNaN, decide_eq_true h₁, decide_eq_true h₂]

theorem Sim64.isNaN {a a' : F64} (h : Sim64 a a') : a'.isNaN = a.isNaN := by
  rcases h with rfl | ⟨h₁, h₂⟩
  · rfl
  · simp only [F64.isNaN, decide_eq_true h₁, decide_eq_true h₂]

/-! ## Deterministic operators agree on operands equal up to NaN -/

theorem minimum32_congr {a a' b b' : F32} (ha : Sim32 a a') (hb : Sim32 b b') :
    F32.minimum a' b' = F32.minimum a b := by
  rcases ha with rfl | ⟨h₁, h₂⟩
  · rcases hb with rfl | ⟨h₃, h₄⟩
    · rfl
    · simp only [F32.minimum, F32.isNaN, decide_eq_true h₃, decide_eq_true h₄, Bool.or_true,
        ite_true]
  · simp only [F32.minimum, F32.isNaN, decide_eq_true h₁, decide_eq_true h₂, Bool.true_or,
      ite_true]

theorem maximum32_congr {a a' b b' : F32} (ha : Sim32 a a') (hb : Sim32 b b') :
    F32.maximum a' b' = F32.maximum a b := by
  rcases ha with rfl | ⟨h₁, h₂⟩
  · rcases hb with rfl | ⟨h₃, h₄⟩
    · rfl
    · simp only [F32.maximum, F32.isNaN, decide_eq_true h₃, decide_eq_true h₄, Bool.or_true,
        ite_true]
  · simp only [F32.maximum, F32.isNaN, decide_eq_true h₁, decide_eq_true h₂, Bool.true_or,
      ite_true]

theorem minimum64_congr {a a' b b' : F64} (ha : Sim64 a a') (hb : Sim64 b b') :
    F64.minimum a' b' = F64.minimum a b := by
  rcases ha with rfl | ⟨h₁, h₂⟩
  · rcases hb with rfl | ⟨h₃, h₄⟩
    · rfl
    · simp only [F64.minimum, F64.isNaN, decide_eq_true h₃, decide_eq_true h₄, Bool.or_true,
        ite_true]
  · simp only [F64.minimum, F64.isNaN, decide_eq_true h₁, decide_eq_true h₂, Bool.true_or,
      ite_true]

theorem maximum64_congr {a a' b b' : F64} (ha : Sim64 a a') (hb : Sim64 b b') :
    F64.maximum a' b' = F64.maximum a b := by
  rcases ha with rfl | ⟨h₁, h₂⟩
  · rcases hb with rfl | ⟨h₃, h₄⟩
    · rfl
    · simp only [F64.maximum, F64.isNaN, decide_eq_true h₃, decide_eq_true h₄, Bool.or_true,
        ite_true]
  · simp only [F64.maximum, F64.isNaN, decide_eq_true h₁, decide_eq_true h₂, Bool.true_or,
      ite_true]

/-- Binary `f32` operators other than `copysign` agree on operands equal up to NaN. -/
theorem binOp32_congr {op : Silmaril.Wasm.FloatBinOp} (hop : op ≠ .copysign) {a a' b b' : F32}
    (ha : Sim32 a a') (hb : Sim32 b b') :
    Numerics.floatBinOp32 op a' b' = Numerics.floatBinOp32 op a b := by
  cases op with
  | add => simp only [Numerics.floatBinOp32, F32.add, ha.model, hb.model]
  | sub => simp only [Numerics.floatBinOp32, F32.sub, ha.model, hb.model]
  | mul => simp only [Numerics.floatBinOp32, F32.mul, ha.model, hb.model]
  | div => simp only [Numerics.floatBinOp32, F32.div, ha.model, hb.model]
  | min => exact minimum32_congr ha hb
  | max => exact maximum32_congr ha hb
  | copysign => exact absurd rfl hop

/-- Binary `f64` operators other than `copysign` agree on operands equal up to NaN. -/
theorem binOp64_congr {op : Silmaril.Wasm.FloatBinOp} (hop : op ≠ .copysign) {a a' b b' : F64}
    (ha : Sim64 a a') (hb : Sim64 b b') :
    Numerics.floatBinOp64 op a' b' = Numerics.floatBinOp64 op a b := by
  cases op with
  | add => simp only [Numerics.floatBinOp64, F64.add, ha.model, hb.model]
  | sub => simp only [Numerics.floatBinOp64, F64.sub, ha.model, hb.model]
  | mul => simp only [Numerics.floatBinOp64, F64.mul, ha.model, hb.model]
  | div => simp only [Numerics.floatBinOp64, F64.div, ha.model, hb.model]
  | min => exact minimum64_congr ha hb
  | max => exact maximum64_congr ha hb
  | copysign => exact absurd rfl hop

/-- Unary `f32` operators other than the sign operations agree on operands equal up to NaN. -/
theorem unOp32_congr {op : Silmaril.Wasm.FloatUnOp} (hop : op ≠ .abs ∧ op ≠ .neg) {a a' : F32}
    (ha : Sim32 a a') : Numerics.floatUnOp32 op a' = Numerics.floatUnOp32 op a := by
  cases op with
  | sqrt => simp only [Numerics.floatUnOp32, F32.sqrt, ha.model]
  | ceil => simp only [Numerics.floatUnOp32, F32.ceil, F32.roundIntegral, ha.model]
  | floor => simp only [Numerics.floatUnOp32, F32.floor, F32.roundIntegral, ha.model]
  | trunc => simp only [Numerics.floatUnOp32, F32.trunc, F32.roundIntegral, ha.model]
  | nearest => simp only [Numerics.floatUnOp32, F32.nearest, F32.roundIntegral, ha.model]
  | abs => exact absurd rfl hop.1
  | neg => exact absurd rfl hop.2

/-- Unary `f64` operators other than the sign operations agree on operands equal up to NaN. -/
theorem unOp64_congr {op : Silmaril.Wasm.FloatUnOp} (hop : op ≠ .abs ∧ op ≠ .neg) {a a' : F64}
    (ha : Sim64 a a') : Numerics.floatUnOp64 op a' = Numerics.floatUnOp64 op a := by
  cases op with
  | sqrt => simp only [Numerics.floatUnOp64, F64.sqrt, ha.model]
  | ceil => simp only [Numerics.floatUnOp64, F64.ceil, F64.roundIntegral, ha.model]
  | floor => simp only [Numerics.floatUnOp64, F64.floor, F64.roundIntegral, ha.model]
  | trunc => simp only [Numerics.floatUnOp64, F64.trunc, F64.roundIntegral, ha.model]
  | nearest => simp only [Numerics.floatUnOp64, F64.nearest, F64.roundIntegral, ha.model]
  | abs => exact absurd rfl hop.1
  | neg => exact absurd rfl hop.2

/-- `f32` comparisons agree on operands equal up to NaN. -/
theorem relOp32_congr (op : Silmaril.Wasm.FloatRelOp) {a a' b b' : F32} (ha : Sim32 a a')
    (hb : Sim32 b b') : Numerics.floatRelOp32 op a' b' = Numerics.floatRelOp32 op a b := by
  cases op <;> simp only [Numerics.floatRelOp32, F32.equal, F32.notEqual, F32.lessThan,
    F32.lessEqual, F32.greaterThan, F32.greaterEqual, ha.model, hb.model]

/-- `f64` comparisons agree on operands equal up to NaN. -/
theorem relOp64_congr (op : Silmaril.Wasm.FloatRelOp) {a a' b b' : F64} (ha : Sim64 a a')
    (hb : Sim64 b b') : Numerics.floatRelOp64 op a' b' = Numerics.floatRelOp64 op a b := by
  cases op <;> simp only [Numerics.floatRelOp64, F64.equal, F64.notEqual, F64.lessThan,
    F64.lessEqual, F64.greaterThan, F64.greaterEqual, ha.model, hb.model]


/-! ## Sign operations keep NaNs -/

theorem classify32_congr {n m : Nat} (h : n % 2 ^ 31 = m % 2 ^ 31) :
    classify32 n = classify32 m := by
  have he : n / 2 ^ 23 % 2 ^ 8 = m / 2 ^ 23 % 2 ^ 8 := by omega
  have ht : n / 2 ^ 0 % 2 ^ 23 = m / 2 ^ 0 % 2 ^ 23 := by omega
  simp only [classify32, classify, decode32, decode, field, binary32ExponentBits,
    binary32SignificandBits, he, ht]
  rfl

theorem classify64_congr {n m : Nat} (h : n % 2 ^ 63 = m % 2 ^ 63) :
    classify64 n = classify64 m := by
  have he : n / 2 ^ 52 % 2 ^ 11 = m / 2 ^ 52 % 2 ^ 11 := by omega
  have ht : n / 2 ^ 0 % 2 ^ 52 = m / 2 ^ 0 % 2 ^ 52 := by omega
  simp only [classify64, classify, decode64, decode, field, binary64ExponentBits,
    binary64SignificandBits, he, ht]
  rfl

theorem isNaN_neg32 (x : F32) : (F32.neg x).IsNaN ↔ x.IsNaN := by
  have h : (x.bits ^^^ 0x80000000).toNat % 2 ^ 31 = x.bits.toNat % 2 ^ 31 := by
    rw [UInt32.toNat_xor, Nat.xor_mod_two_pow]
    have h₀ : (0x80000000 : UInt32).toNat % 2 ^ 31 = 0 := by decide
    rw [h₀, Nat.xor_zero]
  unfold F32.IsNaN F32.neg
  rw [classify32_congr h]

theorem isNaN_abs32 (x : F32) : (F32.abs x).IsNaN ↔ x.IsNaN := by
  have h : (x.bits &&& 0x7fffffff).toNat % 2 ^ 31 = x.bits.toNat % 2 ^ 31 := by
    have h₀ : (0x7fffffff : UInt32).toNat = 2 ^ 31 - 1 := by decide
    rw [UInt32.toNat_and, h₀, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  unfold F32.IsNaN F32.abs
  rw [classify32_congr h]

theorem isNaN_neg64 (x : F64) : (F64.neg x).IsNaN ↔ x.IsNaN := by
  have h : (x.bits ^^^ 0x8000000000000000).toNat % 2 ^ 63 = x.bits.toNat % 2 ^ 63 := by
    rw [UInt64.toNat_xor, Nat.xor_mod_two_pow]
    have h₀ : (0x8000000000000000 : UInt64).toNat % 2 ^ 63 = 0 := by decide
    rw [h₀, Nat.xor_zero]
  unfold F64.IsNaN F64.neg
  rw [classify64_congr h]

theorem isNaN_abs64 (x : F64) : (F64.abs x).IsNaN ↔ x.IsNaN := by
  have h : (x.bits &&& 0x7fffffffffffffff).toNat % 2 ^ 63 = x.bits.toNat % 2 ^ 63 := by
    have h₀ : (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 := by decide
    rw [UInt64.toNat_and, h₀, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  unfold F64.IsNaN F64.abs
  rw [classify64_congr h]


/-! ## Canonicalisation of bits -/

@[simp] theorem asF32_bits_inv (w : F32) : asF32 w.bits.toBitVec = w := by
  cases w
  simp only [asF32, UInt32.ofBitVec_toBitVec]

@[simp] theorem asF64_bits_inv (w : F64) : asF64 w.bits.toBitVec = w := by
  cases w
  simp only [asF64, UInt64.ofBitVec_toBitVec]

theorem asF32_nan32 : asF32 nan32 = F32.canonicalNaN := asF32_bits_inv _

theorem asF64_nan64 : asF64 nan64 = F64.canonicalNaN := asF64_bits_inv _

theorem nan32_isNaN : (asF32 nan32).IsNaN := by
  rw [asF32_nan32]
  decide

theorem nan64_isNaN : (asF64 nan64).IsNaN := by
  rw [asF64_nan64]
  decide

theorem canon32_nan {b : BitVec 32} (h : (asF32 b).IsNaN) : canon32 b = nan32 := by
  simp only [canon32, F32.isNaN, decide_eq_true h, ite_true]

theorem canon32_ok {b : BitVec 32} (h : ¬ (asF32 b).IsNaN) : canon32 b = b := by
  simp only [canon32, F32.isNaN, decide_eq_false h, Bool.false_eq_true, ite_false]

theorem canon64_nan {b : BitVec 64} (h : (asF64 b).IsNaN) : canon64 b = nan64 := by
  simp only [canon64, F64.isNaN, decide_eq_true h, ite_true]

theorem canon64_ok {b : BitVec 64} (h : ¬ (asF64 b).IsNaN) : canon64 b = b := by
  simp only [canon64, F64.isNaN, decide_eq_false h, Bool.false_eq_true, ite_false]

theorem sim_canon32 (b : BitVec 32) : Sim32 (asF32 b) (asF32 (canon32 b)) := by
  by_cases h : (asF32 b).IsNaN
  · rw [canon32_nan h]
    exact Or.inr ⟨h, nan32_isNaN⟩
  · rw [canon32_ok h]
    exact Or.inl rfl

theorem sim_canon64 (b : BitVec 64) : Sim64 (asF64 b) (asF64 (canon64 b)) := by
  by_cases h : (asF64 b).IsNaN
  · rw [canon64_nan h]
    exact Or.inr ⟨h, nan64_isNaN⟩
  · rw [canon64_ok h]
    exact Or.inl rfl

/-- Operands equal up to NaN have the same canonical image. -/
theorem canon32_of_sim {b b' : BitVec 32} (h : Sim32 (asF32 b) (asF32 b')) :
    canon32 b' = canon32 b := by
  rcases h with h | ⟨h₁, h₂⟩
  · have hb : b' = b := by
      rw [← Numerics.asF32_bits b', ← Numerics.asF32_bits b, h]
    rw [hb]
  · rw [canon32_nan h₁, canon32_nan h₂]

theorem canon64_of_sim {b b' : BitVec 64} (h : Sim64 (asF64 b) (asF64 b')) :
    canon64 b' = canon64 b := by
  rcases h with h | ⟨h₁, h₂⟩
  · have hb : b' = b := by
      rw [← Numerics.asF64_bits b', ← Numerics.asF64_bits b, h]
    rw [hb]
  · rw [canon64_nan h₁, canon64_nan h₂]

theorem canon32_idem (b : BitVec 32) : canon32 (canon32 b) = canon32 b :=
  canon32_of_sim (sim_canon32 b)

theorem canon64_idem (b : BitVec 64) : canon64 (canon64 b) = canon64 b :=
  canon64_of_sim (sim_canon64 b)

/-- An image that is not a NaN determines the bits. -/
theorem canon32_inj {b b' : BitVec 32} (h : canon32 b = canon32 b') (hb : ¬ (asF32 b).IsNaN) :
    b' = b := by
  rw [canon32_ok hb] at h
  by_cases hb' : (asF32 b').IsNaN
  · rw [canon32_nan hb'] at h
    rw [h] at hb
    exact absurd nan32_isNaN hb
  · rw [canon32_ok hb'] at h
    exact h.symm

theorem canon64_inj {b b' : BitVec 64} (h : canon64 b = canon64 b') (hb : ¬ (asF64 b).IsNaN) :
    b' = b := by
  rw [canon64_ok hb] at h
  by_cases hb' : (asF64 b').IsNaN
  · rw [canon64_nan hb'] at h
    rw [h] at hb
    exact absurd nan64_isNaN hb
  · rw [canon64_ok hb'] at h
    exact h.symm


/-! ## Result sets have the canonical image of the deterministic result (`32`) -/

theorem binaryResult32_canon {eval : F32 → F32 → F32} {a b : F32} {z : BitVec 32}
    (h : F32.binaryResult eval a b (asF32 z)) : canon32 z = canon32 (eval a b).bits.toBitVec := by
  unfold F32.binaryResult at h
  by_cases hn : (eval a b).IsNaN
  · have hz : (asF32 z).IsNaN := by
      simp only [hn, ↓reduceIte] at h
      split at h
      · exact h.1
      · exact h.1
    have hr : (asF32 (eval a b).bits.toBitVec).IsNaN := by
      rw [asF32_bits_inv]
      exact hn
    rw [canon32_nan hz, canon32_nan hr]
  · have hz : asF32 z = eval a b := by simpa only [hn, ↓reduceIte] using h
    rw [← hz]
    exact congrArg canon32 (Numerics.asF32_bits z).symm

theorem unaryResult32_canon {eval : F32 → F32} {a : F32} {z : BitVec 32}
    (h : F32.unaryResult eval a (asF32 z)) : canon32 z = canon32 (eval a).bits.toBitVec := by
  unfold F32.unaryResult at h
  by_cases hn : (eval a).IsNaN
  · have hz : (asF32 z).IsNaN := by
      simp only [hn, ↓reduceIte] at h
      split at h
      · exact h.1
      · exact h.1
    have hr : (asF32 (eval a).bits.toBitVec).IsNaN := by
      rw [asF32_bits_inv]
      exact hn
    rw [canon32_nan hz, canon32_nan hr]
  · have hz : asF32 z = eval a := by simpa only [hn, ↓reduceIte] using h
    rw [← hz]
    exact congrArg canon32 (Numerics.asF32_bits z).symm

/-- A sign operation commutes with canonicalisation up to canonicalisation. -/
theorem sign32_canon {f : F32 → F32} (hf : ∀ w, (f w).IsNaN ↔ w.IsNaN) (x : BitVec 32) :
    canon32 (f (asF32 (canon32 x))).bits.toBitVec = canon32 (f (asF32 x)).bits.toBitVec := by
  by_cases hx : (asF32 x).IsNaN
  · have h₁ : (asF32 (f (asF32 (canon32 x))).bits.toBitVec).IsNaN := by
      rw [asF32_bits_inv, hf, canon32_nan hx]
      exact nan32_isNaN
    have h₂ : (asF32 (f (asF32 x)).bits.toBitVec).IsNaN := by
      rw [asF32_bits_inv, hf]
      exact hx
    rw [canon32_nan h₁, canon32_nan h₂]
  · rw [canon32_ok hx]


/-! ## Result sets have the canonical image of the deterministic result (`64`) -/

theorem binaryResult64_canon {eval : F64 → F64 → F64} {a b : F64} {z : BitVec 64}
    (h : F64.binaryResult eval a b (asF64 z)) : canon64 z = canon64 (eval a b).bits.toBitVec := by
  unfold F64.binaryResult at h
  by_cases hn : (eval a b).IsNaN
  · have hz : (asF64 z).IsNaN := by
      simp only [hn, ↓reduceIte] at h
      split at h
      · exact h.1
      · exact h.1
    have hr : (asF64 (eval a b).bits.toBitVec).IsNaN := by
      rw [asF64_bits_inv]
      exact hn
    rw [canon64_nan hz, canon64_nan hr]
  · have hz : asF64 z = eval a b := by simpa only [hn, ↓reduceIte] using h
    rw [← hz]
    exact congrArg canon64 (Numerics.asF64_bits z).symm

theorem unaryResult64_canon {eval : F64 → F64} {a : F64} {z : BitVec 64}
    (h : F64.unaryResult eval a (asF64 z)) : canon64 z = canon64 (eval a).bits.toBitVec := by
  unfold F64.unaryResult at h
  by_cases hn : (eval a).IsNaN
  · have hz : (asF64 z).IsNaN := by
      simp only [hn, ↓reduceIte] at h
      split at h
      · exact h.1
      · exact h.1
    have hr : (asF64 (eval a).bits.toBitVec).IsNaN := by
      rw [asF64_bits_inv]
      exact hn
    rw [canon64_nan hz, canon64_nan hr]
  · have hz : asF64 z = eval a := by simpa only [hn, ↓reduceIte] using h
    rw [← hz]
    exact congrArg canon64 (Numerics.asF64_bits z).symm

/-- A sign operation commutes with canonicalisation up to canonicalisation. -/
theorem sign64_canon {f : F64 → F64} (hf : ∀ w, (f w).IsNaN ↔ w.IsNaN) (x : BitVec 64) :
    canon64 (f (asF64 (canon64 x))).bits.toBitVec = canon64 (f (asF64 x)).bits.toBitVec := by
  by_cases hx : (asF64 x).IsNaN
  · have h₁ : (asF64 (f (asF64 (canon64 x))).bits.toBitVec).IsNaN := by
      rw [asF64_bits_inv, hf, canon64_nan hx]
      exact nan64_isNaN
    have h₂ : (asF64 (f (asF64 x)).bits.toBitVec).IsNaN := by
      rw [asF64_bits_inv, hf]
      exact hx
    rw [canon64_nan h₁, canon64_nan h₂]
  · rw [canon64_ok hx]


/-! ## Operators on canonicalised operands -/

/-- **Binary operators other than `copysign` ignore NaN payloads.** -/
theorem binOp_canon {t : FloatType} {op : FloatBinOp} (hop : op ≠ .copysign)
    (x y : BitVec t.width) :
    floatBinOp t op (canonBits (.float t) x) (canonBits (.float t) y) = floatBinOp t op x y := by
  cases t
  · show (Numerics.floatBinOp32 op (asF32 (canon32 x)) (asF32 (canon32 y))).bits.toBitVec =
      (Numerics.floatBinOp32 op (asF32 x) (asF32 y)).bits.toBitVec
    rw [binOp32_congr hop (sim_canon32 x) (sim_canon32 y)]
  · show (Numerics.floatBinOp64 op (asF64 (canon64 x)) (asF64 (canon64 y))).bits.toBitVec =
      (Numerics.floatBinOp64 op (asF64 x) (asF64 y)).bits.toBitVec
    rw [binOp64_congr hop (sim_canon64 x) (sim_canon64 y)]

/-- **Comparisons ignore NaN payloads.** -/
theorem relOp_canon {t : FloatType} (op : FloatRelOp) (x y : BitVec t.width) :
    floatRelOp t op (canonBits (.float t) x) (canonBits (.float t) y) = floatRelOp t op x y := by
  cases t
  · show Numerics.bool32 (Numerics.floatRelOp32 op (asF32 (canon32 x)) (asF32 (canon32 y))) =
      Numerics.bool32 (Numerics.floatRelOp32 op (asF32 x) (asF32 y))
    rw [relOp32_congr op (sim_canon32 x) (sim_canon32 y)]
  · show Numerics.bool32 (Numerics.floatRelOp64 op (asF64 (canon64 x)) (asF64 (canon64 y))) =
      Numerics.bool32 (Numerics.floatRelOp64 op (asF64 x) (asF64 y))
    rw [relOp64_congr op (sim_canon64 x) (sim_canon64 y)]

/-- Unary operators other than the sign operations ignore NaN payloads. -/
theorem unOp_canon {t : FloatType} {op : FloatUnOp} (hop : op ≠ .abs ∧ op ≠ .neg)
    (x : BitVec t.width) : floatUnOp t op (canonBits (.float t) x) = floatUnOp t op x := by
  cases t
  · show (Numerics.floatUnOp32 op (asF32 (canon32 x))).bits.toBitVec =
      (Numerics.floatUnOp32 op (asF32 x)).bits.toBitVec
    rw [unOp32_congr hop (sim_canon32 x)]
  · show (Numerics.floatUnOp64 op (asF64 (canon64 x))).bits.toBitVec =
      (Numerics.floatUnOp64 op (asF64 x)).bits.toBitVec
    rw [unOp64_congr hop (sim_canon64 x)]

/-- The sign operations commute with canonicalisation up to canonicalisation. -/
theorem signOp_canon {t : FloatType} {op : FloatUnOp} (hop : op = .abs ∨ op = .neg)
    (x : BitVec t.width) :
    canonBits (.float t) (floatUnOp t op x) =
      canonBits (.float t) (floatUnOp t op (canonBits (.float t) x)) := by
  rcases hop with rfl | rfl <;> cases t
  · exact (sign32_canon isNaN_abs32 x).symm
  · exact (sign64_canon isNaN_abs64 x).symm
  · exact (sign32_canon isNaN_neg32 x).symm
  · exact (sign64_canon isNaN_neg64 x).symm

theorem binOpRel_eq {t : FloatType} {op : FloatBinOp} (hop : op ≠ .copysign)
    {x y z : BitVec t.width} :
    floatBinOpRel t op x y z ↔ match t with
      | .f32 => F32.binaryResult (Numerics.floatBinOp32 op) (asF32 x) (asF32 y) (asF32 z)
      | .f64 => F64.binaryResult (Numerics.floatBinOp64 op) (asF64 x) (asF64 y) (asF64 z) := by
  cases op <;> first | exact Iff.rfl | exact absurd rfl hop

theorem unOpRel_eq {t : FloatType} {op : FloatUnOp} (hop : op ≠ .abs ∧ op ≠ .neg)
    {x z : BitVec t.width} :
    floatUnOpRel t op x z ↔ match t with
      | .f32 => F32.unaryResult (Numerics.floatUnOp32 op) (asF32 x) (asF32 z)
      | .f64 => F64.unaryResult (Numerics.floatUnOp64 op) (asF64 x) (asF64 z) := by
  cases op <;> first | exact Iff.rfl | exact absurd rfl hop.1 | exact absurd rfl hop.2

/-- **Every result a profile allows for a binary operator other than `copysign` has the
canonical image of the deterministic result.** -/
theorem canon_floatBinOpP {P : Profile} {t : FloatType} {op : FloatBinOp} (hop : op ≠ .copysign)
    {x y z : BitVec t.width} (h : floatBinOpP P t op x y z) :
    canonBits (.float t) z = canonBits (.float t) (floatBinOp t op x y) := by
  unfold floatBinOpP at h
  cases hn : P.nan
  · have h' : floatBinOpRel t op x y z := by simpa only [hn] using h
    have h'' := (binOpRel_eq hop).mp h'
    cases t
    · exact binaryResult32_canon h''
    · exact binaryResult64_canon h''
  · have hz : z = floatBinOp t op x y := by simpa only [hn] using h
    rw [hz]

/-- The sign operations are exact at every profile. -/
theorem floatUnOpP_sign {P : Profile} {t : FloatType} {op : FloatUnOp} (hop : op = .abs ∨ op = .neg)
    {x z : BitVec t.width} (h : floatUnOpP P t op x z) : z = floatUnOp t op x := by
  unfold floatUnOpP at h
  cases hn : P.nan
  · have h' : floatUnOpRel t op x z := by simpa only [hn] using h
    rcases hop with rfl | rfl <;> exact h'
  · simpa only [hn] using h

/-- **Every result a profile allows for a unary operator has the canonical image of the
deterministic result on the canonicalised operand.** -/
theorem canon_floatUnOpP {P : Profile} {t : FloatType} {op : FloatUnOp} {x z : BitVec t.width}
    (h : floatUnOpP P t op x z) :
    canonBits (.float t) z = canonBits (.float t) (floatUnOp t op (canonBits (.float t) x)) := by
  by_cases hs : op = .abs ∨ op = .neg
  · rw [floatUnOpP_sign hs h]
    exact signOp_canon hs x
  · have hop : op ≠ .abs ∧ op ≠ .neg := not_or.mp hs
    rw [unOp_canon hop x]
    unfold floatUnOpP at h
    cases hn : P.nan
    · have h' : floatUnOpRel t op x z := by simpa only [hn] using h
      have h'' := (unOpRel_eq hop).mp h'
      cases t
      · exact unaryResult32_canon h''
      · exact unaryResult64_canon h''
    · have hz : z = floatUnOp t op x := by simpa only [hn] using h
      rw [hz]


/-! ## Conversions -/

/-- A conversion that does not reinterpret a float as an integer. -/
def ConvOk (op : ConvertOp) : Prop := ∀ t, op ≠ .reinterpretInt t

/-- Results of two conversions agree up to NaN payloads (and traps are equal). -/
def RelC (t : NumType) : Except Numerics.FloatTrap (BitVec t.width) →
    Except Numerics.FloatTrap (BitVec t.width) → Prop
  | .error e, .error e' => e = e'
  | .ok z, .ok z' => canonBits t z = canonBits t z'
  | _, _ => False

theorem RelC.refl (t : NumType) (r : Except Numerics.FloatTrap (BitVec t.width)) : RelC t r r := by
  cases r
  · exact rfl
  · exact rfl

/-- **Conversions other than reinterpretation ignore NaN payloads.** -/
theorem convert_canon {op : ConvertOp} (hop : ConvOk op) (x : BitVec op.source.width) :
    convert op (canonBits op.source x) = convert op x := by
  cases op with
  | trunc s t sg =>
    cases s
    · show Numerics.truncFloat .f32 t sg (canon32 x) = Numerics.truncFloat .f32 t sg x
      simp only [Numerics.truncFloat, Numerics.unpackFloat, (sim_canon32 x).model]
      rfl
    · show Numerics.truncFloat .f64 t sg (canon64 x) = Numerics.truncFloat .f64 t sg x
      simp only [Numerics.truncFloat, Numerics.unpackFloat, (sim_canon64 x).model]
      rfl
  | truncSat s t sg =>
    cases s
    · show Except.ok (Numerics.truncSatFloat .f32 t sg (canon32 x)) =
        Except.ok (Numerics.truncSatFloat .f32 t sg x)
      simp only [Numerics.truncSatFloat, Numerics.unpackFloat, (sim_canon32 x).model]
    · show Except.ok (Numerics.truncSatFloat .f64 t sg (canon64 x)) =
        Except.ok (Numerics.truncSatFloat .f64 t sg x)
      simp only [Numerics.truncSatFloat, Numerics.unpackFloat, (sim_canon64 x).model]
  | demote =>
    show Except.ok ((asF64 (canon64 x)).toF32.bits.toBitVec) =
      Except.ok ((asF64 x).toF32.bits.toBitVec)
    simp only [F64.toF32, (sim_canon64 x).model]
  | promote =>
    show Except.ok ((asF32 (canon32 x)).toF64.bits.toBitVec) =
      Except.ok ((asF32 x).toF64.bits.toBitVec)
    simp only [F32.toF64, (sim_canon32 x).model]
  | reinterpretInt t => exact absurd rfl (hop t)
  | wrap | extend _ | convert _ _ _ | reinterpretFloat _ => rfl

/-- A choice among the NaNs allowed for a NaN result, as in `convertRel` for `demote`. -/
theorem choice32_canon {r : F32} {c : Prop} [Decidable c] {y : BitVec 32}
    (h : if r.IsNaN then (if c then (asF32 y).IsCanonicalNaN else (asF32 y).IsArithmeticNaN)
      else asF32 y = r) : canon32 y = canon32 r.bits.toBitVec := by
  by_cases hn : r.IsNaN
  · have hy : (asF32 y).IsNaN := by
      simp only [hn, ↓reduceIte] at h
      split at h
      · exact h.1
      · exact h.1
    have hr : (asF32 r.bits.toBitVec).IsNaN := by
      rw [asF32_bits_inv]
      exact hn
    rw [canon32_nan hy, canon32_nan hr]
  · have hy : asF32 y = r := by simpa only [hn, ↓reduceIte] using h
    rw [← hy]
    exact congrArg canon32 (Numerics.asF32_bits y).symm

/-- A choice among the NaNs allowed for a NaN result, as in `convertRel` for `promote`. -/
theorem choice64_canon {r : F64} {c : Prop} [Decidable c] {y : BitVec 64}
    (h : if r.IsNaN then (if c then (asF64 y).IsCanonicalNaN else (asF64 y).IsArithmeticNaN)
      else asF64 y = r) : canon64 y = canon64 r.bits.toBitVec := by
  by_cases hn : r.IsNaN
  · have hy : (asF64 y).IsNaN := by
      simp only [hn, ↓reduceIte] at h
      split at h
      · exact h.1
      · exact h.1
    have hr : (asF64 r.bits.toBitVec).IsNaN := by
      rw [asF64_bits_inv]
      exact hn
    rw [canon64_nan hy, canon64_nan hr]
  · have hy : asF64 y = r := by simpa only [hn, ↓reduceIte] using h
    rw [← hy]
    exact congrArg canon64 (Numerics.asF64_bits y).symm

/-- The specification's conversion results agree with the deterministic conversion up to NaN
payloads. -/
theorem convertRel_relC {op : ConvertOp} {x : BitVec op.source.width}
    {r : Except Numerics.FloatTrap (BitVec op.target.width)} (h : convertRel op x r) :
    RelC op.target r (convert op x) := by
  have hd : r = convert op x → RelC op.target r (convert op x) := fun hr => hr ▸ RelC.refl _ _
  cases op
  case demote =>
    cases r with
    | ok y =>
      exact choice32_canon (r := (asF64 x).toF32) (c := (asF64 x).IsNonNaNOrCanonicalNaN) h
    | error e => exact hd h
  case promote =>
    cases r with
    | ok y =>
      exact choice64_canon (r := (asF32 x).toF64) (c := (asF32 x).IsNonNaNOrCanonicalNaN) h
    | error e => exact hd h
  all_goals (cases r <;> exact hd h)

/-- **Every result a profile allows for a conversion other than reinterpretation agrees, up to
NaN payloads, with the deterministic conversion of the canonicalised operand.** -/
theorem convertP_canon {P : Profile} {op : ConvertOp} (hop : ConvOk op)
    {x : BitVec op.source.width} {r : Except Numerics.FloatTrap (BitVec op.target.width)}
    (h : convertP P op x r) : RelC op.target r (convert op (canonBits op.source x)) := by
  rw [convert_canon hop x]
  unfold convertP at h
  cases hn : P.nan
  · have h' : convertRel op x r := by simpa only [hn] using h
    exact convertRel_relC h'
  · have hr : r = convert op x := by simpa only [hn] using h
    rw [hr]
    exact RelC.refl _ _

end Silmaril.Proofs.Wasm.Det.NaN
