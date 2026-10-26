module

public import Silmaril.Numeric.Float.Instances
public import Silmaril.Wasm.Numerics.Float
public import Silmaril.Numeric.Ieee754.RneBridge
public import Silmaril.Numeric.Ieee754.PackingCorrectness
public import Silmaril.Numeric.Integer.Conversion

/-!
# Which profile results WebAssembly admits

WebAssembly Core 3.0 §4.3.3 specifies scalar floating point with
round-to-nearest-ties-to-even, gradual underflow, and a nondeterministic NaN
result: canonical NaN (either sign) when every NaN operand is canonical, and any
arithmetic (quiet) NaN otherwise. The repository states this as the relations
`Wasm.Numerics.floatBinOpRel`, `floatUnOpRel` and `convertRel`, plus the
deterministic integer conversions `truncFloat`, `truncSatFloat` and `convertInt`.

This module proves, for every `Profile` (and therefore for x86 SSE, RISC-V F/D
and AArch64 alike), which profile operations produce results those relations
admit. The hypotheses are sufficient configuration requirements for a compiler
to establish (their necessity is not proved here): no input flushing (x86
DAZ = 0, AArch64 FZ = 0), no result flushing where a result can be tiny (x86
FZ = 0, AArch64 FZ = 0), and round-to-nearest-even where WebAssembly rounds. For
`ceil`/`floor`/`trunc`/`nearest`, the `signalInexact` argument of
`Profile.roundToIntegral` is arbitrary.

* `add`/`sub`/`mul`/`div`/`sqrt`, `promote`/`demote`: always admitted
  (`binary_admitted32`, …). The NaN a profile chooses (propagated and quieted, or
  the default NaN of either sign) always lies in WebAssembly's permitted set.
* `ceil`/`floor`/`trunc`/`nearest`: admitted in their static direction without
  any rounding-mode hypothesis.
* `min`/`max`: `MinMaxRule.minimum` (AArch64 `FMIN`) is always admitted; the other
  rules are admitted exactly when `MinMaxRule.agreesWithWasm` holds, which
  characterizes x86 `MINSS`, RISC-V `FMIN` and AArch64 `FMINNM` (`minMax_admitted_iff32`).
* float-to-integer: every profile agrees with `trunc` whenever `trunc` does not
  trap; the out-of-range results are `IntOverflowRule`-specific
  (`toInt_eq_truncFloat32`, `toInt_saturateNaNToZero_eq_truncSat32`, …).
* integer-to-float and comparisons: equal to WebAssembly for every profile.

`Bits.isQuietNaN` is WebAssembly's arithmetic-NaN class and
`Bits.isCanonicalNaN` its canonical-NaN class (`isArithmeticNaN32`,
`isCanonicalNaN32`).
-/

@[expose] public section

namespace Silmaril.Numeric.Float

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Ieee754
open Silmaril.Wasm Silmaril.Wasm.Numerics

/-! ## Encodings: the repository's predicates as `Bits` predicates -/

private theorem exponent_eq_allOnes_iff (fmt : Format) (e : BitVec fmt.exponentBits) :
    e = -1#_ ↔ e.toNat = maxExponentField fmt.exponentBits := by
  rw [← BitVec.toNat_inj, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
  rfl

/-- The repository's field-based NaN classification agrees with `Bits.isNaN`. -/
theorem classify_eq_nan_iff (fmt : Format) (b : Bits fmt) :
    classify fmt.exponentBits fmt.mantissaBitsWithoutImplicit
      (decode fmt.exponentBits fmt.mantissaBitsWithoutImplicit b.toNat) = .nan ↔
      b.isNaN = true := by
  have he := Conformance.unpackExponent_toNat fmt b
  have hm := Conformance.unpackMantissa_toNat fmt b
  have hmax : maxExponentField fmt.exponentBits ≠ 0 := by
    have := fmt.he
    have : 1 < 2 ^ fmt.exponentBits := Nat.one_lt_two_pow_iff.mpr (by omega)
    unfold maxExponentField
    omega
  have hm0 : unpackMantissa b = 0#_ ↔
      (decode fmt.exponentBits fmt.mantissaBitsWithoutImplicit b.toNat).trailingSignificand = 0 :=
          by
    rw [← BitVec.toNat_inj, hm]
    simp
  simp only [Bits.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  rw [exponent_eq_allOnes_iff, he, hm0]
  unfold classify
  split_ifs <;> simp_all
  omega

/-- The core decoder is unchanged by the core model's NaN canonicalization. -/
theorem unpack_pack_unpack (fmt : Format) (b : Bits fmt) :
    unpack fmt (pack fmt (unpack fmt b)) = unpack fmt b := by
  rw [Conformance.pack_unpack]
  split
  next h =>
    have hn : b.isNaN = true := by
      simp only [Bits.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
      exact h
    rw [Conformance.unpack_packedNaN]
    exact ((Bits.value_eq_notANumber_iff b).mpr hn).symm
  next => rfl

theorem canonicalNaN_bits32 : F32.canonicalNaN.bits = 0x7fc00000 := by decide
theorem canonicalNaN_bits64 : F64.canonicalNaN.bits = 0x7ff8000000000000 := by decide

/-- `Bits.isNaN` in terms of field values. -/
theorem isNaN_iff_toNat {fmt : Format} (b : Bits fmt) : b.isNaN = true ↔
    (unpackExponent b).toNat = 2 ^ fmt.exponentBits - 1 ∧ (unpackMantissa b).toNat ≠ 0 := by
  simp only [Bits.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ← BitVec.toNat_inj,
    BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.zero_mod]

/-- `Bits.isCanonicalNaN` in terms of field values. -/
theorem isCanonicalNaN_iff_toNat {fmt : Format} (b : Bits fmt) : b.isCanonicalNaN = true ↔
    b.isNaN = true ∧ (unpackMantissa b).toNat = 2 ^ (fmt.mantissaBitsWithoutImplicit - 1) := by
  simp only [Bits.isCanonicalNaN, Bool.and_eq_true, beq_iff_eq, ← BitVec.toNat_inj,
    Bits.quietMask_toNat]

/-- `Bits.isQuietNaN` in terms of field values. -/
theorem isQuietNaN_iff_toNat {fmt : Format} (b : Bits fmt) : b.isQuietNaN = true ↔
    b.isNaN = true ∧
      (unpackMantissa b).toNat / 2 ^ (fmt.mantissaBitsWithoutImplicit - 1) % 2 = 1 := by
  simp only [Bits.isQuietNaN, Bool.and_eq_true, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_eq]

section Binary32

variable (x y z : BitVec 32)

private theorem exponent_toNat32 :
    (unpackExponent (spec := .binary32) x).toNat = x.toNat / 8388608 % 256 := by
  rw [Conformance.unpackExponent_toNat]
  simp [decode, field]

private theorem mantissa_toNat32 : (unpackMantissa (spec := .binary32) x).toNat = x.toNat %
    8388608 := by
  rw [Conformance.unpackMantissa_toNat]
  simp [decode, field]

private theorem sign_toNat32 :
    (unpackSign (spec := .binary32) x).toNat = x.toNat / 2147483648 % 2 := by
  rw [Conformance.unpackSign_toNat]
  simp [field]

theorem isNaN32 : (asF32 x).IsNaN ↔ Bits.isNaN (fmt := .binary32) x = true :=
  classify_eq_nan_iff .binary32 x

theorem isCanonicalNaN32 :
    (asF32 x).IsCanonicalNaN ↔ Bits.isCanonicalNaN (fmt := .binary32) x = true := by
  have hmask : ∀ v : UInt32, (v &&& 0x7fffffff).toNat = v.toNat % 2147483648 := by
    intro v
    rw [UInt32.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod v.toNat 31
  have key : Bits.isNaN (fmt := .binary32) x = true →
      (x.toNat % 2147483648 = 0x7fc00000 ↔ Bits.isCanonicalNaN (fmt := .binary32) x = true) := by
    intro h
    rw [isCanonicalNaN_iff_toNat, mantissa_toNat32]
    have hn := h
    rw [isNaN_iff_toNat, exponent_toNat32, mantissa_toNat32] at hn
    have := x.isLt
    simp only [h, true_and]
    norm_num at hn ⊢
    omega
  have hc : ((0x7fc00000 : UInt32) &&& 0x7fffffff).toNat = 0x7fc00000 := by decide
  unfold F32.IsCanonicalNaN
  rw [isNaN32, canonicalNaN_bits32, ← UInt32.toNat_inj, hmask, hc]
  change (_ ∧ x.toNat % 2147483648 = _) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    exact (key h1).mp h2
  · intro h
    have h1 := Bits.isNaN_of_isCanonicalNaN h
    exact ⟨h1, (key h1).mpr h⟩

theorem isArithmeticNaN32 :
    (asF32 x).IsArithmeticNaN ↔ Bits.isQuietNaN (fmt := .binary32) x = true := by
  unfold F32.IsArithmeticNaN
  rw [isNaN32, isQuietNaN_iff_toNat, mantissa_toNat32]
  change (_ ∧ x.toNat % 2 ^ 23 ≥ 2 ^ 22) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    norm_num at h2 ⊢
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    norm_num at h2 ⊢
    omega

theorem isNonNaNOrCanonicalNaN32 :
    (asF32 x).IsNonNaNOrCanonicalNaN ↔ Bits.isNonNaNOrCanonicalNaN (fmt := .binary32) x = true := by
  simp [F32.IsNonNaNOrCanonicalNaN, Bits.isNonNaNOrCanonicalNaN, isNaN32, isCanonicalNaN32]

theorem signBit32 : (asF32 x).signBit = Bits.signBit (fmt := .binary32) x := by
  have hs : Bits.signBit (fmt := .binary32) x = decide (x.toNat / 2147483648 % 2 = 1) := by
    unfold Bits.signBit
    rw [Bool.eq_iff_iff, beq_iff_eq, ← BitVec.toNat_inj, sign_toNat32]
    simp
  have hf : (asF32 x).signBit = decide (x &&& 0x80000000#32 ≠ 0#32) := by
    unfold F32.signBit
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_eq, ne_eq, ne_eq, ← UInt32.toBitVec_inj]
    rfl
  have htwo : (0x80000000#32 : BitVec 32) = BitVec.twoPow 32 31 := by decide
  rw [hs, hf, htwo, BitVec.and_twoPow, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : x.toNat / 2 ^ 31 % 2 = 1
  · simp only [h, decide_true, ↓reduceIte]
    norm_num at h ⊢
    simp [h]
  · simp only [h, decide_false, ↓reduceIte, Bool.false_eq_true]
    norm_num at h ⊢
    simp [h]

theorem asF32_inj : asF32 x = asF32 y ↔ x = y := by
  constructor
  · intro h
    exact congrArg (fun v : F32 => v.bits.toBitVec) h
  · rintro rfl
    rfl

theorem model_unpack32 : (asF32 x).model.unpack = Bits.value (fmt := .binary32) x :=
  unpack_pack_unpack .binary32 x

end Binary32

section Binary64

variable (x y z : BitVec 64)

private theorem exponent_toNat64 :
    (unpackExponent (spec := .binary64) x).toNat = x.toNat / 4503599627370496 % 2048 := by
  rw [Conformance.unpackExponent_toNat]
  simp [decode, field]

private theorem mantissa_toNat64 :
    (unpackMantissa (spec := .binary64) x).toNat = x.toNat % 4503599627370496 := by
  rw [Conformance.unpackMantissa_toNat]
  simp [decode, field]

private theorem sign_toNat64 :
    (unpackSign (spec := .binary64) x).toNat = x.toNat / 9223372036854775808 % 2 := by
  rw [Conformance.unpackSign_toNat]
  simp [field]

theorem isNaN64 : (asF64 x).IsNaN ↔ Bits.isNaN (fmt := .binary64) x = true :=
  classify_eq_nan_iff .binary64 x

theorem isCanonicalNaN64 :
    (asF64 x).IsCanonicalNaN ↔ Bits.isCanonicalNaN (fmt := .binary64) x = true := by
  have hmask : ∀ v : UInt64,
      (v &&& 0x7fffffffffffffff).toNat = v.toNat % 9223372036854775808 := by
    intro v
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod v.toNat 63
  have key : Bits.isNaN (fmt := .binary64) x = true →
      (x.toNat % 9223372036854775808 = 0x7ff8000000000000 ↔
        Bits.isCanonicalNaN (fmt := .binary64) x = true) := by
    intro h
    rw [isCanonicalNaN_iff_toNat, mantissa_toNat64]
    have hn := h
    rw [isNaN_iff_toNat, exponent_toNat64, mantissa_toNat64] at hn
    have := x.isLt
    simp only [h, true_and]
    norm_num at hn ⊢
    omega
  have hc : ((0x7ff8000000000000 : UInt64) &&& 0x7fffffffffffffff).toNat = 0x7ff8000000000000 := by
    decide
  unfold F64.IsCanonicalNaN
  rw [isNaN64, canonicalNaN_bits64, ← UInt64.toNat_inj, hmask, hc]
  change (_ ∧ x.toNat % 9223372036854775808 = _) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    exact (key h1).mp h2
  · intro h
    have h1 := Bits.isNaN_of_isCanonicalNaN h
    exact ⟨h1, (key h1).mpr h⟩

theorem isArithmeticNaN64 :
    (asF64 x).IsArithmeticNaN ↔ Bits.isQuietNaN (fmt := .binary64) x = true := by
  unfold F64.IsArithmeticNaN
  rw [isNaN64, isQuietNaN_iff_toNat, mantissa_toNat64]
  change (_ ∧ x.toNat % 2 ^ 52 ≥ 2 ^ 51) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    norm_num at h2 ⊢
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    norm_num at h2 ⊢
    omega

theorem isNonNaNOrCanonicalNaN64 :
    (asF64 x).IsNonNaNOrCanonicalNaN ↔ Bits.isNonNaNOrCanonicalNaN (fmt := .binary64) x = true := by
  simp [F64.IsNonNaNOrCanonicalNaN, Bits.isNonNaNOrCanonicalNaN, isNaN64, isCanonicalNaN64]

theorem signBit64 : (asF64 x).signBit = Bits.signBit (fmt := .binary64) x := by
  have hs : Bits.signBit (fmt := .binary64) x = decide (x.toNat / 9223372036854775808 % 2 = 1) := by
    unfold Bits.signBit
    rw [Bool.eq_iff_iff, beq_iff_eq, ← BitVec.toNat_inj, sign_toNat64]
    simp
  have hf : (asF64 x).signBit = decide (x &&& 0x8000000000000000#64 ≠ 0#64) := by
    unfold F64.signBit
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_eq, ne_eq, ne_eq, ← UInt64.toBitVec_inj]
    rfl
  have htwo : (0x8000000000000000#64 : BitVec 64) = BitVec.twoPow 64 63 := by decide
  rw [hs, hf, htwo, BitVec.and_twoPow, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : x.toNat / 2 ^ 63 % 2 = 1
  · simp only [h, decide_true, ↓reduceIte]
    norm_num at h ⊢
    simp [h]
  · simp only [h, decide_false, ↓reduceIte, Bool.false_eq_true]
    norm_num at h ⊢
    simp [h]

theorem asF64_inj : asF64 x = asF64 y ↔ x = y := by
  constructor
  · intro h
    exact congrArg (fun v : F64 => v.bits.toBitVec) h
  · rintro rfl
    rfl

theorem model_unpack64 : (asF64 x).model.unpack = Bits.value (fmt := .binary64) x :=
  unpack_pack_unpack .binary64 x

end Binary64

/-! ## A format-generic form of WebAssembly's NaN nondeterminism -/

/-- `result` is admitted where WebAssembly's deterministic reference produces
`reference`: an equal result if the reference is not a NaN, and otherwise a
canonical NaN when every NaN operand is canonical (`inputsCanonical`) or a quiet
NaN when some is not. -/
def Admits {fmt : Format} (inputsCanonical : Bool) (reference result : Bits fmt) : Prop :=
  if reference.isNaN then
    (if inputsCanonical then result.isCanonicalNaN else result.isQuietNaN) = true
  else result = reference

/-- Every NaN operand is canonical. -/
def allCanonical {fmt : Format} (operands : List (Bits fmt)) : Bool :=
  operands.all Bits.isNonNaNOrCanonicalNaN

theorem admits_of_canonical {fmt : Format} {c : Bool} {reference result : Bits fmt}
    (hnan : reference.isNaN = true) (h : result.isCanonicalNaN =
    true) : Admits c reference result := by
  unfold Admits
  simp only [hnan, ↓reduceIte]
  cases c
  · exact Bits.isQuietNaN_of_isCanonicalNaN h
  · exact h

theorem admits_self {fmt : Format} (c : Bool) {reference : Bits fmt}
    (h : reference.isNonNaNOrCanonicalNaN = true) : Admits c reference reference := by
  unfold Admits
  split
  next hn =>
    simp only [Bits.isNonNaNOrCanonicalNaN, hn, Bool.not_true, Bool.false_or] at h
    cases c
    · exact Bits.isQuietNaN_of_isCanonicalNaN h
    · exact h
  next => rfl

theorem admits_of_not_nan {fmt : Format} (c : Bool) {reference : Bits fmt}
    (h : reference.isNaN = false) : Admits c reference reference :=
  admits_self c (by simp [Bits.isNonNaNOrCanonicalNaN, h])

/-- The NaN a profile picks is either a quieted operand NaN or its default NaN. -/
theorem pickNaN_cases (p : Profile) {fmt : Format} (operands : List (Bits fmt)) :
    (∃ b ∈ operands, b.isNaN = true ∧ p.pickNaN operands = b.quiet) ∨
      p.pickNaN operands = p.defaultNaN fmt := by
  unfold Profile.pickNaN
  split
  · exact Or.inr rfl
  · split
    next b hb =>
      exact Or.inl ⟨b, List.mem_of_find?_eq_some hb, List.find?_some hb, rfl⟩
    next => exact Or.inr rfl
  · split
    next b hb =>
      have hs := List.find?_some hb
      simp only [Bits.isSignalingNaN, Bool.and_eq_true] at hs
      exact Or.inl ⟨b, List.mem_of_find?_eq_some hb, hs.1, rfl⟩
    next =>
      split
      next b hb =>
        exact Or.inl ⟨b, List.mem_of_find?_eq_some hb, List.find?_some hb, rfl⟩
      next => exact Or.inr rfl

/-- Every NaN a profile picks lies in WebAssembly's permitted NaN set. -/
theorem pickNaN_admits (p : Profile) {fmt : Format} (operands : List (Bits fmt))
    {reference : Bits fmt} (hnan : reference.isNaN = true) :
    Admits (allCanonical operands) reference (p.pickNaN operands) := by
  rcases pickNaN_cases p operands with ⟨b, hb, hbn, hpick⟩ | hdef
  · rw [hpick]
    unfold Admits
    simp only [hnan, ↓reduceIte]
    split
    next hall =>
      have hc : b.isNonNaNOrCanonicalNaN = true := List.all_eq_true.mp hall b hb
      simp only [Bits.isNonNaNOrCanonicalNaN, hbn, Bool.not_true, Bool.false_or] at hc
      rw [Bits.quiet_of_isCanonicalNaN hc]
      exact hc
    next => exact Bits.isQuietNaN_quiet hbn
  · rw [hdef]
    exact admits_of_canonical hnan (Bits.isCanonicalNaN_defaultNaN _ _)

/-- A core operation with a NaN operand rounds to the core model's NaN. -/
theorem CoreOp.round_of_nan (fmt : Format) (mode : RoundingMode) (op : CoreOp)
    (h : UnpackedFloat.notANumber ∈ op.operands) : (op.round fmt mode).isNaN = true := by
  have hnan : op.round fmt mode = packedNaN fmt := by
    cases op with
    | add x y =>
      simp only [CoreOp.operands, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;>
        first
          | rfl
          | (cases x <;> rfl)
    | sub x y =>
      simp only [CoreOp.operands, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;>
        first
          | rfl
          | (cases x <;> rfl)
    | mul x y =>
      simp only [CoreOp.operands, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;>
        first
          | rfl
          | (cases x <;> rfl)
    | div x y =>
      simp only [CoreOp.operands, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;>
        first
          | rfl
          | (cases x <;> rfl)
    | sqrt x =>
      simp only [CoreOp.operands, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      rfl
    | fma x y z =>
      simp only [CoreOp.operands, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;>
        first
          | rfl
          | (cases x <;> rfl)
          | (cases x <;> cases y <;> rfl)
    | convert x =>
      simp only [CoreOp.operands, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      rfl
  rw [hnan]
  exact Bits.isNaN_packedNaN fmt

/-- A profile's binary arithmetic result is admitted, without flushing. -/
theorem binary_admits (p : Profile) {fmt : Format}
    (core : ArithOp) (mode : RoundingMode) (x y : Bits fmt)
    (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (hops : (core.core x.value y.value).operands = [x.value, y.value]) :
    Admits (allCanonical [x, y]) ((core.core x.value y.value).round fmt mode)
      (p.binary fmt core mode x y).value := by
  simp only [Profile.binary, Profile.flushInput_of_false p _ hin,
    Profile.nanOrElse]
  split
  next hany =>
    apply pickNaN_admits
    apply CoreOp.round_of_nan
    rw [hops]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hany
    rcases hany with h | h
    · exact List.mem_cons.mpr (Or.inl ((Bits.value_eq_notANumber_iff x).mpr h).symm)
    · exact List.mem_cons_of_mem _
        (List.mem_singleton.mpr ((Bits.value_eq_notANumber_iff y).mpr h).symm)
  next =>
    simp only [Profile.finish, Profile.flushSign?, hout]
    split
    next hr => exact admits_of_canonical hr (Bits.isCanonicalNaN_defaultNaN _ _)
    next hr => exact admits_of_not_nan _ (by simpa using hr)

/-- A profile's square root is admitted, without flushing. -/
theorem sqrt_admits (p : Profile) {fmt : Format} (mode : RoundingMode)
    (x : Bits fmt) (hin : p.flushInputs = false) (hout : p.flushResults = false) :
    Admits (allCanonical [x]) ((CoreOp.sqrt x.value).round fmt mode)
      (p.sqrt fmt mode x).value := by
  simp only [Profile.sqrt, Profile.flushInput_of_false p _ hin,
    Profile.nanOrElse]
  split
  next hany =>
    apply pickNaN_admits
    apply CoreOp.round_of_nan
    simp only [List.any_cons, List.any_nil, Bool.or_false] at hany
    simp [CoreOp.operands, ((Bits.value_eq_notANumber_iff x).mpr hany)]
  next =>
    simp only [Profile.finish, Profile.flushSign?, hout]
    split
    next hr => exact admits_of_canonical hr (Bits.isCanonicalNaN_defaultNaN _ _)
    next hr => exact admits_of_not_nan _ (by simpa using hr)

/-- A profile's round-to-integral result is admitted, without input flushing,
provided the core integral rounding of a non-NaN operand is never a
non-canonical NaN (the repository proves this for binary32 and binary64). -/
theorem roundToIntegral_admits (p : Profile) {fmt : Format} (mode : RoundingMode)
    (signalInexact : Bool) (x : Bits fmt) (hin : p.flushInputs = false)
    (hcanon : Bits.isNonNaNOrCanonicalNaN
      (fmt := fmt) (Rounding.integralRounded fmt mode x.value) = true) :
    Admits (allCanonical [x]) (Rounding.integralRounded fmt mode x.value)
      (p.roundToIntegral fmt mode signalInexact x).value := by
  simp only [Profile.roundToIntegral, Profile.flushInput_of_false p _ hin,
    Profile.nanOrElse]
  split
  next hany =>
    apply pickNaN_admits
    simp only [List.any_cons, List.any_nil, Bool.or_false] at hany
    rw [(Bits.value_eq_notANumber_iff x).mpr hany]
    exact Bits.isNaN_packedNaN fmt
  next => exact admits_self _ hcanon

/-- A converted NaN is admitted. -/
theorem convertNaN_admits {src dst : Format} {x : Bits src} {reference : Bits dst}
    (hx : x.isNaN = true) (hr : reference.isNaN = true) :
    Admits x.isNonNaNOrCanonicalNaN reference (Bits.convertNaN src dst x) := by
  unfold Admits
  simp only [hr, ↓reduceIte]
  split
  next hc =>
    simp only [Bits.isNonNaNOrCanonicalNaN, hx, Bool.not_true, Bool.false_or] at hc
    exact Bits.isCanonicalNaN_convertNaN src dst hc
  next => exact Bits.isQuietNaN_convertNaN src dst x

/-- A profile's format conversion is admitted, without input flushing, when the
result is not flushed. -/
theorem convert_admits_of_noFlush (p : Profile) {src dst : Format} (mode : RoundingMode)
    (x : Bits src) (hin : p.flushInputs = false)
    (hf : p.flushSign? dst mode (FlagSpec.convertOutcome x.datum) = none) :
    Admits x.isNonNaNOrCanonicalNaN ((CoreOp.convert x.value).round dst mode)
      (p.convert src dst mode x).value := by
  unfold Profile.convert
  simp only [Profile.flushInput_of_false p _ hin]
  by_cases hx : x.isNaN = true
  · have hr : ((CoreOp.convert x.value).round dst mode).isNaN = true := by
      apply CoreOp.round_of_nan
      simp [CoreOp.operands, (Bits.value_eq_notANumber_iff x).mpr hx]
    simp only [hx, ↓reduceIte]
    cases p.propagation
    · exact admits_of_canonical hr (Bits.isCanonicalNaN_defaultNaN _ _)
    · exact convertNaN_admits hx hr
    · exact convertNaN_admits hx hr
  · simp only [hx, Bool.false_eq_true, ↓reduceIte, Profile.finish, hf]
    split
    next hr => exact admits_of_canonical hr (Bits.isCanonicalNaN_defaultNaN _ _)
    next hr => exact admits_of_not_nan _ (by simpa using hr)

/-- A profile's format conversion is admitted, without flushing. -/
theorem convert_admits (p : Profile) {src dst : Format} (mode : RoundingMode)
    (x : Bits src) (hin : p.flushInputs = false) (hout : p.flushResults = false) :
    Admits x.isNonNaNOrCanonicalNaN ((CoreOp.convert x.value).round dst mode)
      (p.convert src dst mode x).value :=
  convert_admits_of_noFlush p mode x hin (by simp [Profile.flushSign?, hout])

/-- A nonzero finite binary32 value is not tiny in binary64, under either
tininess detection: it is at least `2^-149` in magnitude, far above `2^-1022`. -/
theorem not_tiny_binary64_of_binary32 (tininess : FlagSpec.Tininess) (mode : RoundingMode)
    {v : ℚ} (h : FlagSpec.Representable Format.binary32 v) :
    ¬ FlagSpec.Tiny Format.binary64 tininess mode v := by
  rintro ⟨hv0, hsmall⟩
  have hrep64 := FlagSpec.representable_binary64_of_binary32 h
  obtain ⟨n, q, rfl, -, hq, -⟩ := h
  have hn : n ≠ 0 := by rintro rfl; simp at hv0
  have hmag : (2 : ℚ) ^ FlagSpec.emin Format.binary64 ≤ |(n : ℚ) * 2 ^ q| := by
    have h1 : (1 : ℚ) ≤ |(n : ℚ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    have hle : FlagSpec.emin Format.binary64 ≤ FlagSpec.minQuantum Format.binary32 := by
      decide +kernel
    have h2 : (2 : ℚ) ^ FlagSpec.emin Format.binary64 ≤ 2 ^ q :=
      zpow_le_zpow_right₀ (by norm_num) (le_trans hle hq)
    rw [abs_mul, abs_of_pos (FlagSpec.two_zpow_pos (K := ℚ) q)]
    calc (2 : ℚ) ^ FlagSpec.emin Format.binary64 = 1 * 2 ^ FlagSpec.emin Format.binary64 :=
          (one_mul _).symm
      _ ≤ |(n : ℚ)| * 2 ^ q := mul_le_mul h1 h2 (by positivity) (by positivity)
  cases tininess with
  | beforeRounding =>
    simp only [FlagSpec.tininessMagnitude] at hsmall
    exact absurd hmag (not_le.mpr hsmall)
  | afterRounding =>
    simp only [FlagSpec.tininessMagnitude,
      FlagSpec.roundUnbounded_of_representable _ _ hrep64] at hsmall
    exact absurd hmag (not_le.mpr hsmall)

/-- Widening binary32 to binary64 never flushes the result: no binary32 value is
tiny in binary64. -/
theorem flushSign?_convert_binary32_binary64 (p : Profile) (mode : RoundingMode)
    (x : Bits .binary32) :
    p.flushSign? .binary64 mode (FlagSpec.convertOutcome x.datum) = none := by
  unfold Profile.flushSign?
  split
  · cases hd : x.datum with
    | nan s => cases s <;> simp [FlagSpec.convertOutcome]
    | infinity s => simp [FlagSpec.convertOutcome]
    | finite s v =>
      have hrep : FlagSpec.Representable Format.binary32 v :=
        FlagSpec.decode_finite_representable Format.binary32 x.toNat hd
      simp [FlagSpec.convertOutcome, not_tiny_binary64_of_binary32 p.tininess mode hrep]
  · rfl

/-! ## WebAssembly's relations in `Admits` form -/

section Relations32

variable (x y r z : BitVec 32)

theorem nanRelation32_iff (c : Prop) [Decidable c] (cb : Bool) (hc : c ↔ cb = true) :
    (if (asF32 r).IsNaN then (if c then (asF32 z).IsCanonicalNaN else (asF32 z).IsArithmeticNaN)
      else asF32 z = asF32 r) ↔ Admits (fmt := .binary32) cb r z := by
  unfold Admits
  by_cases hr : Bits.isNaN (fmt := .binary32) r = true
  · have hr' : (asF32 r).IsNaN := (isNaN32 r).mpr hr
    simp only [hr', hr, ↓reduceIte]
    by_cases hcb : cb = true
    · simp only [hc.mpr hcb, hcb, ↓reduceIte]
      exact isCanonicalNaN32 z
    · have : ¬c := fun h => hcb (hc.mp h)
      simp only [this, hcb, ↓reduceIte, Bool.false_eq_true]
      exact isArithmeticNaN32 z
  · have hr' : ¬(asF32 r).IsNaN := fun h => hr ((isNaN32 r).mp h)
    simp only [hr', hr, ↓reduceIte, Bool.false_eq_true]
    exact asF32_inj z r

theorem binaryResult32_iff (eval : F32 → F32 → F32) (h : eval (asF32 x) (asF32 y) = asF32 r) :
    F32.binaryResult eval (asF32 x) (asF32 y) (asF32 z) ↔
      Admits (fmt := .binary32) (allCanonical (fmt := .binary32) [x, y]) r z := by
  unfold F32.binaryResult
  rw [h]
  apply nanRelation32_iff
  simp [F32.canonicalNaNInputs, allCanonical, isNonNaNOrCanonicalNaN32]

theorem unaryResult32_iff (eval : F32 → F32) (h : eval (asF32 x) = asF32 r) :
    F32.unaryResult eval (asF32 x) (asF32 z) ↔
      Admits (fmt := .binary32) (allCanonical (fmt := .binary32) [x]) r z := by
  unfold F32.unaryResult
  rw [h]
  apply nanRelation32_iff
  simp [allCanonical, isNonNaNOrCanonicalNaN32]

end Relations32

section Relations64

variable (x y r z : BitVec 64)

theorem nanRelation64_iff (c : Prop) [Decidable c] (cb : Bool) (hc : c ↔ cb = true) :
    (if (asF64 r).IsNaN then (if c then (asF64 z).IsCanonicalNaN else (asF64 z).IsArithmeticNaN)
      else asF64 z = asF64 r) ↔ Admits (fmt := .binary64) cb r z := by
  unfold Admits
  by_cases hr : Bits.isNaN (fmt := .binary64) r = true
  · have hr' : (asF64 r).IsNaN := (isNaN64 r).mpr hr
    simp only [hr', hr, ↓reduceIte]
    by_cases hcb : cb = true
    · simp only [hc.mpr hcb, hcb, ↓reduceIte]
      exact isCanonicalNaN64 z
    · have : ¬c := fun h => hcb (hc.mp h)
      simp only [this, hcb, ↓reduceIte, Bool.false_eq_true]
      exact isArithmeticNaN64 z
  · have hr' : ¬(asF64 r).IsNaN := fun h => hr ((isNaN64 r).mp h)
    simp only [hr', hr, ↓reduceIte, Bool.false_eq_true]
    exact asF64_inj z r

theorem binaryResult64_iff (eval : F64 → F64 → F64) (h : eval (asF64 x) (asF64 y) = asF64 r) :
    F64.binaryResult eval (asF64 x) (asF64 y) (asF64 z) ↔
      Admits (fmt := .binary64) (allCanonical (fmt := .binary64) [x, y]) r z := by
  unfold F64.binaryResult
  rw [h]
  apply nanRelation64_iff
  simp [F64.canonicalNaNInputs, allCanonical, isNonNaNOrCanonicalNaN64]

theorem unaryResult64_iff (eval : F64 → F64) (h : eval (asF64 x) = asF64 r) :
    F64.unaryResult eval (asF64 x) (asF64 z) ↔
      Admits (fmt := .binary64) (allCanonical (fmt := .binary64) [x]) r z := by
  unfold F64.unaryResult
  rw [h]
  apply nanRelation64_iff
  simp [allCanonical, isNonNaNOrCanonicalNaN64]

end Relations64

/-! ## Arithmetic, square root and integral rounding -/

section Arithmetic

variable (p : Profile)

/-- The binary arithmetic operations WebAssembly shares with every profile. -/
def wasmBinaryCore? : FloatBinOp → Option ArithOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | _ => none

/-- The static rounding direction of WebAssembly's integral rounding operators. -/
def wasmIntegralMode? : FloatUnOp → Option RoundingMode
  | .ceil => some .towardPositive
  | .floor => some .towardNegative
  | .trunc => some .towardZero
  | .nearest => some .nearestTiesToEven
  | _ => none

/-- binary32 `add`, `sub`, `mul`, `div`: every profile's result, in
round-to-nearest-even without flushing, is one WebAssembly admits. -/
theorem binary_admitted32 (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (op : FloatBinOp) (core : ArithOp)
    (hop : wasmBinaryCore? op = some core) (x y : BitVec 32) :
    floatBinOpRel .f32 op x y (p.binary .binary32 core .nearestTiesToEven x y).value := by
  cases op <;> simp only [wasmBinaryCore?, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals
    show F32.binaryResult _ (asF32 x) (asF32 y) (asF32 _)
    rw [binaryResult32_iff x y (CoreOp.round .binary32 .nearestTiesToEven _) _ _ ?_]
    · exact binary_admits p (fmt := .binary32) _ _ x y hin hout rfl
  · simp only [floatBinOp32]
    rw [← F32.addWith_rne]
    simp only [F32.addWith, model_unpack32]
    rfl
  · simp only [floatBinOp32]
    rw [← F32.subWith_rne]
    simp only [F32.subWith, model_unpack32]
    rfl
  · simp only [floatBinOp32]
    rw [← F32.mulWith_rne]
    simp only [F32.mulWith, model_unpack32]
    rfl
  · simp only [floatBinOp32]
    rw [← F32.divWith_rne]
    simp only [F32.divWith, model_unpack32]
    rfl

/-- binary64 `add`, `sub`, `mul`, `div`. -/
theorem binary_admitted64 (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (op : FloatBinOp) (core : ArithOp)
    (hop : wasmBinaryCore? op = some core) (x y : BitVec 64) :
    floatBinOpRel .f64 op x y (p.binary .binary64 core .nearestTiesToEven x y).value := by
  cases op <;> simp only [wasmBinaryCore?, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals
    show F64.binaryResult _ (asF64 x) (asF64 y) (asF64 _)
    rw [binaryResult64_iff x y (CoreOp.round .binary64 .nearestTiesToEven _) _ _ ?_]
    · exact binary_admits p (fmt := .binary64) _ _ x y hin hout rfl
  · simp only [floatBinOp64]
    rw [← F64.addWith_rne]
    simp only [F64.addWith, model_unpack64]
    rfl
  · simp only [floatBinOp64]
    rw [← F64.subWith_rne]
    simp only [F64.subWith, model_unpack64]
    rfl
  · simp only [floatBinOp64]
    rw [← F64.mulWith_rne]
    simp only [F64.mulWith, model_unpack64]
    rfl
  · simp only [floatBinOp64]
    rw [← F64.divWith_rne]
    simp only [F64.divWith, model_unpack64]
    rfl

/-- binary32 `add`. -/
theorem add_admitted32 (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (x y : BitVec 32) :
    floatBinOpRel .f32 .add x y (p.add .binary32 .nearestTiesToEven x y).value :=
  binary_admitted32 p hin hout .add _ rfl x y

/-- binary64 `add`. -/
theorem add_admitted64 (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (x y : BitVec 64) :
    floatBinOpRel .f64 .add x y (p.add .binary64 .nearestTiesToEven x y).value :=
  binary_admitted64 p hin hout .add _ rfl x y

/-- binary32 `sqrt`. -/
theorem sqrt_admitted32 (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (x : BitVec 32) :
    floatUnOpRel .f32 .sqrt x (p.sqrt .binary32 .nearestTiesToEven x).value := by
  show F32.unaryResult F32.sqrt (asF32 x) (asF32 _)
  rw [unaryResult32_iff x
    (CoreOp.round .binary32 .nearestTiesToEven (.sqrt (Bits.value (fmt := .binary32) x))) _ _ ?_]
  · exact sqrt_admits p (fmt := .binary32) _ x hin hout
  · rw [← F32.sqrtWith_rne]
    simp only [F32.sqrtWith, model_unpack32]
    rfl

/-- binary64 `sqrt`. -/
theorem sqrt_admitted64 (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (x : BitVec 64) :
    floatUnOpRel .f64 .sqrt x (p.sqrt .binary64 .nearestTiesToEven x).value := by
  show F64.unaryResult F64.sqrt (asF64 x) (asF64 _)
  rw [unaryResult64_iff x
    (CoreOp.round .binary64 .nearestTiesToEven (.sqrt (Bits.value (fmt := .binary64) x))) _ _ ?_]
  · exact sqrt_admits p (fmt := .binary64) _ x hin hout
  · rw [← F64.sqrtWith_rne]
    simp only [F64.sqrtWith, model_unpack64]
    rfl

/-- binary32 `ceil`, `floor`, `trunc`, `nearest` in their static direction. No
rounding-mode or result-flushing hypothesis is needed. -/
theorem roundToIntegral_admitted32 (hin : p.flushInputs = false) (op : FloatUnOp)
    (mode : RoundingMode) (hop : wasmIntegralMode? op = some mode) (signalInexact : Bool)
    (x : BitVec 32) :
    floatUnOpRel .f32 op x (p.roundToIntegral .binary32 mode signalInexact x).value := by
  have hround : F32.roundIntegral mode (asF32 x) =
      asF32 (Rounding.integralRounded .binary32 mode (Bits.value (fmt := .binary32) x)) := by
    simp only [F32.roundIntegral, model_unpack32]
    rfl
  have hcanon : Bits.isNonNaNOrCanonicalNaN (fmt := .binary32)
      (Rounding.integralRounded .binary32 mode (Bits.value (fmt := .binary32) x)) = true := by
    have := F32.roundIntegral_isCanonicalized mode (asF32 x)
    rw [hround] at this
    exact (isNonNaNOrCanonicalNaN32 _).mp this
  cases op <;> simp only [wasmIntegralMode?, Option.some.injEq, reduceCtorEq] at hop <;>
    subst hop <;>
    · show F32.unaryResult (F32.roundIntegral _) (asF32 x) (asF32 _)
      rw [unaryResult32_iff x _ _ _ hround]
      exact roundToIntegral_admits p (fmt := .binary32) _ signalInexact x hin hcanon

/-- binary64 `ceil`, `floor`, `trunc`, `nearest`. -/
theorem roundToIntegral_admitted64 (hin : p.flushInputs = false) (op : FloatUnOp)
    (mode : RoundingMode) (hop : wasmIntegralMode? op = some mode) (signalInexact : Bool)
    (x : BitVec 64) :
    floatUnOpRel .f64 op x (p.roundToIntegral .binary64 mode signalInexact x).value := by
  have hround : F64.roundIntegral mode (asF64 x) =
      asF64 (Rounding.integralRounded .binary64 mode (Bits.value (fmt := .binary64) x)) := by
    simp only [F64.roundIntegral, model_unpack64]
    rfl
  have hcanon : Bits.isNonNaNOrCanonicalNaN (fmt := .binary64)
      (Rounding.integralRounded .binary64 mode (Bits.value (fmt := .binary64) x)) = true := by
    have := F64.roundIntegral_isCanonicalized mode (asF64 x)
    rw [hround] at this
    exact (isNonNaNOrCanonicalNaN64 _).mp this
  cases op <;> simp only [wasmIntegralMode?, Option.some.injEq, reduceCtorEq] at hop <;>
    subst hop <;>
    · show F64.unaryResult (F64.roundIntegral _) (asF64 x) (asF64 _)
      rw [unaryResult64_iff x _ _ _ hround]
      exact roundToIntegral_admits p (fmt := .binary64) _ signalInexact x hin hcanon

/-- `f64.promote_f32`: admitted for every profile without input flushing. Result
flushing never applies (`flushSign?_convert_binary32_binary64`). -/
theorem promote_admitted (hin : p.flushInputs = false) (x : BitVec 32) :
    convertRel .promote x (.ok (p.convert .binary32 .binary64 .nearestTiesToEven x).value) :=
        by
  simp only [convertRel]
  have h : (asF32 x).toF64 = asF64 (CoreOp.round .binary64 .nearestTiesToEven (.convert
      (Bits.value (fmt := .binary32) x))) := by
    simp only [F32.toF64, model_unpack32]
    rfl
  rw [h]
  rw [nanRelation64_iff _ _ _ (Bits.isNonNaNOrCanonicalNaN (fmt := .binary32) x)
    (isNonNaNOrCanonicalNaN32 x)]
  exact convert_admits_of_noFlush p (src := .binary32) _ x hin
    (flushSign?_convert_binary32_binary64 p _ x)

/-- `f32.demote_f64`: admitted for every profile without flushing. -/
theorem demote_admitted (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (x : BitVec 64) :
    convertRel .demote x (.ok (p.convert .binary64 .binary32 .nearestTiesToEven x).value) := by
  simp only [convertRel]
  have h : (asF64 x).toF32 = asF32 (CoreOp.round .binary32 .nearestTiesToEven (.convert
      (Bits.value (fmt := .binary64) x))) := by
    simp only [F64.toF32, model_unpack64]
    rfl
  rw [h]
  rw [nanRelation32_iff _ _ _ (Bits.isNonNaNOrCanonicalNaN (fmt := .binary64) x)
    (isNonNaNOrCanonicalNaN64 x)]
  exact convert_admits p (src := .binary64) _ x hin hout

end Arithmetic

/-! ## Minimum and maximum -/

/-- `UnpackedFloat.compare` is antisymmetric. -/
theorem compare_swap (a b : UnpackedFloat) :
    a.compare b = (b.compare a).map Ordering.swap := by
  rcases a with ⟨sa⟩ | _ | ⟨sa⟩ | ⟨sa, ma, ea, ha⟩ <;>
  rcases b with ⟨sb⟩ | _ | ⟨sb⟩ | ⟨sb, mb, eb, hb⟩ <;>
  (try cases sa) <;> (try cases sb) <;>
  first
    | rfl
    | simp [UnpackedFloat.compare, Ordering.swap_then, ← Std.OrientedOrd.eq_swap]

/-- Values that compare equal are equal or are two zeros. -/
theorem compare_eq_cases {a b : UnpackedFloat} (h : a.compare b = some .eq) :
    a = b ∨ ∃ s t, a = .zero s ∧ b = .zero t := by
  rcases a with ⟨sa⟩ | _ | ⟨sa⟩ | ⟨sa, ma, ea, ha⟩ <;>
  rcases b with ⟨sb⟩ | _ | ⟨sb⟩ | ⟨sb, mb, eb, hb⟩ <;>
  (try cases sa) <;> (try cases sb) <;>
  simp_all [UnpackedFloat.compare, Ordering.then_eq_eq, Ordering.swap_eq_eq]

/-- Two non-NaN values are ordered. -/
theorem compare_isSome {a b : UnpackedFloat} (ha : a ≠ .notANumber)
    (hb : b ≠ .notANumber) : (a.compare b).isSome := by
  rcases a with ⟨sa⟩ | _ | ⟨sa⟩ | ⟨sa, ma, ea, ha⟩ <;>
  rcases b with ⟨sb⟩ | _ | ⟨sb⟩ | ⟨sb, mb, eb, hb⟩ <;>
  (try cases sa) <;> (try cases sb) <;>
  simp_all [UnpackedFloat.compare]

namespace Bits

variable {fmt : Format}

theorem pack_value {b : Bits fmt} (h : b.isNaN = false) : pack fmt b.value = b := by
  unfold value
  rw [Conformance.pack_unpack]
  split
  next hc =>
    exfalso
    simp [isNaN, hc.1, hc.2] at h
  next => rfl

theorem value_injective {x y : Bits fmt} (hx : x.isNaN = false) (hy : y.isNaN = false)
    (h : x.value = y.value) : x = y := by
  rw [← pack_value hx, ← pack_value hy, h]

theorem value_ne_notANumber {b : Bits fmt} (h : b.isNaN = false) : b.value ≠ .notANumber := by
  intro hv
  rw [(value_eq_notANumber_iff b).mp hv] at h
  cases h

theorem eq_packedZero_of_value {b : Bits fmt} {s : Sign} (h : b.value = .zero s) :
    b = packedZero fmt s := by
  have hn : b.isNaN = false := by
    cases hb : b.isNaN
    · rfl
    · rw [(value_eq_notANumber_iff b).mpr hb] at h
      cases h
  rw [← pack_value hn, h]
  rfl

@[simp] theorem value_packedZero (fmt : Format) (s : Sign) :
    Bits.value (fmt := fmt) (packedZero fmt s) = .zero s :=
  Conformance.unpack_packedZero fmt s

@[simp] theorem signBit_packedZero (fmt : Format) (s : Sign) :
    Bits.signBit (fmt := fmt) (packedZero fmt s) = (s == .negative) := by
  unfold signBit packedZero
  rw [Conformance.unpackSign_packComponents]
  cases s <;> rfl

theorem packedZero_inj (fmt : Format) {s t : Sign} :
    (packedZero fmt s : Bits fmt) = packedZero fmt t ↔ s = t := by
  constructor
  · intro h
    have := congrArg (Bits.signBit (fmt := fmt)) h
    simp only [signBit_packedZero] at this
    cases s <;> cases t <;> simp_all
  · rintro rfl
    rfl

theorem isSignalingNaN_eq {b : Bits fmt} (h : b.isNaN = true) :
    b.isSignalingNaN = !b.isQuietNaN := by
  simp [isSignalingNaN, isQuietNaN, h]

end Bits

namespace Profile

variable {fmt : Format}

theorem numericLt_of_nan_left {x : Bits fmt} (y : Bits fmt) (h : x.isNaN = true) :
    numericLt x y = false := by
  simp [numericLt, (Bits.value_eq_notANumber_iff x).mpr h, UnpackedFloat.compare]

theorem numericLt_of_nan_right (x : Bits fmt) {y : Bits fmt} (h : y.isNaN = true) :
    numericLt x y = false := by
  simp only [numericLt, (Bits.value_eq_notANumber_iff y).mpr h]
  cases x.value <;> rfl

theorem numericMinMax_eq_or (isMax : Bool) (x y : Bits fmt) :
    numericMinMax isMax x y = x ∨ numericMinMax isMax x y = y := by
  unfold numericMinMax
  split
  · split <;> simp
  · split <;> simp

end Profile

/-- WebAssembly's deterministic `fmin` (`isMax = false`) or `fmax` reference. -/
def wasmMinMax {fmt : Format} (isMax : Bool) (x y : Bits fmt) : Bits fmt :=
  if x.isNaN || y.isNaN then packedNaN fmt else Profile.numericMinMax isMax x y

theorem wasmMinMax_isNaN {fmt : Format} (isMax : Bool) (x y : Bits fmt) :
    (wasmMinMax isMax x y).isNaN = (x.isNaN || y.isNaN) := by
  unfold wasmMinMax
  split
  next h => rw [Bits.isNaN_packedNaN, h]
  next h =>
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at h
    rcases Profile.numericMinMax_eq_or isMax x y with e | e <;> rw [e] <;> simp [h]

/-- When a min/max rule's result agrees with WebAssembly's permitted results.
`minimum` always does. x86 `MINSS`/`MAXSS` does when the second operand is a quiet
NaN, or when neither operand is a NaN and the operands are not `(-0, +0)` for
minimum or `(+0, -0)` for maximum. `minimumNumber` does when both or neither
operand is a NaN. `minNum` does unless exactly one operand is a quiet NaN. -/
def MinMaxRule.agreesWithWasm {fmt : Format} (rule : MinMaxRule) (isMax : Bool) (x y : Bits fmt) :
    Bool :=
  match rule with
  | .minimum => true
  | .x86 =>
    if y.isNaN then y.isQuietNaN
    else !x.isNaN && !(x == packedZero fmt (if isMax then .positive else .negative) &&
      y == packedZero fmt (if isMax then .negative else .positive))
  | .minimumNumber => x.isNaN == y.isNaN
  | .minNum => !((x.isQuietNaN && !y.isNaN) || (y.isQuietNaN && !x.isNaN))

private theorem admits_iff_eq {fmt : Format} {c : Bool} {reference result : Bits fmt}
    (h : reference.isNaN = false) : Admits c reference result ↔ result = reference := by
  unfold Admits
  simp [h]

private theorem not_admits {fmt : Format} {c : Bool} {reference result : Bits fmt}
    (h : reference.isNaN = true) (hr : result.isNaN = false) : ¬Admits c reference result := by
  unfold Admits
  simp only [h, ↓reduceIte]
  split
  · intro hc
    rw [Bits.isNaN_of_isCanonicalNaN hc] at hr
    cases hr
  · intro hc
    rw [Bits.isNaN_of_isQuietNaN hc] at hr
    cases hr

/-- x86 min/max on two non-NaN operands equals WebAssembly's exactly away from
the signed-zero pair where x86 returns the second operand. -/
private theorem x86_numeric_iff {fmt : Format} (isMax : Bool) {x y : Bits fmt}
    (hx : x.isNaN = false) (hy : y.isNaN = false) :
    (if (if isMax then Profile.numericLt y x else Profile.numericLt x y) then x else y) =
        Profile.numericMinMax isMax x y ↔
      ¬(x = packedZero fmt (if isMax then .positive else .negative) ∧
        y = packedZero fmt (if isMax then .negative else .positive)) := by
  have hsome := compare_isSome (Bits.value_ne_notANumber hx) (Bits.value_ne_notANumber hy)
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
  have hswap : y.value.compare x.value = some o.swap := by
    rw [compare_swap, ho]
    rfl
  have hzeros : ∀ s t : Sign, x = packedZero fmt s → y = packedZero fmt t → o = .eq := by
    intro s t h1 h2
    rw [h1, h2, Bits.value_packedZero, Bits.value_packedZero] at ho
    simp only [UnpackedFloat.compare, Option.some.injEq] at ho
    exact ho.symm
  unfold Profile.numericMinMax Profile.numericEq
  simp only [Profile.numericLt, ho, hswap]
  cases o with
  | lt =>
    cases isMax <;> simp [Ordering.swap] <;> intro h1 h2 <;> exact absurd (hzeros _ _ h1 h2) (by
        decide)
  | gt =>
    cases isMax <;> simp [Ordering.swap] <;> intro h1 h2 <;> exact absurd (hzeros _ _ h1 h2) (by
        decide)
  | eq =>
    rcases compare_eq_cases ho with hv | ⟨sx, sy, hsx, hsy⟩
    · have hxy := Bits.value_injective hx hy hv
      subst hxy
      simp only [Ordering.swap, ite_self, true_iff]
      rintro ⟨h1, h2⟩
      have := h1.symm.trans h2
      rw [Bits.packedZero_inj] at this
      cases isMax <;> cases this
    · have ex := Bits.eq_packedZero_of_value hsx
      have ey := Bits.eq_packedZero_of_value hsy
      subst ex ey
      simp only [Bits.signBit_packedZero, Bits.packedZero_inj, Ordering.swap]
      cases isMax <;> cases sx <;> cases sy <;> simp [Bits.packedZero_inj]

section MinMaxValues

variable (p : Profile) (hin : p.flushInputs = false) {fmt : Format} (isMax : Bool) (x y : Bits fmt)
include hin

theorem minMaxWith_minimum_value :
    (p.minMaxWith .minimum isMax x y).value =
      if x.isNaN || y.isNaN then p.pickNaN [x, y] else Profile.numericMinMax isMax x y := by
  simp only [Profile.minMaxWith, Profile.flushInput_of_false p _ hin,
    Profile.nanOrElse, List.any_cons, List.any_nil, Bool.or_false]

theorem minMaxWith_minimumNumber_value :
    (p.minMaxWith .minimumNumber isMax x y).value =
      if x.isNaN && y.isNaN then p.pickNaN [x, y] else if x.isNaN then y else if y.isNaN then x
      else Profile.numericMinMax isMax x y := by
  simp only [Profile.minMaxWith, Profile.flushInput_of_false p _ hin]

theorem minMaxWith_minNum_value :
    (p.minMaxWith .minNum isMax x y).value =
      if x.isSignalingNaN || y.isSignalingNaN || (x.isNaN && y.isNaN) then p.pickNaN [x, y]
      else if x.isNaN then y else if y.isNaN then x else Profile.numericMinMax isMax x y := by
  simp only [Profile.minMaxWith, Profile.flushInput_of_false p _ hin]

theorem minMaxWith_x86_value :
    (p.minMaxWith .x86 isMax x y).value =
      if (if isMax then Profile.numericLt y x else Profile.numericLt x y) then x else y := by
  simp only [Profile.minMaxWith, Profile.flushInput_of_false p _ hin]

end MinMaxValues

/-- Which min/max results WebAssembly admits, for every rule, profile and format. -/
theorem minMax_admits_iff (p : Profile) (hin : p.flushInputs = false) {fmt : Format}
    (rule : MinMaxRule) (isMax : Bool) (x y : Bits fmt) :
    Admits (allCanonical [x, y]) (wasmMinMax isMax x y) (p.minMaxWith rule isMax x y).value ↔
      rule.agreesWithWasm isMax x y = true := by
  have href := wasmMinMax_isNaN isMax x y
  have hnum : (x.isNaN || y.isNaN) = false →
      wasmMinMax isMax x y = Profile.numericMinMax isMax x y := by
    intro h
    simp [wasmMinMax, h]
  have hsig : ∀ b : Bits fmt, b.isNaN = false → b.isSignalingNaN = false := by
    intro b h
    simp [Bits.isSignalingNaN, h]
  have hquiet : ∀ b : Bits fmt, b.isNaN = false → b.isQuietNaN = false := by
    intro b h
    simp [Bits.isQuietNaN, h]
  cases rule with
  | minimum =>
    rw [minMaxWith_minimum_value p hin]
    simp only [MinMaxRule.agreesWithWasm, iff_true]
    cases h : (x.isNaN || y.isNaN)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← hnum h]
      exact admits_of_not_nan _ (by rw [href, h])
    · simp only [↓reduceIte]
      exact pickNaN_admits p [x, y] (by rw [href, h])
  | minimumNumber =>
    rw [minMaxWith_minimumNumber_value p hin]
    simp only [MinMaxRule.agreesWithWasm]
    cases hx : x.isNaN <;> cases hy : y.isNaN
    · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, iff_true]
      rw [← hnum (by simp [hx, hy])]
      exact admits_of_not_nan _ (by simp [href, hx, hy])
    · have hr : (wasmMinMax isMax x y).isNaN = true := by simp [href, hy]
      simp only [Bool.and_true, Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun h => absurd h (not_admits hr hx), fun h => by simp at h⟩
    · have hr : (wasmMinMax isMax x y).isNaN = true := by simp [href, hx]
      simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun h => absurd h (not_admits hr hy), fun h => by simp at h⟩
    · have hr : (wasmMinMax isMax x y).isNaN = true := by simp [href, hx]
      simp only [Bool.and_self, ↓reduceIte, beq_self_eq_true, iff_true]
      exact pickNaN_admits p [x, y] hr
  | minNum =>
    rw [minMaxWith_minNum_value p hin]
    simp only [MinMaxRule.agreesWithWasm]
    cases hx : x.isNaN <;> cases hy : y.isNaN
    · simp only [hsig x hx, hsig y hy, hquiet x hx, hquiet y hy,
        Bool.or_false, Bool.not_false, Bool.and_true,
        Bool.and_self, Bool.false_eq_true, ↓reduceIte, iff_true]
      rw [← hnum (by simp [hx, hy])]
      exact admits_of_not_nan _ (by simp [href, hx, hy])
    · have hr : (wasmMinMax isMax x y).isNaN = true := by simp [href, hy]
      rw [Bits.isSignalingNaN_eq hy]
      cases hq : y.isQuietNaN
      · simp only [hsig x hx, hquiet x hx, Bool.or_false,
          Bool.not_false, Bool.not_true, Bool.and_true,
          Bool.or_true, Bool.and_self, ↓reduceIte, iff_true]
        exact pickNaN_admits p [x, y] hr
      · simp only [hsig x hx, hquiet x hx, Bool.or_false,
          Bool.not_false, Bool.not_true, Bool.and_true,
          Bool.or_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte, iff_false]
        exact not_admits hr hx
    · have hr : (wasmMinMax isMax x y).isNaN = true := by simp [href, hx]
      rw [Bits.isSignalingNaN_eq hx]
      cases hq : x.isQuietNaN
      · simp only [hsig y hy, hquiet y hy, Bool.and_false, Bool.or_false,
          Bool.not_false, Bool.not_true, Bool.and_true,
          Bool.and_self, ↓reduceIte, iff_true]
        exact pickNaN_admits p [x, y] hr
      · simp only [hsig y hy, hquiet y hy, Bool.and_false, Bool.or_false,
          Bool.not_false, Bool.not_true,
          Bool.and_self, Bool.false_eq_true, ↓reduceIte, iff_false]
        exact not_admits hr hy
    · have hr : (wasmMinMax isMax x y).isNaN = true := by simp [href, hx]
      simp only [Bool.and_false, Bool.or_false, Bool.not_false,
          Bool.not_true, Bool.or_true, Bool.and_self,
          ↓reduceIte, iff_true]
      exact pickNaN_admits p [x, y] hr
  | x86 =>
    rw [minMaxWith_x86_value p hin]
    simp only [MinMaxRule.agreesWithWasm]
    cases hy : y.isNaN
    · cases hx : x.isNaN
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and,
          Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        rw [admits_iff_eq (by simp [href, hx, hy]), hnum (by simp [hx, hy]),
          x86_numeric_iff isMax hx hy]
        tauto
      · have hlt1 := Profile.numericLt_of_nan_left y hx
        have hlt2 := Profile.numericLt_of_nan_right y hx
        simp only [hlt1, hlt2, Bool.false_eq_true, ↓reduceIte, ite_self, Bool.not_true,
          Bool.false_and, iff_false]
        exact not_admits (by simp [href, hx]) hy
    · have hlt1 := Profile.numericLt_of_nan_left x hy
      have hlt2 := Profile.numericLt_of_nan_right x hy
      have hr : (wasmMinMax isMax x y).isNaN = true := by simp [href, hy]
      simp only [hlt1, hlt2, Bool.false_eq_true, ↓reduceIte, ite_self]
      unfold Admits
      simp only [hr, ↓reduceIte]
      split
      next hc =>
        have hyc : y.isCanonicalNaN = true := by
          simp only [allCanonical, List.all_cons, List.all_nil, Bool.and_true,
            Bool.and_eq_true] at hc
          simpa [Bits.isNonNaNOrCanonicalNaN, hy] using hc.2
        simp [hyc, Bits.isQuietNaN_of_isCanonicalNaN hyc]
      next => rfl

section Bridge32

variable (x y : BitVec 32)

theorem isNaN_eq32 : (asF32 x).isNaN = Bits.isNaN (fmt := .binary32) x := by
  cases h : Bits.isNaN (fmt := .binary32) x <;> simp [F32.isNaN, isNaN32, h]

theorem equal32 : F32.equal (asF32 x) (asF32 y) = Profile.numericEq (fmt := .binary32) x y := by
  unfold F32.equal
  show Float32.Model.beq (asF32 x).model (asF32 y).model = _
  unfold Float32.Model.beq
  rw [model_unpack32, model_unpack32]
  rfl

theorem lessThan32 :
    F32.lessThan (asF32 x) (asF32 y) = Profile.numericLt (fmt := .binary32) x y := by
  unfold F32.lessThan
  show decide (Float32.Model.lt (asF32 x).model (asF32 y).model = true) = _
  rw [Bool.decide_eq_true]
  unfold Float32.Model.lt
  rw [model_unpack32, model_unpack32]
  rfl

theorem lessEqual32 : F32.lessEqual (asF32 x) (asF32 y) =
    ((Bits.value (fmt := .binary32) x).compare (Bits.value (fmt := .binary32) y)).any (·.isLE) := by
  unfold F32.lessEqual Float32.Model.le
  rw [model_unpack32, model_unpack32]
  rfl

theorem minimum32 : F32.minimum (asF32 x) (asF32 y) = asF32 (wasmMinMax (fmt := .binary32) false x
    y) := by
  unfold F32.minimum wasmMinMax Profile.numericMinMax
  rw [isNaN_eq32, isNaN_eq32, equal32, lessThan32, signBit32]
  by_cases h1 : (Bits.isNaN (fmt := .binary32) x || Bits.isNaN (fmt := .binary32) y) = true
  · simp only [h1, ↓reduceIte]
    rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases Profile.numericEq (fmt := .binary32) x y <;> cases Bits.signBit (fmt := .binary32) x <;>
      cases Profile.numericLt (fmt := .binary32) x y <;> rfl

theorem maximum32 : F32.maximum (asF32 x) (asF32 y) = asF32 (wasmMinMax (fmt := .binary32) true x
    y) := by
  unfold F32.maximum wasmMinMax Profile.numericMinMax
  rw [isNaN_eq32, isNaN_eq32, equal32, lessThan32, signBit32]
  by_cases h1 : (Bits.isNaN (fmt := .binary32) x || Bits.isNaN (fmt := .binary32) y) = true
  · simp only [h1, ↓reduceIte]
    rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases Profile.numericEq (fmt := .binary32) x y <;> cases Bits.signBit (fmt := .binary32) x <;>
      cases Profile.numericLt (fmt := .binary32) x y <;> rfl

end Bridge32

section Bridge64

variable (x y : BitVec 64)

theorem isNaN_eq64 : (asF64 x).isNaN = Bits.isNaN (fmt := .binary64) x := by
  cases h : Bits.isNaN (fmt := .binary64) x <;> simp [F64.isNaN, isNaN64, h]

theorem equal64 : F64.equal (asF64 x) (asF64 y) = Profile.numericEq (fmt := .binary64) x y := by
  unfold F64.equal
  show Float.Model.beq (asF64 x).model (asF64 y).model = _
  unfold Float.Model.beq
  rw [model_unpack64, model_unpack64]
  rfl

theorem lessThan64 :
    F64.lessThan (asF64 x) (asF64 y) = Profile.numericLt (fmt := .binary64) x y := by
  unfold F64.lessThan
  show decide (Float.Model.lt (asF64 x).model (asF64 y).model = true) = _
  rw [Bool.decide_eq_true]
  unfold Float.Model.lt
  rw [model_unpack64, model_unpack64]
  rfl

theorem lessEqual64 : F64.lessEqual (asF64 x) (asF64 y) =
    ((Bits.value (fmt := .binary64) x).compare (Bits.value (fmt := .binary64) y)).any (·.isLE) := by
  unfold F64.lessEqual Float.Model.le
  rw [model_unpack64, model_unpack64]
  rfl

theorem minimum64 : F64.minimum (asF64 x) (asF64 y) = asF64 (wasmMinMax (fmt := .binary64) false x
    y) := by
  unfold F64.minimum wasmMinMax Profile.numericMinMax
  rw [isNaN_eq64, isNaN_eq64, equal64, lessThan64, signBit64]
  by_cases h1 : (Bits.isNaN (fmt := .binary64) x || Bits.isNaN (fmt := .binary64) y) = true
  · simp only [h1, ↓reduceIte]
    rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases Profile.numericEq (fmt := .binary64) x y <;> cases Bits.signBit (fmt := .binary64) x <;>
      cases Profile.numericLt (fmt := .binary64) x y <;> rfl

theorem maximum64 : F64.maximum (asF64 x) (asF64 y) = asF64 (wasmMinMax (fmt := .binary64) true x
    y) := by
  unfold F64.maximum wasmMinMax Profile.numericMinMax
  rw [isNaN_eq64, isNaN_eq64, equal64, lessThan64, signBit64]
  by_cases h1 : (Bits.isNaN (fmt := .binary64) x || Bits.isNaN (fmt := .binary64) y) = true
  · simp only [h1, ↓reduceIte]
    rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases Profile.numericEq (fmt := .binary64) x y <;> cases Bits.signBit (fmt := .binary64) x <;>
      cases Profile.numericLt (fmt := .binary64) x y <;> rfl

end Bridge64

/-! ## WebAssembly `min` and `max` -/

section MinMaxWasm

variable (p : Profile) (hin : p.flushInputs = false)
include hin

/-- binary32 `min`/`max`: a profile's result under `rule` is admitted exactly when
`MinMaxRule.agreesWithWasm` holds. -/
theorem minMax_admitted_iff32 (rule : MinMaxRule) (isMax : Bool) (x y : BitVec 32) :
    floatBinOpRel .f32 (if isMax then .max else .min) x y
        (p.minMaxWith (fmt := .binary32) rule isMax x y).value ↔
      rule.agreesWithWasm (fmt := .binary32) isMax x y = true := by
  cases isMax
  · show F32.binaryResult F32.minimum (asF32 x) (asF32 y) (asF32 _) ↔ _
    rw [binaryResult32_iff x y _ _ _ (minimum32 x y)]
    exact minMax_admits_iff p hin (fmt := .binary32) rule false x y
  · show F32.binaryResult F32.maximum (asF32 x) (asF32 y) (asF32 _) ↔ _
    rw [binaryResult32_iff x y _ _ _ (maximum32 x y)]
    exact minMax_admits_iff p hin (fmt := .binary32) rule true x y

/-- binary64 `min`/`max`. -/
theorem minMax_admitted_iff64 (rule : MinMaxRule) (isMax : Bool) (x y : BitVec 64) :
    floatBinOpRel .f64 (if isMax then .max else .min) x y
        (p.minMaxWith (fmt := .binary64) rule isMax x y).value ↔
      rule.agreesWithWasm (fmt := .binary64) isMax x y = true := by
  cases isMax
  · show F64.binaryResult F64.minimum (asF64 x) (asF64 y) (asF64 _) ↔ _
    rw [binaryResult64_iff x y _ _ _ (minimum64 x y)]
    exact minMax_admits_iff p hin (fmt := .binary64) rule false x y
  · show F64.binaryResult F64.maximum (asF64 x) (asF64 y) (asF64 _) ↔ _
    rw [binaryResult64_iff x y _ _ _ (maximum64 x y)]
    exact minMax_admits_iff p hin (fmt := .binary64) rule true x y

/-- `MinMaxRule.minimum` (AArch64 `FMIN`/`FMAX`) always yields an admitted binary32 result. -/
theorem minimumRule_admitted32 (isMax : Bool) (x y : BitVec 32) :
    floatBinOpRel .f32 (if isMax then .max else .min) x y
      (p.minMaxWith (fmt := .binary32) .minimum isMax x y).value :=
  (minMax_admitted_iff32 p hin .minimum isMax x y).mpr rfl

/-- `MinMaxRule.minimum` always yields an admitted binary64 result. -/
theorem minimumRule_admitted64 (isMax : Bool) (x y : BitVec 64) :
    floatBinOpRel .f64 (if isMax then .max else .min) x y
      (p.minMaxWith (fmt := .binary64) .minimum isMax x y).value :=
  (minMax_admitted_iff64 p hin .minimum isMax x y).mpr rfl

end MinMaxWasm

/-! ## Integer conversions -/

section IntConversions

variable (p : Profile) (hin : p.flushInputs = false)
  (target : IntType) (sign : Wasm.Signedness)
include hin

/-- Every profile's truncating conversion agrees with WebAssembly `trunc` whenever
`trunc` does not trap; otherwise it yields the profile's `IntOverflowRule` result. -/
theorem toInt_eq_truncFloat32 (x : BitVec 32) :
    (p.toInt .binary32 (integerFormat target sign) .towardZero x).value =
      match truncFloat .f32 target sign x with
      | .ok v => v
      | .error _ => Profile.intOverflowResult p.intOverflow (integerFormat target sign)
          (Bits.value (fmt := .binary32) x) .towardZero := by
  simp only [Profile.toInt, Profile.flushInput_of_false p _ hin, truncFloat,
    unpackFloat, model_unpack32]
  cases Integer.fromFloat? (integerFormat target sign) (Bits.value (fmt := .binary32) x)
      .towardZero with
  | some n => rfl
  | none =>
    by_cases hn : (Bits.value (fmt := .binary32) x).isNaN = true
    · simp only [hn, ↓reduceIte]
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]

/-- binary64 truncating conversion against WebAssembly `trunc`. -/
theorem toInt_eq_truncFloat64 (x : BitVec 64) :
    (p.toInt .binary64 (integerFormat target sign) .towardZero x).value =
      match truncFloat .f64 target sign x with
      | .ok v => v
      | .error _ => Profile.intOverflowResult p.intOverflow (integerFormat target sign)
          (Bits.value (fmt := .binary64) x) .towardZero := by
  simp only [Profile.toInt, Profile.flushInput_of_false p _ hin, truncFloat,
    unpackFloat, model_unpack64]
  cases Integer.fromFloat? (integerFormat target sign) (Bits.value (fmt := .binary64) x)
      .towardZero with
  | some n => rfl
  | none =>
    by_cases hn : (Bits.value (fmt := .binary64) x).isNaN = true
    · simp only [hn, ↓reduceIte]
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]

/-- In-range agreement, for every profile: a non-trapping WebAssembly `trunc`
result is the profile's result. -/
theorem toInt_of_truncFloat_ok32 {x : BitVec 32} {v : IntValue target}
    (h : truncFloat .f32 target sign x = .ok v) :
    (p.toInt .binary32 (integerFormat target sign) .towardZero x).value = v := by
  rw [toInt_eq_truncFloat32 p hin target sign x, h]

/-- binary64 in-range agreement. -/
theorem toInt_of_truncFloat_ok64 {x : BitVec 64} {v : IntValue target}
    (h : truncFloat .f64 target sign x = .ok v) :
    (p.toInt .binary64 (integerFormat target sign) .towardZero x).value = v := by
  rw [toInt_eq_truncFloat64 p hin target sign x, h]

/-- `IntOverflowRule.saturateNaNToZero` (AArch64 `FCVTZS`/`FCVTZU`) equals WebAssembly
`trunc_sat` on every binary32 input. -/
theorem toInt_saturateNaNToZero_eq_truncSat32 (hrule : p.intOverflow = .saturateNaNToZero)
    (x : BitVec 32) :
    (p.toInt .binary32 (integerFormat target sign) .towardZero x).value =
      truncSatFloat .f32 target sign x := by
  simp only [Profile.toInt, Profile.flushInput_of_false p _ hin, truncSatFloat,
    unpackFloat, hrule]
  rw [model_unpack32]
  cases h : Integer.fromFloat? (integerFormat target sign) (Bits.value (fmt := .binary32) x)
      .towardZero with
  | some n => exact congrArg Integer.bits (Integer.fromFloatSaturating_agrees h).symm
  | none => rfl

/-- binary64 `trunc_sat` agreement for `saturateNaNToZero`. -/
theorem toInt_saturateNaNToZero_eq_truncSat64 (hrule : p.intOverflow = .saturateNaNToZero)
    (x : BitVec 64) :
    (p.toInt .binary64 (integerFormat target sign) .towardZero x).value =
      truncSatFloat .f64 target sign x := by
  simp only [Profile.toInt, Profile.flushInput_of_false p _ hin, truncSatFloat,
    unpackFloat, hrule]
  rw [model_unpack64]
  cases h : Integer.fromFloat? (integerFormat target sign) (Bits.value (fmt := .binary64) x)
      .towardZero with
  | some n => exact congrArg Integer.bits (Integer.fromFloatSaturating_agrees h).symm
  | none => rfl

/-- `IntOverflowRule.saturateNaNToMax` (RISC-V `FCVT`) equals WebAssembly `trunc_sat`
on every non-NaN binary32 input, and yields the maximum for NaN. -/
theorem toInt_saturateNaNToMax_eq32 (hrule : p.intOverflow = .saturateNaNToMax) (x : BitVec 32) :
    (p.toInt .binary32 (integerFormat target sign) .towardZero x).value =
      if Bits.isNaN (fmt := .binary32) x then
        (Integer.ofIntWrapping (integerFormat target sign) (integerFormat target
            sign).maxValue).bits
      else truncSatFloat .f32 target sign x := by
  simp only [Profile.toInt, Profile.flushInput_of_false p _ hin, truncSatFloat,
    unpackFloat, hrule]
  rw [model_unpack32, ← Bits.value_isNaN]
  cases h : Integer.fromFloat? (integerFormat target sign) (Bits.value (fmt := .binary32) x)
      .towardZero with
  | some n =>
    have hnan : (Bits.value (fmt := .binary32) x).isNaN = false := by
      cases hv : Bits.value (fmt := .binary32) x <;>
        simp_all [Integer.fromFloat?, Rounding.toInt?, UnpackedFloat.isNaN]
    simp only [hnan, Bool.false_eq_true, ↓reduceIte]
    exact congrArg Integer.bits (Integer.fromFloatSaturating_agrees h).symm
  | none => rfl

/-- binary64 form of `toInt_saturateNaNToMax_eq32`. -/
theorem toInt_saturateNaNToMax_eq64 (hrule : p.intOverflow = .saturateNaNToMax) (x : BitVec 64) :
    (p.toInt .binary64 (integerFormat target sign) .towardZero x).value =
      if Bits.isNaN (fmt := .binary64) x then
        (Integer.ofIntWrapping (integerFormat target sign) (integerFormat target
            sign).maxValue).bits
      else truncSatFloat .f64 target sign x := by
  simp only [Profile.toInt, Profile.flushInput_of_false p _ hin, truncSatFloat,
    unpackFloat, hrule]
  rw [model_unpack64, ← Bits.value_isNaN]
  cases h : Integer.fromFloat? (integerFormat target sign) (Bits.value (fmt := .binary64) x)
      .towardZero with
  | some n =>
    have hnan : (Bits.value (fmt := .binary64) x).isNaN = false := by
      cases hv : Bits.value (fmt := .binary64) x <;>
        simp_all [Integer.fromFloat?, Rounding.toInt?, UnpackedFloat.isNaN]
    simp only [hnan, Bool.false_eq_true, ↓reduceIte]
    exact congrArg Integer.bits (Integer.fromFloatSaturating_agrees h).symm
  | none => rfl

end IntConversions

/-- Integer-to-float conversion equals WebAssembly `convert` for every profile. -/
theorem ofInt_eq_convertInt32 (p : Profile) (source : IntType) (sign :
    Wasm.Signedness)
    (x : IntValue source) :
    convertInt source .f32 sign x =
      (p.ofInt .binary32 .nearestTiesToEven
        (match sign with | .signed => x.toInt | .unsigned => (x.toNat : Int))).value := by
  cases sign <;> rfl

/-- binary64 integer-to-float conversion. -/
theorem ofInt_eq_convertInt64 (p : Profile) (source : IntType) (sign :
    Wasm.Signedness)
    (x : IntValue source) :
    convertInt source .f64 sign x =
      (p.ofInt .binary64 .nearestTiesToEven
        (match sign with | .signed => x.toInt | .unsigned => (x.toNat : Int))).value := by
  cases sign <;> rfl

/-! ## Comparisons -/

/-- The IEEE predicate of each WebAssembly comparison. WebAssembly has no flags, so
the signaling choice only matters for the flags a profile reports. -/
def wasmPredicate : FloatRelOp → Predicate
  | .eq => Predicate.eqQuiet
  | .ne => Predicate.neQuiet
  | .lt => Predicate.ltSignaling
  | .gt => Predicate.gtSignaling
  | .le => Predicate.leSignaling
  | .ge => Predicate.geSignaling

private theorem compare_value (p : Profile) (hin : p.flushInputs = false) {fmt : Format}
    (P : Predicate) (x y : Bits fmt) :
    (p.comparePredicate P x y).value = P.eval (x.value.compare y.value) := by
  simp [Profile.comparePredicate, Profile.compare, Profile.flushInput_of_false p _ hin]

private theorem predicate_eval (op : FloatRelOp) (c : Option Ordering) (numericEq numericLt le :
    Bool)
    (heq : numericEq = (c == some .eq)) (hlt : numericLt = (c == some .lt))
    (hle : le = c.any (·.isLE)) (gt ge : Bool) (hgt : gt = (c.map Ordering.swap == some .lt))
    (hge : ge = (c.map Ordering.swap).any (·.isLE)) :
    (wasmPredicate op).eval c = match op with
      | .eq => numericEq | .ne => !numericEq | .lt => numericLt | .le => le
      | .gt => gt | .ge => ge := by
  subst heq hlt hle hgt hge
  rcases c with _ | ⟨_ | _ | _⟩ <;> cases op <;> rfl

/-- binary32 comparisons: every profile computes WebAssembly's result. -/
theorem comparePredicate_eq_floatRelOp32 (p : Profile) (hin : p.flushInputs = false)
    (op : FloatRelOp) (x y : BitVec 32) :
    bool32 (p.comparePredicate (fmt := .binary32) (wasmPredicate op) x y).value = floatRelOp .f32
        op x y := by
  show _ = bool32 (floatRelOp32 op (asF32 x) (asF32 y))
  rw [compare_value p hin]
  congr 1
  have hswap := compare_swap (Bits.value (fmt := .binary32) y)
    (Bits.value (fmt := .binary32) x)
  rw [predicate_eval op _ _ _ _ rfl rfl rfl
    (F32.lessThan (asF32 y) (asF32 x)) (F32.lessEqual (asF32 y) (asF32 x))
    (by rw [lessThan32]; unfold Profile.numericLt; rw [hswap])
    (by rw [lessEqual32, hswap])]
  cases op
  · exact (equal32 x y).symm
  · show _ = !F32.equal _ _
    rw [equal32]
    rfl
  · exact (lessThan32 x y).symm
  · rfl
  · exact (lessEqual32 x y).symm
  · rfl

/-- binary64 comparisons. -/
theorem comparePredicate_eq_floatRelOp64 (p : Profile) (hin : p.flushInputs = false)
    (op : FloatRelOp) (x y : BitVec 64) :
    bool32 (p.comparePredicate (fmt := .binary64) (wasmPredicate op) x y).value = floatRelOp .f64
        op x y := by
  show _ = bool32 (floatRelOp64 op (asF64 x) (asF64 y))
  rw [compare_value p hin]
  congr 1
  have hswap := compare_swap (Bits.value (fmt := .binary64) y)
    (Bits.value (fmt := .binary64) x)
  rw [predicate_eval op _ _ _ _ rfl rfl rfl
    (F64.lessThan (asF64 y) (asF64 x)) (F64.lessEqual (asF64 y) (asF64 x))
    (by rw [lessThan64]; unfold Profile.numericLt; rw [hswap])
    (by rw [lessEqual64, hswap])]
  cases op
  · exact (equal64 x y).symm
  · show _ = !F64.equal _ _
    rw [equal64]
    rfl
  · exact (lessThan64 x y).symm
  · rfl
  · exact (lessEqual64 x y).symm
  · rfl

/-! ## Corollaries for the concrete profiles

The statements take round-to-nearest-even as the direction passed to each
operation, which is what the instruction layer supplies when x86 MXCSR.RC,
RISC-V `frm` (or a static `rm`) or AArch64 FPCR.RMode selects it. The x86
statements hold for any MXCSR with DAZ and FZ clear, such as the power-on value
1F80H; the AArch64 statements for FPCR.FZ = 0, with either FPCR.DN. -/

section Concrete

/-- x86 SSE `ADDSS`/`SUBSS`/`MULSS`/`DIVSS` results are admitted by WebAssembly. -/
theorem x86_binary_admitted32 (c : MXCSRControl) (hdaz : c.denormalsAreZeros = false)
    (hfz : c.flushToZero = false) (op : FloatBinOp) (core : ArithOp)
    (hop : wasmBinaryCore? op = some core) (x y : BitVec 32) :
    floatBinOpRel .f32 op x y
      ((Profile.x86SSE c).binary .binary32 core .nearestTiesToEven x y).value :=
  binary_admitted32 _ hdaz hfz op core hop x y

/-- x86 SSE2 `ADDSD`/`SUBSD`/`MULSD`/`DIVSD` results are admitted by WebAssembly. -/
theorem x86_binary_admitted64 (c : MXCSRControl) (hdaz : c.denormalsAreZeros = false)
    (hfz : c.flushToZero = false) (op : FloatBinOp) (core : ArithOp)
    (hop : wasmBinaryCore? op = some core) (x y : BitVec 64) :
    floatBinOpRel .f64 op x y
      ((Profile.x86SSE c).binary .binary64 core .nearestTiesToEven x y).value :=
  binary_admitted64 _ hdaz hfz op core hop x y

/-- x86 `MINSS`/`MAXSS` agree with WebAssembly `fmin`/`fmax` exactly when the
second operand is a quiet NaN, or neither operand is a NaN and the operands are
not `(-0, +0)` (minimum) or `(+0, -0)` (maximum). -/
theorem x86_minMax_admitted_iff32 (c : MXCSRControl) (hdaz : c.denormalsAreZeros = false)
    (isMax : Bool) (x y : BitVec 32) :
    floatBinOpRel .f32 (if isMax then .max else .min) x y
        ((Profile.x86SSE c).minMaxBase (fmt := .binary32) isMax x y).value ↔
      MinMaxRule.agreesWithWasm (fmt := .binary32) .x86 isMax x y = true :=
  minMax_admitted_iff32 _ hdaz .x86 isMax x y

/-- x86 `MINSD`/`MAXSD` against WebAssembly `fmin`/`fmax`. -/
theorem x86_minMax_admitted_iff64 (c : MXCSRControl) (hdaz : c.denormalsAreZeros = false)
    (isMax : Bool) (x y : BitVec 64) :
    floatBinOpRel .f64 (if isMax then .max else .min) x y
        ((Profile.x86SSE c).minMaxBase (fmt := .binary64) isMax x y).value ↔
      MinMaxRule.agreesWithWasm (fmt := .binary64) .x86 isMax x y = true :=
  minMax_admitted_iff64 _ hdaz .x86 isMax x y

/-- x86 `CVTTSS2SI` (and its unsigned AVX-512 form) is WebAssembly `trunc` where
`trunc` does not trap, and the integer indefinite value where it traps. -/
theorem x86_cvtt_eq_truncFloat32 (c : MXCSRControl) (hdaz : c.denormalsAreZeros = false)
    (target : IntType) (sign : Wasm.Signedness) (x : BitVec 32) :
    ((Profile.x86SSE c).toInt .binary32 (integerFormat target sign) .towardZero x).value =
      match truncFloat .f32 target sign x with
      | .ok v => v
      | .error _ => Profile.intOverflowResult .indefinite (integerFormat target sign)
          (Bits.value (fmt := .binary32) x) .towardZero :=
  toInt_eq_truncFloat32 _ hdaz target sign x

/-- x86 `CVTTSD2SI` against WebAssembly `trunc`. -/
theorem x86_cvtt_eq_truncFloat64 (c : MXCSRControl) (hdaz : c.denormalsAreZeros = false)
    (target : IntType) (sign : Wasm.Signedness) (x : BitVec 64) :
    ((Profile.x86SSE c).toInt .binary64 (integerFormat target sign) .towardZero x).value =
      match truncFloat .f64 target sign x with
      | .ok v => v
      | .error _ => Profile.intOverflowResult .indefinite (integerFormat target sign)
          (Bits.value (fmt := .binary64) x) .towardZero :=
  toInt_eq_truncFloat64 _ hdaz target sign x

/-- RISC-V F/D arithmetic results are admitted by WebAssembly. -/
theorem riscv_binary_admitted32 (op : FloatBinOp) (core : ArithOp)
    (hop : wasmBinaryCore? op = some core) (x y : BitVec 32) :
    floatBinOpRel .f32 op x y
      (Profile.riscvFD.binary .binary32 core .nearestTiesToEven x y).value :=
  binary_admitted32 _ rfl rfl op core hop x y

/-- RISC-V `FMIN`/`FMAX` agree with WebAssembly exactly when both or neither
operand is a NaN. -/
theorem riscv_minMax_admitted_iff32 (isMax : Bool) (x y : BitVec 32) :
    floatBinOpRel .f32 (if isMax then .max else .min) x y
        (Profile.riscvFD.minMaxBase (fmt := .binary32) isMax x y).value ↔
      Bits.isNaN (fmt := .binary32) x = Bits.isNaN (fmt := .binary32) y := by
  rw [show Profile.riscvFD.minMaxBase (fmt := .binary32) isMax x y =
    Profile.riscvFD.minMaxWith (fmt := .binary32) .minimumNumber isMax x y from rfl,
    minMax_admitted_iff32 _ rfl .minimumNumber isMax x y]
  simp [MinMaxRule.agreesWithWasm]

/-- AArch64 `FADD`/`FSUB`/`FMUL`/`FDIV` results are admitted by WebAssembly. -/
theorem aarch64_binary_admitted32 (dn : Bool) (op : FloatBinOp)
    (core : ArithOp) (hop : wasmBinaryCore? op = some core)
    (x y : BitVec 32) :
    floatBinOpRel .f32 op x y
      ((Profile.aarch64 { defaultNaN := dn }).binary .binary32 core .nearestTiesToEven
        x y).value :=
  binary_admitted32 _ rfl rfl op core hop x y

/-- AArch64 `FMIN`/`FMAX` always produce a result WebAssembly admits. -/
theorem aarch64_fmin_admitted32 (dn : Bool) (isMax : Bool) (x y : BitVec 32) :
    floatBinOpRel .f32 (if isMax then .max else .min) x y
      ((Profile.aarch64 { defaultNaN := dn }).minMaxBase (fmt := .binary32) isMax x y).value :=
  minimumRule_admitted32 _ rfl isMax x y

/-- AArch64 `FCVTZS`/`FCVTZU` equal WebAssembly `trunc_sat`. -/
theorem aarch64_fcvtz_eq_truncSat32 (dn : Bool) (target : IntType) (sign : Wasm.Signedness)
    (x : BitVec 32) :
    ((Profile.aarch64 { defaultNaN := dn }).toInt .binary32 (integerFormat target sign)
      .towardZero x).value = truncSatFloat .f32 target sign x :=
  toInt_saturateNaNToZero_eq_truncSat32 _ rfl target sign rfl x

end Concrete

end Silmaril.Numeric.Float
