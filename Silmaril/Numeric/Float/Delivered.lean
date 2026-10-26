module

public import Silmaril.Numeric.Float.Flags
public import Silmaril.Numeric.Ieee754.Flags.DivSqrt

/-!
# Returned values of the profile operations agree with their flags

The profile operations compute their flags from the exact result
(`Silmaril.Numeric.Float.Flags`) and their values with the executable rounding.
This module proves that the two agree for a profile that flushes neither inputs
nor results: on finite operands, the returned encoding decodes to the
specification's `FlagSpec.deliver` of the exact result, so the inexact flag is
raised exactly when the returned value differs from the exact result.

* `binary_delivered`, `binary_inexact_iff`: `add`, `sub`, `mul` and `div`
  (divisor nonzero);
* `sqrt_delivered`, `sqrt_inexact_iff`: square root of a nonnegative operand, with
  the decoded result read in `ℝ`;
* `fmaWith_delivered`, `fmaWith_inexact_iff`: fused multiply-add, for every NaN
  rule;
* `convert_delivered`, `convert_inexact_iff`: format conversion;
* `ofInt_delivered`, `ofInt_inexact_iff`: integer-to-float conversion, for every
  profile (integers are never tiny and have no input to flush).

Together with `Silmaril.Numeric.Float.Flags` (the overflow and underflow flags are
those of the same exact result), this is the value/flag agreement of IEEE 754-2019
§7 for these operations. With result flushing the agreement fails by design on
exact tiny results (`x86_binary_flags_eq_ieee_iff`), and with input flushing the
exact result is that of the flushed operands; neither case is covered here. NaN
results, signed zeros and payloads are outside `deliver` and not covered either.
-/

@[expose] public section

namespace Silmaril.Numeric.Float

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec
open Silmaril.Numeric.Ieee754.Conformance (value? value?_addExact value?_subExact value?_mulExact
  value?_fmaExact value?_ofInt)
open Silmaril.Numeric.Ieee754.FlagSpec (Datum)

namespace ArithOp

/-- The exact rational result of a binary arithmetic operation. -/
def exact : ArithOp → ℚ → ℚ → ℚ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

/-- The executable rounding of the core operation delivers `deliver` of the
exact result, in every format and rounding direction. -/
theorem roundedOf?_round (fmt : Format) (mode : RoundingMode) (op : ArithOp)
    {x y : UnpackedFloat} {a b : ℚ} (hx : value? x = some a) (hy : value? y = some b)
    (hb : op = .div → b ≠ 0) :
    roundedOf? (UnpackedFloat.unpack fmt ((op.core x y).round fmt mode)) =
      some (deliver fmt mode (op.exact a b)) := by
  cases op
  · exact roundedOf?_unpack_packRounded fmt mode (value?_addExact mode hx hy)
  · exact roundedOf?_unpack_packRounded fmt mode (value?_subExact mode hx hy)
  · exact roundedOf?_unpack_packRounded fmt mode (value?_mulExact hx hy)
  · exact roundedOf?_unpack_divRounded fmt mode hx hy (hb rfl)

/-- The IEEE flags of the operation on finite operands are those of rounding the
exact result. -/
theorem ieeeFlags_finite (op : ArithOp) (f : Format) (mode : RoundingMode)
    (tininess : Tininess) (nx ny : Bool) {a b : ℚ} (hb : op = .div → b ≠ 0) :
    op.ieeeFlags f mode tininess (.finite nx a) (.finite ny b) =
      roundingFlags f mode tininess (op.exact a b) := by
  cases op
  · rfl
  · exact sub_finite f mode tininess nx ny a b
  · rfl
  · exact div_finite f mode tininess nx ny a (hb rfl)

end ArithOp

namespace Bits

variable {fmt : Format}

/-- An encoding that decodes to a delivered result is not a NaN. -/
theorem isNaN_eq_false_of_roundedOf? {r : Bits fmt} {d : Rounded ℚ}
    (h : roundedOf? (UnpackedFloat.unpack fmt r) = some d) : r.isNaN = false := by
  cases hn : r.isNaN
  · rfl
  · exfalso
    simp only [Bits.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hn
    change roundedOf? r.value = some d at h
    unfold Bits.value UnpackedFloat.unpack at h
    simp [hn.1, hn.2, roundedOf?] at h

theorem value?_of_datum {x : Bits fmt} {n : Bool} {a : ℚ} (hx : x.datum = .finite n a) :
    value? x.value = some a := by
  rw [Bits.value?_value, hx]
  rfl

theorem isNaN_eq_false_of_datum {x : Bits fmt} {n : Bool} {a : ℚ} (hx : x.datum = .finite n a) :
    x.isNaN = false := by
  rw [← Bits.datum_isNaN, hx]
  rfl

end Bits

namespace Profile

variable (p : Profile) {fmt : Format}

open Bits (isNaN_eq_false_of_roundedOf? value?_of_datum isNaN_eq_false_of_datum)

/-- Without flushing, the value of `add`, `sub`, `mul` and `div` on finite
operands (a nonzero divisor for `div`) decodes to `deliver` of the exact result. -/
theorem binary_delivered (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (op : ArithOp) (mode : RoundingMode) {x y : Bits fmt} {nx ny : Bool} {a b : ℚ}
    (hx : x.datum = .finite nx a) (hy : y.datum = .finite ny b) (hb : op = .div → b ≠ 0) :
    roundedOf? (p.binary fmt op mode x y).value.value = some (deliver fmt mode (op.exact a b)) := by
  have hr := ArithOp.roundedOf?_round fmt mode op (value?_of_datum hx) (value?_of_datum hy) hb
  have hrn := isNaN_eq_false_of_roundedOf? hr
  simp only [binary, flushInput_of_false p _ hin, nanOrElse, finish, flushSign?, hout,
    List.any_cons, List.any_nil, isNaN_eq_false_of_datum hx, isNaN_eq_false_of_datum hy,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, hrn]
  exact hr

/-- Without flushing, `add`, `sub`, `mul` and `div` on finite operands raise
inexact exactly when the returned value differs from the exact result. -/
theorem binary_inexact_iff (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (op : ArithOp) (mode : RoundingMode) {x y : Bits fmt} {nx ny : Bool} {a b : ℚ}
    (hx : x.datum = .finite nx a) (hy : y.datum = .finite ny b) (hb : op = .div → b ≠ 0) :
    (p.binary fmt op mode x y).flags.inexact = true ↔
      value? (p.binary fmt op mode x y).value.value ≠ some (op.exact a b) := by
  rw [binary_flags_ieee p hin hout, hx, hy, ArithOp.ieeeFlags_finite op _ _ _ _ _ hb,
    roundingFlags_inexact, ne_eq, ne_eq, ← roundedOf?_eq_finite_iff,
    binary_delivered p hin hout op mode hx hy hb, Option.some.injEq]

/-- Without flushing, the square root of a finite nonnegative operand decodes,
read in `ℝ`, to `deliver` of the real square root. -/
theorem sqrt_delivered (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) {x : Bits fmt} {n : Bool} {a : ℚ} (hx : x.datum = .finite n a)
    (ha : 0 ≤ a) :
    (roundedOf? (p.sqrt fmt mode x).value.value).map Rounded.cast =
      some (deliver fmt mode (Real.sqrt (a : ℝ))) := by
  have hr := roundedOf?_unpack_sqrtRounded fmt mode (value?_of_datum hx) ha
  obtain ⟨d, hd⟩ : ∃ d, roundedOf? (UnpackedFloat.unpack fmt
      (Rounding.sqrtRounded fmt mode x.value)) = some d := by
    cases h : roundedOf? (UnpackedFloat.unpack fmt (Rounding.sqrtRounded fmt mode x.value)) with
    | none => rw [h] at hr; simp at hr
    | some d => exact ⟨d, rfl⟩
  have hrn := isNaN_eq_false_of_roundedOf? hd
  simp only [sqrt, flushInput_of_false p _ hin, nanOrElse, finish, flushSign?, hout,
    List.any_cons, List.any_nil, isNaN_eq_false_of_datum hx, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, CoreOp.round, hrn]
  exact hr

/-- Without flushing, the square root of a finite nonnegative operand raises
inexact exactly when the returned value is not the exact real square root. -/
theorem sqrt_inexact_iff (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) {x : Bits fmt} {n : Bool} {a : ℚ} (hx : x.datum = .finite n a)
    (ha : 0 ≤ a) :
    (p.sqrt fmt mode x).flags.inexact = true ↔
      ¬ ∃ v : ℚ, value? (p.sqrt fmt mode x).value.value = some v ∧
        (v : ℝ) = Real.sqrt (a : ℝ) := by
  rw [sqrt_flags_ieee p hin hout, hx, sqrt_finite _ _ _ _ ha, roundingFlags_inexact]
  refine (inexact_iff_of_map_cast _ _ (sqrt_delivered p hin hout mode hx ha)).trans ?_
  simp only [roundedOf?_eq_finite_iff]

/-- Without flushing, fused multiply-add of finite operands decodes to `deliver`
of the exact `a * b + c`, for every NaN rule. -/
theorem fmaWith_delivered (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (rule : FmaNaNRule) (mode : RoundingMode) {x y z : Bits fmt} {nx ny nz : Bool} {a b c : ℚ}
    (hx : x.datum = .finite nx a) (hy : y.datum = .finite ny b) (hz : z.datum = .finite nz c) :
    roundedOf? (p.fmaWith fmt rule mode x y z).value.value =
      some (deliver fmt mode (a * b + c)) := by
  have hr := roundedOf?_unpack_packRounded fmt mode
    (value?_fmaExact mode (value?_of_datum hx) (value?_of_datum hy) (value?_of_datum hz))
  have hrn : Bits.isNaN (Rounding.fmaRounded fmt mode x.value y.value z.value) = false :=
    isNaN_eq_false_of_roundedOf? hr
  simp only [fmaWith, flushInput_of_false p _ hin, finish, flushSign?, hout,
    isNaN_eq_false_of_datum hx, isNaN_eq_false_of_datum hy, isNaN_eq_false_of_datum hz,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, CoreOp.round, hrn]
  exact hr

/-- Without flushing, fused multiply-add of finite operands raises inexact exactly
when the returned value differs from `a * b + c`. -/
theorem fmaWith_inexact_iff (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (rule : FmaNaNRule) (mode : RoundingMode) {x y z : Bits fmt} {nx ny nz : Bool} {a b c : ℚ}
    (hx : x.datum = .finite nx a) (hy : y.datum = .finite ny b) (hz : z.datum = .finite nz c) :
    (p.fmaWith fmt rule mode x y z).flags.inexact = true ↔
      value? (p.fmaWith fmt rule mode x y z).value.value ≠ some (a * b + c) := by
  rw [fmaWith_flags_ieee p hin hout, hx, hy, hz, fma_finite, roundingFlags_inexact, ne_eq, ne_eq,
    ← roundedOf?_eq_finite_iff, fmaWith_delivered p hin hout rule mode hx hy hz,
    Option.some.injEq]

/-- Without flushing, converting a finite operand decodes to `deliver` of its
value in the destination format. -/
theorem convert_delivered {src dst : Format} (hin : p.flushInputs = false)
    (hout : p.flushResults = false) (mode : RoundingMode) {x : Bits src} {n : Bool} {a : ℚ}
    (hx : x.datum = .finite n a) :
    roundedOf? (p.convert src dst mode x).value.value = some (deliver dst mode a) := by
  have hr := roundedOf?_unpack_packRounded dst mode (value?_of_datum hx)
  have hrn := isNaN_eq_false_of_roundedOf? hr
  simp only [convert, flushInput_of_false p _ hin, finish, flushSign?, hout,
    isNaN_eq_false_of_datum hx, Bool.false_eq_true, ↓reduceIte, CoreOp.round, hrn]
  exact hr

/-- Without flushing, converting a finite operand raises inexact exactly when the
returned value differs from the operand's value. -/
theorem convert_inexact_iff {src dst : Format} (hin : p.flushInputs = false)
    (hout : p.flushResults = false) (mode : RoundingMode) {x : Bits src} {n : Bool} {a : ℚ}
    (hx : x.datum = .finite n a) :
    (p.convert src dst mode x).flags.inexact = true ↔
      value? (p.convert src dst mode x).value.value ≠ some a := by
  rw [convert_flags_ieee p hin hout, hx, convert_finite, roundingFlags_inexact, ne_eq, ne_eq,
    ← roundedOf?_eq_finite_iff, convert_delivered p hin hout mode hx, Option.some.injEq]

/-- For every profile, integer-to-float conversion decodes to `deliver` of the
integer. -/
theorem ofInt_delivered (mode : RoundingMode) (n : Int) :
    roundedOf? (p.ofInt fmt mode n).value.value = some (deliver fmt mode (n : ℚ)) :=
  roundedOf?_unpack_packRounded fmt mode (value?_ofInt n)

/-- For every profile, integer-to-float conversion raises inexact exactly when the
returned value differs from the integer. -/
theorem ofInt_inexact_iff (mode : RoundingMode) (n : Int) :
    (p.ofInt fmt mode n).flags.inexact = true ↔
      value? (p.ofInt fmt mode n).value.value ≠ some (n : ℚ) := by
  rw [ofInt_flags, FlagSpec.ofInt, roundingFlags_inexact, ne_eq, ne_eq,
    ← roundedOf?_eq_finite_iff, ofInt_delivered, Option.some.injEq]

/-! ## Architecture profiles -/

/-- x86 SSE with DAZ and FZ clear: `ADDSS`…`DIVSD` raise precision exactly when
the returned value differs from the exact result. -/
theorem x86SSE_binary_inexact_iff {c : MXCSRControl} (hdaz : c.denormalsAreZeros = false)
    (hftz : c.flushToZero = false) (op : ArithOp) (mode : RoundingMode) {x y : Bits fmt}
    {nx ny : Bool} {a b : ℚ} (hx : x.datum = .finite nx a) (hy : y.datum = .finite ny b)
    (hb : op = .div → b ≠ 0) :
    ((Profile.x86SSE c).binary fmt op mode x y).flags.inexact = true ↔
      value? ((Profile.x86SSE c).binary fmt op mode x y).value.value ≠ some (op.exact a b) :=
  (Profile.x86SSE c).binary_inexact_iff hdaz hftz op mode hx hy hb

/-- RISC-V F/D, which never flushes: `FADD`…`FDIV` raise NX exactly when the
returned value differs from the exact result. -/
theorem riscvFD_binary_inexact_iff (op : ArithOp) (mode : RoundingMode) {x y : Bits fmt}
    {nx ny : Bool} {a b : ℚ} (hx : x.datum = .finite nx a) (hy : y.datum = .finite ny b)
    (hb : op = .div → b ≠ 0) :
    (Profile.riscvFD.binary fmt op mode x y).flags.inexact = true ↔
      value? (Profile.riscvFD.binary fmt op mode x y).value.value ≠ some (op.exact a b) :=
  Profile.riscvFD.binary_inexact_iff rfl rfl op mode hx hy hb

/-- AArch64 with FPCR.FZ clear: `FADD`…`FDIV` raise IXC exactly when the returned
value differs from the exact result. -/
theorem aarch64_binary_inexact_iff {c : FPCRControl} (hfz : c.flushToZero = false)
    (op : ArithOp) (mode : RoundingMode) {x y : Bits fmt} {nx ny : Bool} {a b : ℚ}
    (hx : x.datum = .finite nx a) (hy : y.datum = .finite ny b) (hb : op = .div → b ≠ 0) :
    ((Profile.aarch64 c).binary fmt op mode x y).flags.inexact = true ↔
      value? ((Profile.aarch64 c).binary fmt op mode x y).value.value ≠ some (op.exact a b) :=
  (Profile.aarch64 c).binary_inexact_iff hfz hfz op mode hx hy hb

end Profile

end Silmaril.Numeric.Float
