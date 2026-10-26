module

public import Silmaril.Numeric.Ieee754.Rounding
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Exact arithmetic before destination rounding

The rational interpretation here is independent of the executable arithmetic.
The theorems prove that the unbounded integer calculations used by `addExact`
and `mulExact` denote rational addition and multiplication for every finite
input, without assuming normalized significands or a destination exponent range.
In particular, the intermediate consumed by FMA denotes exactly `x * y + z`,
as required by IEEE 754-2019 §5.4.1 before its one destination rounding.

Rational interpretation identifies the two zeros. The sign of an exact zero
is a separate obligation under IEEE §6.3; `addExact_finite_cancel` and
`fmaExact_finite_cancel` prove that sign for nonzero finite operands that cancel.
These results establish the exact arithmetic stage, not
correctness of the following rounding and packing stages or exception flags.

Reference: <https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Conformance

open Float.Model Float.Model.UnpackedFloat

/-- The mathematical value of an integer significand and an unbounded binary exponent. -/
def dyadic (mantissa exponent : Int) : ℚ := (mantissa : ℚ) * (2 : ℚ) ^ exponent

/-- Independent rational semantics. Both zeros denote zero; infinities and
NaNs have no rational value. No normalization or range invariant is assumed. -/
def value? : UnpackedFloat → Option ℚ
  | .zero _ => some 0
  | .finite sign mantissa exponent _ => some (dyadic (sign.apply mantissa) exponent)
  | .infinity _ | .notANumber => none

@[simp] theorem value?_zero (sign : Sign) : value? (.zero sign) = some 0 := rfl
@[simp] theorem value?_infinity (sign : Sign) : value? (.infinity sign) = none := rfl
@[simp] theorem value?_notANumber : value? .notANumber = none := rfl
@[simp] theorem value?_finite (sign : Sign) (mantissa : Nat) (exponent : Int)
    (positive : 0 < mantissa) :
    value? (.finite sign mantissa exponent positive) =
      some (dyadic (sign.apply mantissa) exponent) := rfl

@[simp] theorem dyadic_zero (exponent : Int) : dyadic 0 exponent = 0 := by
  simp [dyadic]

@[simp] theorem dyadic_neg (mantissa exponent : Int) :
    dyadic (-mantissa) exponent = -dyadic mantissa exponent := by
  simp [dyadic]

@[simp] theorem dyadic_eq_zero_iff (mantissa exponent : Int) :
    dyadic mantissa exponent = 0 ↔ mantissa = 0 := by
  simp [dyadic, mul_eq_zero, zpow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)]

theorem dyadic_add (left right exponent : Int) :
    dyadic (left + right) exponent = dyadic left exponent + dyadic right exponent := by
  simp [dyadic, add_mul]

theorem dyadic_mul (left right leftExponent rightExponent : Int) :
    dyadic (left * right) (leftExponent + rightExponent) =
      dyadic left leftExponent * dyadic right rightExponent := by
  simp only [dyadic, Int.cast_mul, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  ring

/-- Increasing an integer significand by a left shift and decreasing its
exponent by the same amount preserves its exact value. -/
theorem dyadic_shiftLeft (mantissa shift : Nat) (exponent : Int) :
    dyadic ((mantissa <<< shift : Nat) : Int) (exponent - shift) = dyadic mantissa exponent := by
  simp only [dyadic, Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Int.cast_natCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [← zpow_natCast (2 : ℚ) shift, mul_assoc,
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 2
  omega

/-- Exponent alignment preserves value, for every requested target exponent. -/
theorem decreaseExponent_value (sign : Sign) (mantissa : Nat) (exponent target : Int) :
    dyadic (sign.apply (decreaseExponent mantissa exponent target).1)
      (decreaseExponent mantissa exponent target).2 = dyadic (sign.apply mantissa) exponent := by
  cases sign <;> simp only [decreaseExponent, Sign.apply, dyadic_neg, dyadic_shiftLeft]

/-- When alignment requests a lower exponent, it reaches precisely that exponent. -/
theorem decreaseExponent_exponent_of_le (mantissa : Nat) {exponent target : Int}
    (h : target ≤ exponent) : (decreaseExponent mantissa exponent target).2 = target := by
  simp [decreaseExponent, Int.toNat_of_nonneg (sub_nonneg.mpr h)]

/-- Exact alignment to a common exponent, as used by addition. -/
theorem decreaseExponent_value_of_le (sign : Sign) (mantissa : Nat) {exponent target : Int}
    (h : target ≤ exponent) :
    dyadic (sign.apply (decreaseExponent mantissa exponent target).1) target =
      dyadic (sign.apply mantissa) exponent := by
  simpa only [decreaseExponent_exponent_of_le mantissa h] using
    decreaseExponent_value sign mantissa exponent target

/-- Constructing a signed dyadic number preserves its exact rational value,
including when the supplied significand is zero. -/
@[simp] theorem value?_ofDyadic (mantissa exponent : Int) (zeroSign : Sign) :
    value? (Rounding.ofDyadic mantissa exponent zeroSign) = some (dyadic mantissa exponent) := by
  unfold Rounding.ofDyadic
  split
  next h =>
    have hm : mantissa = 0 := Int.natAbs_eq_zero.mp h
    subst mantissa
    simp
  next _ =>
    simp only [value?]
    congr 2
    split
    next h => simp [Sign.apply, abs_of_neg h]
    next h => simp [Sign.apply, abs_of_nonneg (Int.not_lt.mp h)]

/-- Embedding an arbitrary integer has its exact mathematical integer value. -/
@[simp] theorem value?_ofInt (value : Int) :
    value? (Rounding.ofInt value) = some (value : ℚ) := by
  simp [Rounding.ofInt, dyadic]

/-- Negation has its ordinary rational meaning for every finite input. -/
theorem value?_neg {x : UnpackedFloat} {a : ℚ} (hx : value? x = some a) :
    value? x.neg = some (-a) := by
  cases x with
  | infinity sign => simp [value?] at hx
  | notANumber => simp [value?] at hx
  | zero sign =>
    have ha : a = 0 := by simpa [value?] using hx.symm
    subst a
    simp [UnpackedFloat.neg]
  | finite sign mantissa exponent positive =>
    simp only [value?, Option.some.injEq] at hx
    subst a
    cases sign <;> simp [value?, UnpackedFloat.neg, Sign.apply, dyadic]

/-- Exact addition denotes rational addition for all finite inputs. In
particular, exponent alignment does not discard low significand bits. -/
theorem value?_addExact (mode : RoundingMode) {x y : UnpackedFloat} {a b : ℚ}
    (hx : value? x = some a) (hy : value? y = some b) :
    value? (Rounding.addExact mode x y) = some (a + b) := by
  cases x with
  | infinity sign => simp [value?] at hx
  | notANumber => simp [value?] at hx
  | zero sign =>
    cases y <;> simp_all [value?, Rounding.addExact]
  | finite sx mx ex px =>
    cases y with
    | infinity sign => simp [value?] at hy
    | notANumber => simp [value?] at hy
    | zero sign => simp_all [value?, Rounding.addExact]
    | finite sy my ey py =>
      simp only [value?, Option.some.injEq] at hx hy
      subst a
      subst b
      change value? (Rounding.ofDyadic
        (sx.apply (decreaseExponent mx ex (min ex ey)).1 +
          sy.apply (decreaseExponent my ey (min ex ey)).1)
        (min ex ey) (Rounding.cancellationSign mode)) = _
      rw [value?_ofDyadic, dyadic_add,
        decreaseExponent_value_of_le sx mx (min_le_left ex ey),
        decreaseExponent_value_of_le sy my (min_le_right ex ey)]

/-- The exact intermediate used by subtraction denotes rational subtraction. -/
theorem value?_subExact (mode : RoundingMode) {x y : UnpackedFloat} {a b : ℚ}
    (hx : value? x = some a) (hy : value? y = some b) :
    value? (Rounding.addExact mode x y.neg) = some (a - b) := by
  simpa only [sub_eq_add_neg] using value?_addExact mode hx (value?_neg hy)

/-- Nonzero finite operands that cancel exactly produce the zero sign selected
by IEEE §6.3: negative under round-toward-negative, positive otherwise. Unlike
rational equality alone, this theorem distinguishes the resulting zero sign. -/
theorem addExact_finite_cancel (mode : RoundingMode)
    (sx sy : Sign) (mx my : Nat) (ex ey : Int) (px : 0 < mx) (py : 0 < my)
    (hCancel : dyadic (sx.apply mx) ex + dyadic (sy.apply my) ey = 0) :
    Rounding.addExact mode (.finite sx mx ex px) (.finite sy my ey py) =
      .zero (Rounding.cancellationSign mode) := by
  have hDyadic : dyadic
      (sx.apply (decreaseExponent mx ex (min ex ey)).1 +
        sy.apply (decreaseExponent my ey (min ex ey)).1) (min ex ey) = 0 := by
    rw [dyadic_add, decreaseExponent_value_of_le sx mx (min_le_left ex ey),
      decreaseExponent_value_of_le sy my (min_le_right ex ey)]
    exact hCancel
  have hMantissa := (dyadic_eq_zero_iff _ _).mp hDyadic
  change Rounding.ofDyadic
    (sx.apply (decreaseExponent mx ex (min ex ey)).1 +
      sy.apply (decreaseExponent my ey (min ex ey)).1)
    (min ex ey) (Rounding.cancellationSign mode) = _
  simp [hMantissa, Rounding.ofDyadic]

/-- Multiplying signed integer magnitudes is ordinary integer multiplication. -/
theorem sign_apply_mul (left right : Sign) (a b : Int) :
    (left * right).apply (a * b) = left.apply a * right.apply b := by
  cases left <;> cases right <;> simp [Sign.apply]

/-- Exact multiplication denotes rational multiplication, without destination
overflow or underflow, for every pair of finite unpacked values. -/
theorem value?_mulExact {x y : UnpackedFloat} {a b : ℚ}
    (hx : value? x = some a) (hy : value? y = some b) :
    value? (Rounding.mulExact x y) = some (a * b) := by
  cases x with
  | infinity sign => simp [value?] at hx
  | notANumber => simp [value?] at hx
  | zero sign =>
    have ha : a = 0 := by simpa [value?] using hx.symm
    subst a
    cases y with
    | infinity other => simp [value?] at hy
    | notANumber => simp [value?] at hy
    | zero other => simp [value?, Rounding.mulExact]
    | finite sy my ey py => simp [value?, Rounding.mulExact]
  | finite sx mx ex px =>
    cases y with
    | infinity sign => simp [value?] at hy
    | notANumber => simp [value?] at hy
    | zero sign =>
      have hb : b = 0 := by simpa [value?] using hy.symm
      subst b
      simp [value?, Rounding.mulExact]
    | finite sy my ey py =>
      simp only [value?, Option.some.injEq] at hx hy
      subst a
      subst b
      simp only [Rounding.mulExact, value?, Nat.cast_mul, sign_apply_mul, dyadic_mul]

/-- The FMA intermediate has exactly the rational value `a * b + c`. This
holds even when the product cannot be represented in the destination format;
neither multiplication nor addition has been rounded at this stage. -/
theorem value?_fmaExact (mode : RoundingMode) {x y z : UnpackedFloat} {a b c : ℚ}
    (hx : value? x = some a) (hy : value? y = some b) (hz : value? z = some c) :
    value? (Rounding.addExact mode (Rounding.mulExact x y) z) = some (a * b + c) :=
  value?_addExact mode (value?_mulExact hx hy) hz

/-- Exact cancellation of a nonzero finite product with a nonzero finite
addend follows IEEE §6.3's zero-sign rule, before destination rounding. -/
theorem fmaExact_finite_cancel (mode : RoundingMode)
    (sx sy sz : Sign) (mx my mz : Nat) (ex ey ez : Int)
    (px : 0 < mx) (py : 0 < my) (pz : 0 < mz)
    (hCancel : dyadic (sx.apply mx) ex * dyadic (sy.apply my) ey +
      dyadic (sz.apply mz) ez = 0) :
    Rounding.addExact mode
      (Rounding.mulExact (.finite sx mx ex px) (.finite sy my ey py))
      (.finite sz mz ez pz) = .zero (Rounding.cancellationSign mode) := by
  apply addExact_finite_cancel
  simpa only [Nat.cast_mul, sign_apply_mul, dyadic_mul] using hCancel

/-- The executable FMA invokes destination rounding on an intermediate whose
independently interpreted value is exactly `a * b + c`. Correctness of that
rounding call remains a separate theorem; this proves its input is exact. -/
theorem fmaRounded_exact_intermediate (format : Format) (mode : RoundingMode)
    {x y z : UnpackedFloat} {a b c : ℚ}
    (hx : value? x = some a) (hy : value? y = some b) (hz : value? z = some c) :
    ∃ intermediate : UnpackedFloat,
      value? intermediate = some (a * b + c) ∧
      Rounding.fmaRounded format mode x y z = Rounding.packRounded format mode intermediate :=
  ⟨Rounding.addExact mode (Rounding.mulExact x y) z, value?_fmaExact mode hx hy hz, rfl⟩

end Silmaril.Numeric.Ieee754.Conformance
