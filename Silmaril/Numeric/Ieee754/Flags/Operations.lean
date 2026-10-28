module

public import Silmaril.Numeric.Ieee754.Flags.Sqrt
public import Silmaril.Numeric.Ieee754.Flags.Datum
public import Silmaril.Numeric.Integer

/-!
# Exception flags of the arithmetic and conversion operations

Each function below returns the flags raised under default exception handling
(IEEE 754-2019 §7) by one operation, from its classified operands, the
destination format, the rounding direction and the tininess convention. The
rules are:

* Invalid operation (§7.2): any signaling NaN operand (§6.2); `∞ − ∞` in
  addition and subtraction; `0 × ∞` in multiplication and in the product of a
  fused multiply-add; `0 / 0` and `∞ / ∞`; square root of a value less than
  zero; conversion to an integer of a NaN, an infinity or a value whose rounded
  integer lies outside the destination range. For `fusedMultiplyAdd(0, ∞, c)`
  with a quiet NaN `c`, §7.2(c) leaves signaling implementation-defined; the
  choice is the parameter `FmaQuietAddend`.
* Division by zero (§7.3): a finite nonzero dividend and a zero divisor.
* Overflow, underflow and inexact (§§7.4–7.6): as classified by `roundingFlags`
  for the exact result, which is `a + b`, `a · b`, `a / b`, `√a` (through
  `sqrtRoundingFlags`) or `a · b + c` (§5.4.1, a single rounding).
* Operations whose result is a quiet NaN because an operand is a quiet NaN, and
  operations with exact infinite results, raise nothing.
* Conversions between formats (§5.4.2) classify the operand's exact value in the
  destination format. Integer-to-float conversion classifies the integer.
* Float-to-integer conversion (§5.8) and `roundToIntegral` (§5.9) raise inexact
  only in their "exact" forms, selected by `signalsInexact`: `convertToIntegerExact…`
  and `roundToIntegralExact` signal inexact, the other forms do not.

The operands are `Datum` values. For raw binary32 and binary64 encodings see
`Numeric.Ieee754.Flags.Binary`; for denormal flushing see
`Numeric.Ieee754.Flags.Denormal`.

`Coherent` states the combinations permitted by §7: invalid and divide-by-zero
alone, overflow and underflow each with inexact, and never overflow with
underflow. Every operation here produces coherent flags.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.FlagSpec

open Float.Model

/-- The invalid-operation flag alone. -/
def invalid : Flags := Flags.singleton .invalidOperation

/-- The divide-by-zero flag alone. -/
def divideByZero : Flags := Flags.singleton .divisionByZero

/-- The inexact flag alone. -/
def inexactOnly : Flags := Flags.singleton .inexact

/-- Addition (§5.4.1). -/
def add (f : Format) (mode : RoundingMode) (tininess : Tininess) (x y : Datum) : Flags :=
  if x.isSignaling || y.isSignaling then invalid
  else match x, y with
    | .nan _, _ | _, .nan _ => Flags.empty
    | .infinity a, .infinity b => if a = b then Flags.empty else invalid
    | .infinity _, .finite .. | .finite .., .infinity _ => Flags.empty
    | .finite _ a, .finite _ b => roundingFlags f mode tininess (a + b)

/-- Subtraction (§5.4.1), as addition of the negated second operand. -/
def sub (f : Format) (mode : RoundingMode) (tininess : Tininess) (x y : Datum) : Flags :=
  add f mode tininess x y.neg

/-- Multiplication (§5.4.1). -/
def mul (f : Format) (mode : RoundingMode) (tininess : Tininess) (x y : Datum) : Flags :=
  if x.isSignaling || y.isSignaling then invalid
  else match x, y with
    | .nan _, _ | _, .nan _ => Flags.empty
    | .infinity _, .infinity _ => Flags.empty
    | .infinity _, .finite _ b | .finite _ b, .infinity _ => if b = 0 then invalid else Flags.empty
    | .finite _ a, .finite _ b => roundingFlags f mode tininess (a * b)

/-- Division (§5.4.1). -/
def div (f : Format) (mode : RoundingMode) (tininess : Tininess) (x y : Datum) : Flags :=
  if x.isSignaling || y.isSignaling then invalid
  else match x, y with
    | .nan _, _ | _, .nan _ => Flags.empty
    | .infinity _, .infinity _ => invalid
    | .infinity _, .finite .. | .finite .., .infinity _ => Flags.empty
    | .finite _ a, .finite _ b =>
      if b = 0 then (if a = 0 then invalid else divideByZero)
      else roundingFlags f mode tininess (a / b)

/-- Square root (§5.4.1). The square root of `-0` is `-0` and raises nothing. -/
def sqrt (f : Format) (mode : RoundingMode) (tininess : Tininess) : Datum → Flags
  | .nan signaling => if signaling then invalid else Flags.empty
  | .infinity negative => if negative then invalid else Flags.empty
  | .finite _ a => if a < 0 then invalid else sqrtRoundingFlags f mode tininess a

/-- Whether `fusedMultiplyAdd(0, ∞, c)` or `fusedMultiplyAdd(∞, 0, c)` with a
quiet NaN `c` signals invalid. IEEE 754-2019 §7.2(c) leaves this
implementation-defined; an architecture profile must choose. -/
inductive FmaQuietAddend where
  | signalInvalid
  | noSignal
  deriving DecidableEq, Repr

/-- The flags chosen by an `FmaQuietAddend` policy for `fma(0, ∞, qNaN)`. -/
def FmaQuietAddend.flags : FmaQuietAddend → Flags
  | .signalInvalid => invalid
  | .noSignal => Flags.empty

/-- The product is `0 × ∞` or `∞ × 0`. -/
def zeroTimesInfinity (x y : Datum) : Bool :=
  (x.isZero && y.isInfinite) || (x.isInfinite && y.isZero)

/-- Fused multiply-add `x · y + z` with one rounding (§5.4.1). -/
def fma (policy : FmaQuietAddend) (f : Format) (mode : RoundingMode) (tininess : Tininess)
    (x y z : Datum) : Flags :=
  if x.isSignaling || y.isSignaling || z.isSignaling then invalid
  else if zeroTimesInfinity x y then
    if z.isNaN then policy.flags else invalid
  else match x, y, z with
    | .nan _, _, _ | _, .nan _, _ | _, _, .nan _ => Flags.empty
    | .finite _ a, .finite _ b, .finite _ c => roundingFlags f mode tininess (a * b + c)
    | .finite .., .finite .., .infinity _ => Flags.empty
    | _, _, .infinity negative =>
      -- The product is infinite with sign `x.negative xor y.negative`.
      if negative = (x.negative ^^ y.negative) then Flags.empty else invalid
    | _, _, _ => Flags.empty

/-- Conversion of an operand to the format `f` (§5.4.2). A quiet NaN converts
to a quiet NaN without an exception. -/
def convert (f : Format) (mode : RoundingMode) (tininess : Tininess) : Datum → Flags
  | .nan signaling => if signaling then invalid else Flags.empty
  | .infinity _ => Flags.empty
  | .finite _ value => roundingFlags f mode tininess value

/-- Conversion of an integer to the format `f` (§5.4.1, `convertFromInt`). -/
def ofInt (f : Format) (mode : RoundingMode) (tininess : Tininess) (n : ℤ) : Flags :=
  roundingFlags f mode tininess (n : ℚ)

/-- Conversion to a bounded integer with the given rounding direction (§5.8).
NaNs (including quiet NaNs), infinities and out-of-range rounded values are
invalid (§7.2). The `convertToIntegerExact…` forms (`signalsInexact`) also
raise inexact when the rounded integer differs from the operand. -/
def toInt (target : IntFormat) (mode : RoundingMode) (signalsInexact : Bool) : Datum → Flags
  | .nan _ | .infinity _ => invalid
  | .finite _ value =>
    if roundInt mode value < target.minValue ∨ target.maxValue < roundInt mode value then invalid
    else if signalsInexact && decide ((roundInt mode value : ℚ) ≠ value) then inexactOnly
    else Flags.empty

/-- Rounding to an integral value in the same format (§5.9). Only
`roundToIntegralExact` (`signalsInexact`) raises inexact. The integral result
of a finite value of a binary format is again a value of that format, so this
classification has no overflow or underflow case. -/
def roundToIntegral (mode : RoundingMode) (signalsInexact : Bool) : Datum → Flags
  | .nan signaling => if signaling then invalid else Flags.empty
  | .infinity _ => Flags.empty
  | .finite _ value =>
    if signalsInexact && decide ((roundInt mode value : ℚ) ≠ value) then inexactOnly
    else Flags.empty

/-! ## Coherence -/

/-- The flag combinations that one operation can raise under default handling
(§7): invalid operation and division by zero are raised alone, overflow and
underflow are each accompanied by inexact, and overflow and underflow do not
coincide. -/
def Coherent (flags : Flags) : Prop :=
  (flags.invalidOperation = true → flags = invalid) ∧
  (flags.divisionByZero = true → flags = divideByZero) ∧
  (flags.overflow = true → flags.inexact = true) ∧
  (flags.underflow = true → flags.inexact = true) ∧
  ¬ (flags.overflow = true ∧ flags.underflow = true)

instance (flags : Flags) : Decidable (Coherent flags) := by
  unfold Coherent
  infer_instance

@[simp] theorem invalid_invalidOperation : invalid.invalidOperation = true := rfl
@[simp] theorem invalid_divisionByZero : invalid.divisionByZero = false := rfl
@[simp] theorem invalid_overflow : invalid.overflow = false := rfl
@[simp] theorem invalid_underflow : invalid.underflow = false := rfl
@[simp] theorem invalid_inexact : invalid.inexact = false := rfl
@[simp] theorem divideByZero_invalidOperation : divideByZero.invalidOperation = false := rfl
@[simp] theorem divideByZero_divisionByZero : divideByZero.divisionByZero = true := rfl
@[simp] theorem divideByZero_overflow : divideByZero.overflow = false := rfl
@[simp] theorem divideByZero_underflow : divideByZero.underflow = false := rfl
@[simp] theorem divideByZero_inexact : divideByZero.inexact = false := rfl
@[simp] theorem inexactOnly_invalidOperation : inexactOnly.invalidOperation = false := rfl
@[simp] theorem inexactOnly_divisionByZero : inexactOnly.divisionByZero = false := rfl
@[simp] theorem inexactOnly_overflow : inexactOnly.overflow = false := rfl
@[simp] theorem inexactOnly_underflow : inexactOnly.underflow = false := rfl
@[simp] theorem inexactOnly_inexact : inexactOnly.inexact = true := rfl
@[simp] theorem empty_invalidOperation : Flags.empty.invalidOperation = false := rfl
@[simp] theorem empty_divisionByZero : Flags.empty.divisionByZero = false := rfl
@[simp] theorem empty_overflow : Flags.empty.overflow = false := rfl
@[simp] theorem empty_underflow : Flags.empty.underflow = false := rfl
@[simp] theorem empty_inexact : Flags.empty.inexact = false := rfl

theorem coherent_empty : Coherent Flags.empty := by decide
theorem coherent_invalid : Coherent invalid := by decide
theorem coherent_divideByZero : Coherent divideByZero := by decide
theorem coherent_inexactOnly : Coherent inexactOnly := by decide

theorem coherent_roundingFlags {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorRing K] (f : Format) (mode : RoundingMode) (tininess : Tininess) (x : K) :
    Coherent (roundingFlags f mode tininess x) :=
  ⟨fun h => by simp [roundingFlags] at h, fun h => by simp [roundingFlags] at h,
    roundingFlags_inexact_of_overflow, roundingFlags_inexact_of_underflow,
    roundingFlags_not_overflow_and_underflow f mode tininess x⟩

theorem coherent_sqrtRoundingFlags (f : Format) (mode : RoundingMode) (tininess : Tininess)
    {a : ℚ} (ha : 0 ≤ a) : Coherent (sqrtRoundingFlags f mode tininess a) := by
  rw [sqrtRoundingFlags_eq f mode tininess ha]
  exact coherent_roundingFlags f mode tininess _

theorem coherent_fmaQuietAddend (policy : FmaQuietAddend) : Coherent policy.flags := by
  cases policy
  · exact coherent_invalid
  · exact coherent_empty

theorem add_coherent (f : Format) (mode : RoundingMode) (tininess : Tininess) (x y : Datum) :
    Coherent (add f mode tininess x y) := by
  unfold add
  split
  · exact coherent_invalid
  · split
    all_goals first
      | exact coherent_empty
      | exact coherent_invalid
      | exact coherent_roundingFlags _ _ _ _
      | (split <;> first | exact coherent_empty | exact coherent_invalid)

theorem sub_coherent (f : Format) (mode : RoundingMode) (tininess : Tininess) (x y : Datum) :
    Coherent (sub f mode tininess x y) := add_coherent f mode tininess x y.neg

theorem mul_coherent (f : Format) (mode : RoundingMode) (tininess : Tininess) (x y : Datum) :
    Coherent (mul f mode tininess x y) := by
  unfold mul
  split
  · exact coherent_invalid
  · split
    all_goals first
      | exact coherent_empty
      | exact coherent_invalid
      | exact coherent_roundingFlags _ _ _ _
      | (split <;> first | exact coherent_empty | exact coherent_invalid)

theorem div_coherent (f : Format) (mode : RoundingMode) (tininess : Tininess) (x y : Datum) :
    Coherent (div f mode tininess x y) := by
  unfold div
  split
  · exact coherent_invalid
  · split
    all_goals first
      | exact coherent_empty
      | exact coherent_invalid
      | (split
         · split <;> first | exact coherent_invalid | exact coherent_divideByZero
         · exact coherent_roundingFlags _ _ _ _)

theorem sqrt_coherent (f : Format) (mode : RoundingMode) (tininess : Tininess) (x : Datum) :
    Coherent (sqrt f mode tininess x) := by
  cases x with
  | nan s => cases s <;> first | exact coherent_invalid | exact coherent_empty
  | infinity n => cases n <;> first | exact coherent_invalid | exact coherent_empty
  | finite n a =>
    simp only [sqrt]
    split
    · exact coherent_invalid
    · next h => exact coherent_sqrtRoundingFlags f mode tininess (not_lt.mp h)

theorem fma_coherent (policy : FmaQuietAddend) (f : Format) (mode : RoundingMode)
    (tininess : Tininess) (x y z : Datum) : Coherent (fma policy f mode tininess x y z) := by
  unfold fma
  split
  · exact coherent_invalid
  · split
    · split
      · exact coherent_fmaQuietAddend policy
      · exact coherent_invalid
    · split
      all_goals first
        | exact coherent_empty
        | exact coherent_invalid
        | exact coherent_roundingFlags _ _ _ _
        | (split <;> first | exact coherent_empty | exact coherent_invalid)

theorem convert_coherent (f : Format) (mode : RoundingMode) (tininess : Tininess) (x : Datum) :
    Coherent (convert f mode tininess x) := by
  cases x with
  | nan s => cases s <;> first | exact coherent_invalid | exact coherent_empty
  | infinity n => exact coherent_empty
  | finite n a => exact coherent_roundingFlags _ _ _ _

theorem ofInt_coherent (f : Format) (mode : RoundingMode) (tininess : Tininess) (n : ℤ) :
    Coherent (ofInt f mode tininess n) := coherent_roundingFlags _ _ _ _

theorem toInt_coherent (target : IntFormat) (mode : RoundingMode) (signalsInexact : Bool)
    (x : Datum) : Coherent (toInt target mode signalsInexact x) := by
  cases x with
  | nan s => exact coherent_invalid
  | infinity n => exact coherent_invalid
  | finite n a =>
    simp only [toInt]
    split
    · exact coherent_invalid
    · split
      · exact coherent_inexactOnly
      · exact coherent_empty

theorem roundToIntegral_coherent (mode : RoundingMode) (signalsInexact : Bool) (x : Datum) :
    Coherent (roundToIntegral mode signalsInexact x) := by
  cases x with
  | nan s => cases s <;> first | exact coherent_invalid | exact coherent_empty
  | infinity n => exact coherent_empty
  | finite n a =>
    simp only [roundToIntegral]
    split
    · exact coherent_inexactOnly
    · exact coherent_empty

/-! ## Signaling and quiet NaN operands -/

section NaN

variable (f : Format) (mode : RoundingMode) (tininess : Tininess)

/-- A signaling NaN operand raises invalid and nothing else. -/
theorem add_of_signaling {x y : Datum} (h : (x.isSignaling || y.isSignaling) = true) :
    add f mode tininess x y = invalid := by
  simp [add, h]

theorem sub_of_signaling {x y : Datum} (h : (x.isSignaling || y.isSignaling) = true) :
    sub f mode tininess x y = invalid := by
  apply add_of_signaling
  simpa using h

theorem mul_of_signaling {x y : Datum} (h : (x.isSignaling || y.isSignaling) = true) :
    mul f mode tininess x y = invalid := by
  simp [mul, h]

theorem div_of_signaling {x y : Datum} (h : (x.isSignaling || y.isSignaling) = true) :
    div f mode tininess x y = invalid := by
  simp [div, h]

theorem sqrt_of_signaling : sqrt f mode tininess (.nan true) = invalid := rfl

theorem fma_of_signaling (policy : FmaQuietAddend) {x y z : Datum}
    (h : (x.isSignaling || y.isSignaling || z.isSignaling) = true) :
    fma policy f mode tininess x y z = invalid := by
  simp [fma, h]

theorem convert_of_signaling : convert f mode tininess (.nan true) = invalid := rfl

theorem roundToIntegral_of_signaling (signalsInexact : Bool) :
    roundToIntegral mode signalsInexact (.nan true) = invalid := rfl

/-- A quiet NaN operand, with no signaling NaN, raises nothing. -/
theorem add_of_quietNaN {x y : Datum} (hs : (x.isSignaling || y.isSignaling) = false)
    (hn : (x.isNaN || y.isNaN) = true) : add f mode tininess x y = Flags.empty := by
  unfold add
  rw [hs]
  cases x <;> cases y <;> simp_all [Datum.isNaN]

theorem sub_of_quietNaN {x y : Datum} (hs : (x.isSignaling || y.isSignaling) = false)
    (hn : (x.isNaN || y.isNaN) = true) : sub f mode tininess x y = Flags.empty :=
  add_of_quietNaN f mode tininess (by simpa using hs) (by simpa using hn)

theorem mul_of_quietNaN {x y : Datum} (hs : (x.isSignaling || y.isSignaling) = false)
    (hn : (x.isNaN || y.isNaN) = true) : mul f mode tininess x y = Flags.empty := by
  unfold mul
  rw [hs]
  cases x <;> cases y <;> simp_all [Datum.isNaN]

theorem div_of_quietNaN {x y : Datum} (hs : (x.isSignaling || y.isSignaling) = false)
    (hn : (x.isNaN || y.isNaN) = true) : div f mode tininess x y = Flags.empty := by
  unfold div
  rw [hs]
  cases x <;> cases y <;> simp_all [Datum.isNaN]

theorem sqrt_of_quietNaN : sqrt f mode tininess (.nan false) = Flags.empty := rfl

theorem convert_of_quietNaN : convert f mode tininess (.nan false) = Flags.empty := rfl

theorem roundToIntegral_of_quietNaN (signalsInexact : Bool) :
    roundToIntegral mode signalsInexact (.nan false) = Flags.empty := rfl

/-- A quiet NaN operand raises nothing in a fused multiply-add, except for the
implementation-defined case `fma(0, ∞, qNaN)` of §7.2(c). -/
theorem fma_of_quietNaN (policy : FmaQuietAddend) {x y z : Datum}
    (hs : (x.isSignaling || y.isSignaling || z.isSignaling) = false)
    (hn : (x.isNaN || y.isNaN || z.isNaN) = true) :
    fma policy f mode tininess x y z =
      if zeroTimesInfinity x y then policy.flags else Flags.empty := by
  unfold fma
  rw [hs]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · next hzi =>
    have hz : z.isNaN = true := by
      cases x <;> cases y <;> simp_all [zeroTimesInfinity, Datum.isNaN, Datum.isZero,
        Datum.isInfinite]
    simp [hz]
  · cases x <;> cases y <;> cases z <;> simp_all [Datum.isNaN]

/-- Under the `noSignal` policy, every quiet NaN operand raises nothing. -/
theorem fma_noSignal_of_quietNaN {x y z : Datum}
    (hs : (x.isSignaling || y.isSignaling || z.isSignaling) = false)
    (hn : (x.isNaN || y.isNaN || z.isNaN) = true) :
    fma .noSignal f mode tininess x y z = Flags.empty := by
  rw [fma_of_quietNaN f mode tininess .noSignal hs hn]
  split <;> rfl

/-- With a signaling NaN present an operation raises only invalid; otherwise a
NaN operand raises nothing (for the NaN-propagating operations below). This is
the combined form of the two previous families. -/
theorem add_of_nan {x y : Datum} (hn : (x.isNaN || y.isNaN) = true) :
    add f mode tininess x y = if x.isSignaling || y.isSignaling then invalid else Flags.empty := by
  split
  · next h => exact add_of_signaling f mode tininess h
  · next h => exact add_of_quietNaN f mode tininess (by simpa using h) hn

theorem mul_of_nan {x y : Datum} (hn : (x.isNaN || y.isNaN) = true) :
    mul f mode tininess x y = if x.isSignaling || y.isSignaling then invalid else Flags.empty := by
  split
  · next h => exact mul_of_signaling f mode tininess h
  · next h => exact mul_of_quietNaN f mode tininess (by simpa using h) hn

theorem div_of_nan {x y : Datum} (hn : (x.isNaN || y.isNaN) = true) :
    div f mode tininess x y = if x.isSignaling || y.isSignaling then invalid else Flags.empty := by
  split
  · next h => exact div_of_signaling f mode tininess h
  · next h => exact div_of_quietNaN f mode tininess (by simpa using h) hn

/-- Conversion to an integer is invalid for every NaN, quiet or signaling
(§7.2), and for both infinities. -/
theorem toInt_of_nan (target : IntFormat) (signalsInexact : Bool) (signaling : Bool) :
    toInt target mode signalsInexact (.nan signaling) = invalid := rfl

theorem toInt_of_infinity (target : IntFormat) (signalsInexact : Bool) (negative : Bool) :
    toInt target mode signalsInexact (.infinity negative) = invalid := rfl

end NaN

/-! ## Invalid operation and division by zero -/

section Invalid

variable (f : Format) (mode : RoundingMode) (tininess : Tininess)

theorem add_invalid_iff (x y : Datum) :
    (add f mode tininess x y).invalidOperation = true ↔
      (x.isSignaling || y.isSignaling) = true ∨
        ∃ negative, x = .infinity negative ∧ y = .infinity !negative := by
  unfold add
  by_cases hs : (x.isSignaling || y.isSignaling) = true
  · simp [hs]
  · simp only [hs, false_or, Bool.false_eq_true, ↓reduceIte]
    cases x <;> cases y <;> simp_all [Datum.isSignaling, roundingFlags]
    split_ifs <;> simp_all
    next a b hab => cases a <;> cases b <;> simp_all

theorem mul_invalid_iff (x y : Datum) :
    (mul f mode tininess x y).invalidOperation = true ↔
      (x.isSignaling || y.isSignaling) = true ∨ zeroTimesInfinity x y = true := by
  unfold mul
  by_cases hs : (x.isSignaling || y.isSignaling) = true
  · simp [hs]
  · simp only [hs, false_or, Bool.false_eq_true, ↓reduceIte]
    cases x <;> cases y <;>
      simp_all [Datum.isSignaling, roundingFlags, zeroTimesInfinity, Datum.isZero,
        Datum.isInfinite]
    all_goals split_ifs <;> simp_all

theorem div_invalid_iff (x y : Datum) :
    (div f mode tininess x y).invalidOperation = true ↔
      (x.isSignaling || y.isSignaling) = true ∨ (x.isInfinite && y.isInfinite) = true ∨
        (x.isZero && y.isZero) = true := by
  unfold div
  by_cases hs : (x.isSignaling || y.isSignaling) = true
  · simp [hs]
  · simp only [hs, false_or, Bool.false_eq_true, ↓reduceIte]
    cases x <;> cases y <;>
      simp_all [Datum.isSignaling, roundingFlags, Datum.isZero, Datum.isInfinite]
    all_goals split_ifs <;> simp_all

/-- Division by zero is raised exactly for a finite nonzero dividend and a zero
divisor (§7.3); an infinite dividend gives an exact infinity. -/
theorem div_divisionByZero_iff (x y : Datum) :
    (div f mode tininess x y).divisionByZero = true ↔
      ∃ nx a ny, x = .finite nx a ∧ a ≠ 0 ∧ y = .finite ny 0 := by
  unfold div
  by_cases hs : (x.isSignaling || y.isSignaling) = true
  · simp only [hs, ↓reduceIte, invalid_divisionByZero, Bool.false_eq_true, false_iff]
    rintro ⟨nx, a, ny, rfl, -, rfl⟩
    simp [Datum.isSignaling] at hs
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    cases x <;> cases y <;> simp_all [Datum.isSignaling, roundingFlags]
    all_goals split_ifs <;> simp_all

theorem sqrt_invalid_iff (x : Datum) :
    (sqrt f mode tininess x).invalidOperation = true ↔
      x.isSignaling = true ∨ x = .infinity true ∨ ∃ n a, x = .finite n a ∧ a < 0 := by
  cases x with
  | nan s => cases s <;> simp [sqrt, Datum.isSignaling]
  | infinity n => cases n <;> simp [sqrt, Datum.isSignaling]
  | finite n a =>
    by_cases h : a < 0
    · simp [sqrt, h, Datum.isSignaling]
    · rw [show sqrt f mode tininess (.finite n a) = sqrtRoundingFlags f mode tininess a by
          simp [sqrt, h], sqrtRoundingFlags_eq f mode tininess (not_lt.mp h)]
      simp [roundingFlags, Datum.isSignaling, h]

/-- `fusedMultiplyAdd(0, ∞, c)` is invalid for every `c` that is not a quiet
NaN (§7.2(c)). -/
theorem fma_zeroTimesInfinity (policy : FmaQuietAddend) {x y z : Datum}
    (hs : (x.isSignaling || y.isSignaling || z.isSignaling) = false)
    (hzi : zeroTimesInfinity x y = true) (hz : z.isNaN = false) :
    fma policy f mode tininess x y z = invalid := by
  simp [fma, hs, hzi, hz]

/-- `fusedMultiplyAdd(0, ∞, qNaN)` raises what the profile's policy selects. -/
theorem fma_zeroTimesInfinity_quietNaN (policy : FmaQuietAddend) {x y : Datum}
    (hs : (x.isSignaling || y.isSignaling) = false) (hzi : zeroTimesInfinity x y = true) :
    fma policy f mode tininess x y (.nan false) = policy.flags := by
  simp_all [fma, Datum.isSignaling, Datum.isNaN]

/-- An infinite product added to an infinity of the opposite sign is invalid. -/
theorem fma_infinity_cancel (policy : FmaQuietAddend) {x y : Datum} (negative : Bool)
    (hx : x.isNaN = false) (hy : y.isNaN = false) (hzi : zeroTimesInfinity x y = false)
    (hinf : (x.isInfinite || y.isInfinite) = true)
    (hsign : negative ≠ (x.negative ^^ y.negative)) :
    fma policy f mode tininess x y (.infinity negative) = invalid := by
  have hxs : x.isSignaling = false := by
    cases x <;> simp_all [Datum.isSignaling, Datum.isNaN]
  have hys : y.isSignaling = false := by
    cases y <;> simp_all [Datum.isSignaling, Datum.isNaN]
  unfold fma
  rw [hxs, hys]
  simp only [Datum.isSignaling, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hzi]
  cases x <;> cases y <;> simp_all [Datum.isNaN, Datum.isInfinite]

/-- Only division raises divide-by-zero among the operations here. -/
theorem add_divisionByZero (x y : Datum) : (add f mode tininess x y).divisionByZero = false := by
  unfold add
  split
  · rfl
  · split <;> first | rfl | (split <;> rfl)

theorem mul_divisionByZero (x y : Datum) : (mul f mode tininess x y).divisionByZero = false := by
  unfold mul
  split
  · rfl
  · split <;> first | rfl | (split <;> rfl)

theorem sqrt_divisionByZero (x : Datum) : (sqrt f mode tininess x).divisionByZero = false := by
  cases x with
  | nan s => cases s <;> rfl
  | infinity n => cases n <;> rfl
  | finite n a =>
    simp only [sqrt]
    split
    · rfl
    · next h =>
      rw [sqrtRoundingFlags_eq f mode tininess (not_lt.mp h)]
      rfl

theorem fma_divisionByZero (policy : FmaQuietAddend) (x y z : Datum) :
    (fma policy f mode tininess x y z).divisionByZero = false := by
  unfold fma
  split
  · rfl
  · split
    · split
      · cases policy <;> rfl
      · rfl
    · split <;> first | rfl | (split <;> rfl)

end Invalid


/-! ## Exact results raise no flags -/

section Exact

variable (f : Format) (mode : RoundingMode) (tininess : Tininess)

@[simp] theorem add_finite (nx ny : Bool) (a b : ℚ) :
    add f mode tininess (.finite nx a) (.finite ny b) = roundingFlags f mode tininess (a + b) := rfl

@[simp] theorem sub_finite (nx ny : Bool) (a b : ℚ) :
    sub f mode tininess (.finite nx a) (.finite ny b) = roundingFlags f mode tininess (a - b) := by
  simp [sub, Datum.neg, sub_eq_add_neg]

@[simp] theorem mul_finite (nx ny : Bool) (a b : ℚ) :
    mul f mode tininess (.finite nx a) (.finite ny b) = roundingFlags f mode tininess (a * b) := rfl

theorem div_finite (nx ny : Bool) (a : ℚ) {b : ℚ} (hb : b ≠ 0) :
    div f mode tininess (.finite nx a) (.finite ny b) = roundingFlags f mode tininess (a / b) := by
  simp [div, hb, Datum.isSignaling]

theorem fma_finite (policy : FmaQuietAddend) (nx ny nz : Bool) (a b c : ℚ) :
    fma policy f mode tininess (.finite nx a) (.finite ny b) (.finite nz c) =
      roundingFlags f mode tininess (a * b + c) := by
  simp [fma, zeroTimesInfinity, Datum.isSignaling, Datum.isInfinite]

/-- The square root of a nonnegative finite operand is classified by the real
square root. -/
theorem sqrt_finite (n : Bool) {a : ℚ} (ha : 0 ≤ a) :
    sqrt f mode tininess (.finite n a) = roundingFlags f mode tininess (Real.sqrt (a : ℝ)) := by
  simp [sqrt, not_lt.mpr ha, sqrtRoundingFlags_eq f mode tininess ha]

@[simp] theorem convert_finite (n : Bool) (a : ℚ) :
    convert f mode tininess (.finite n a) = roundingFlags f mode tininess a := rfl

/-- An exactly representable sum raises no flags. -/
theorem add_eq_empty_of_representable (nx ny : Bool) {a b : ℚ} (h : Representable f (a + b)) :
    add f mode tininess (.finite nx a) (.finite ny b) = Flags.empty :=
  roundingFlags_of_representable f mode tininess h

/-- Adding zero to a finite value of the format raises no flags. -/
theorem add_zero_eq_empty (nx ny : Bool) {a : ℚ} (h : Representable f a) :
    add f mode tininess (.finite nx a) (.finite ny 0) = Flags.empty :=
  add_eq_empty_of_representable f mode tininess nx ny (by simpa using h)

theorem mul_eq_empty_of_representable (nx ny : Bool) {a b : ℚ} (h : Representable f (a * b)) :
    mul f mode tininess (.finite nx a) (.finite ny b) = Flags.empty :=
  roundingFlags_of_representable f mode tininess h

/-- Multiplying a finite value of the format by one raises no flags. -/
theorem mul_one_eq_empty (nx ny : Bool) {a : ℚ} (h : Representable f a) :
    mul f mode tininess (.finite nx a) (.finite ny 1) = Flags.empty :=
  mul_eq_empty_of_representable f mode tininess nx ny (by simpa using h)

theorem fma_eq_empty_of_representable (policy : FmaQuietAddend) (nx ny nz : Bool) {a b c : ℚ}
    (h : Representable f (a * b + c)) :
    fma policy f mode tininess (.finite nx a) (.finite ny b) (.finite nz c) = Flags.empty := by
  rw [fma_finite]
  exact roundingFlags_of_representable f mode tininess h

theorem div_eq_empty_of_representable (nx ny : Bool) {a b : ℚ} (hb : b ≠ 0)
    (h : Representable f (a / b)) :
    div f mode tininess (.finite nx a) (.finite ny b) = Flags.empty := by
  rw [div_finite f mode tininess nx ny a hb]
  exact roundingFlags_of_representable f mode tininess h

/-- A square root whose exact value `r` is a finite value of the format raises
no flags. -/
theorem sqrt_eq_empty_of_representable (n : Bool) {a r : ℚ} (hr : 0 ≤ r) (hsq : r * r = a)
    (h : Representable f r) : sqrt f mode tininess (.finite n a) = Flags.empty := by
  have ha : 0 ≤ a := hsq ▸ mul_self_nonneg r
  have hsqrt : Real.sqrt (a : ℝ) = (r : ℝ) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by exact_mod_cast ha) (by exact_mod_cast hr)]
    exact_mod_cast hsq.symm
  rw [sqrt_finite f mode tininess n ha, hsqrt, roundingFlags_ratCast]
  exact roundingFlags_of_representable f mode tininess h

theorem convert_eq_empty_of_representable (n : Bool) {a : ℚ} (h : Representable f a) :
    convert f mode tininess (.finite n a) = Flags.empty :=
  roundingFlags_of_representable f mode tininess h

/-- Representability is preserved by a destination format with at least the
precision, at least the subnormal range and at least the finite range. -/
theorem representable_mono {f g : Format} {x : ℚ} (h : Representable f x)
    (hp : f.mantissaBits ≤ g.mantissaBits) (hq : minQuantum g ≤ minQuantum f)
    (hmax : maxFinite f ≤ (maxFinite g : ℚ)) : Representable g x := by
  obtain ⟨n, q, rfl, hn, hq', hx⟩ := h
  refine ⟨n, q, rfl, lt_of_lt_of_le hn (pow_le_pow_right₀ (by norm_num) hp), le_trans hq hq',
    le_trans hx hmax⟩

/-- Every finite binary32 value is a finite binary64 value. -/
theorem representable_binary64_of_binary32 {x : ℚ} (h : Representable Format.binary32 x) :
    Representable Format.binary64 x :=
  representable_mono h (by decide) (by decide) (by decide +kernel)

/-- Conversion of a finite value to a format that contains it raises no flags. -/
theorem convert_binary32_to_binary64 (n : Bool) {a : ℚ} (h : Representable Format.binary32 a) :
    convert Format.binary64 mode tininess (.finite n a) = Flags.empty :=
  convert_eq_empty_of_representable Format.binary64 mode tininess n
    (representable_binary64_of_binary32 h)

/-- An integer that is a finite value of the format converts without flags. The
magnitude bound for binary64 (every integer below `2 ^ 53` in magnitude, so every
32-bit integer) is `F64.ofIntFlags_of_natAbs_lt`. -/
theorem ofInt_eq_empty_of_representable {n : ℤ} (h : Representable f (n : ℚ)) :
    ofInt f mode tininess n = Flags.empty :=
  roundingFlags_of_representable f mode tininess h

/-- A bounded integer rounding: invalid exactly when out of range, otherwise
inexact exactly for the `Exact` forms and a nonintegral operand. -/
theorem toInt_finite (target : IntFormat) (signalsInexact : Bool) (n : Bool) (a : ℚ) :
    toInt target mode signalsInexact (.finite n a) =
      if roundInt mode a < target.minValue ∨ target.maxValue < roundInt mode a then invalid
      else if signalsInexact && decide ((roundInt mode a : ℚ) ≠ a) then inexactOnly
      else Flags.empty := rfl

theorem toInt_invalid_iff (target : IntFormat) (signalsInexact : Bool) (x : Datum) :
    (toInt target mode signalsInexact x).invalidOperation = true ↔
      ∀ n a, x = .finite n a →
        roundInt mode a < target.minValue ∨ target.maxValue < roundInt mode a := by
  cases x with
  | nan s => simp [toInt]
  | infinity n => simp [toInt]
  | finite n a =>
    simp only [toInt_finite, Datum.finite.injEq, and_imp]
    constructor
    · intro h n' a' _ ha
      subst ha
      by_contra hr
      simp only [hr, ↓reduceIte] at h
      split at h <;> simp at h
    · intro h
      simp [h n a rfl rfl]

/-- Rounding an integral operand raises nothing. -/
theorem roundToIntegral_intCast (signalsInexact : Bool) (n : Bool) (k : ℤ) :
    roundToIntegral mode signalsInexact (.finite n (k : ℚ)) = Flags.empty := by
  simp [roundToIntegral]

end Exact

end Silmaril.Numeric.Ieee754.FlagSpec
