module

public import Silmaril.Numeric.Ieee754.Operations
public import Silmaril.Numeric.Ieee754.Exact

/-!
# Short decimal representations of binary64

A finite search over 1–17 significant decimal digits uses exact rational
rounding intervals, including asymmetric intervals at powers of two and the
finite overflow boundary. Within each precision it chooses the closest
accepted decimal, resolving ties to an even coefficient. Exact decimal
expansion is a total fallback, independent of the finite-search bound.

The formatter follows CPython 3.7's repr layout: scientific notation below
1e-4 and at 1e16, at least two exponent digits, and `.0` on integral fixed
representations. The decimal-selection algorithm is independent of that layout.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal

structure Number where
  coefficient : Nat
  exponent : Int
  deriving DecidableEq, Repr

def power (exponent : Int) : ℚ := (10 : ℚ) ^ exponent

def Number.value (number : Number) : ℚ := number.coefficient * power number.exponent

/-- Rational value of an interchange representation; the caller handles
nonfinite values separately. -/
def rational (bits : UInt64) : ℚ :=
  (Conformance.value? (F64.ofBits bits).model.unpack).getD 0

structure Interval where
  lower : ℚ
  upper : ℚ
  includeEnds : Bool
  deriving Repr

def Interval.accepts (interval : Interval) (value : ℚ) : Bool :=
  if interval.includeEnds then decide (interval.lower ≤ value ∧ value ≤ interval.upper)
  else decide (interval.lower < value ∧ value < interval.upper)

/-- Nonzero positive finite encodings are ordered by their unsigned bits.
At maximum finite, extrapolate the next spacing to the overflow midpoint. -/
def roundingInterval (bits : UInt64) : Interval :=
  let value := rational bits
  let previous := rational (bits - 1)
  let following := if bits == 0x7fefffffffffffff then value + (value - previous)
    else rational (bits + 1)
  ⟨(previous + value) / 2, (value + following) / 2, bits.toNat % 2 == 0⟩

/-- Initial exponent estimate uses decimal lengths, then makes one exact
comparison. Intended for positive rationals. -/
def decade (value : ℚ) : Int :=
  let estimate : Int := (toString value.num.natAbs).length - (toString value.den).length
  if value < power estimate then estimate - 1 else estimate

/-- Adjacent decimal lattice points suffice at each precision. Prefer the
closest admissible one, with an even-coefficient tie break. -/
def candidate (interval : Interval) (value : ℚ) (digits : Nat) : Option Number :=
  let exponent := decade value - (digits : Int) + 1
  let scaled := value / power exponent
  let lower := scaled.num.toNat / scaled.den
  let a : Number := ⟨lower, exponent⟩
  let b : Number := ⟨lower + 1, exponent⟩
  let acceptableA := lower != 0 && interval.accepts a.value
  let acceptableB := interval.accepts b.value
  if acceptableA && acceptableB then
    if value - a.value < b.value - value then some a
    else if b.value - value < value - a.value then some b
    else if lower % 2 == 0 then some a else some b
  else if acceptableA then some a
  else if acceptableB then some b
  else none

def firstCandidate (interval : Interval) (value : ℚ) : List Nat → Option Number
  | [] => none
  | digits :: rest => (candidate interval value digits).orElse fun _ =>
      firstCandidate interval value rest

/-- Exact dyadic-to-decimal conversion, with no approximation or host float. -/
def exact (bits : UInt64) : Number :=
  match (F64.ofBits bits).model.unpack with
  | .finite _ mantissa exponent _ =>
    if exponent < 0 then ⟨mantissa * 5 ^ (-exponent).toNat, exponent⟩
    else ⟨mantissa * 2 ^ exponent.toNat, 0⟩
  | _ => ⟨0, 0⟩

def shortest (bits : UInt64) : Number :=
  (firstCandidate (roundingInterval bits) (rational bits) (List.range' 1 17)).getD (exact bits)

/-- Removing trailing coefficient zeros preserves its mathematical value. -/
def trim : Nat → Number → Number
  | 0, number => number
  | fuel + 1, number =>
    if number.coefficient != 0 && number.coefficient % 10 == 0 then
      trim fuel ⟨number.coefficient / 10, number.exponent + 1⟩
    else number

def zeros (count : Nat) : String := String.ofList (List.replicate count '0')

def exponentString (exponent : Int) : String :=
  let digits := toString exponent.natAbs
  (if exponent < 0 then "-" else "+") ++ zeros (2 - digits.length) ++ digits

def layout (input : Number) : String :=
  let number := trim (toString input.coefficient).length input
  let digits := (toString number.coefficient).toList
  let point : Int := (digits.length : Int) + number.exponent
  if point ≤ -4 ∨ 16 < point then
    String.ofList (digits.take 1) ++
      (if digits.length > 1 then "." ++ String.ofList (digits.drop 1) else "") ++
      "e" ++ exponentString (point - 1)
  else if point ≤ 0 then
    "0." ++ zeros (-point).toNat ++ String.ofList digits
  else if point.toNat < digits.length then
    String.ofList (digits.take point.toNat) ++ "." ++ String.ofList (digits.drop point.toNat)
  else String.ofList digits ++ zeros (point.toNat - digits.length) ++ ".0"

/-- Binary64 string conversion; NaN payloads and signs do not appear in text. -/
def repr (bits : UInt64) : String :=
  let value := F64.ofBits bits
  if value.isNaN then "nan"
  else
    let sign := if value.signBit then "-" else ""
    if value.isInfinite then sign ++ "inf"
    else if value.isZero then sign ++ "0.0"
    else sign ++ layout (shortest (bits &&& 0x7fffffffffffffff))

end Silmaril.Numeric.Ieee754.Decimal
