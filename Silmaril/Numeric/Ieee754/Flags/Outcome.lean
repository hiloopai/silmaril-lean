module

public import Silmaril.Numeric.Ieee754.Flags.Operations

/-!
# Operation outcomes before rounding

`Outcome` separates what an operation determines from its operands (IEEE
754-2019 §§5.4, 7.2, 7.3) from what the rounding stage determines (§§7.4–7.6).
An outcome is invalid, a propagated quiet NaN, an exact infinity, a division by
zero, or an exact finite result (a rational, or the square root of a rational).
A `RoundingStage` classifies the finite outcomes; `RoundingStage.ieee` is the
default classification by `roundingFlags` and `sqrtRoundingFlags`.

This seam is where architecture profiles attach non-IEEE behaviour. Input
flushing (denormals-are-zero) changes the operands before the outcome is
computed, and output flushing (flush-to-zero) replaces the rounding stage; see
`Numeric.Ieee754.Flags.Denormal`. The theorems `add_eq_outcome` and its
siblings show that the flag functions of `Numeric.Ieee754.Flags.Operations` are
exactly `Outcome.flags` with the IEEE stage.

Outcomes do not select zero signs or NaN payloads; those are properties of the
delivered value, which this development does not fix.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.FlagSpec

open Float.Model

/-- The result of an operation before rounding to its destination. -/
inductive Outcome where
  /-- Invalid operation (§7.2); the default result is a quiet NaN. -/
  | invalid
  /-- A quiet NaN operand propagates without an exception (§6.2). -/
  | nan
  /-- An exact infinity computed from infinite operands (§6.1). -/
  | infinity (negative : Bool)
  /-- A finite nonzero dividend divided by zero (§7.3); the default result is
  an infinity of the given sign. -/
  | divideByZero (negative : Bool)
  /-- An exact finite rational result, still to be rounded. -/
  | finite (value : ℚ)
  /-- The exact result `√radicand` with `0 ≤ radicand`, still to be rounded. -/
  | sqrt (radicand : ℚ)
  deriving DecidableEq, Repr

/-- The classification of finite exact results by a destination rounding. -/
structure RoundingStage where
  finite : ℚ → Flags
  sqrt : ℚ → Flags

/-- The IEEE 754-2019 default classification (§§7.4–7.6). -/
def RoundingStage.ieee (f : Format) (mode : RoundingMode) (tininess : Tininess) : RoundingStage :=
  ⟨roundingFlags f mode tininess, sqrtRoundingFlags f mode tininess⟩

/-- The flags raised by an outcome under a rounding stage. -/
def Outcome.flags (stage : RoundingStage) : Outcome → Flags
  | .invalid => FlagSpec.invalid
  | .nan => Flags.empty
  | .infinity _ => Flags.empty
  | .divideByZero _ => FlagSpec.divideByZero
  | .finite value => stage.finite value
  | .sqrt radicand => stage.sqrt radicand

/-- Outcome of addition. -/
def addOutcome (x y : Datum) : Outcome :=
  if x.isSignaling || y.isSignaling then .invalid
  else match x, y with
    | .nan _, _ | _, .nan _ => .nan
    | .infinity a, .infinity b => if a = b then .infinity a else .invalid
    | .infinity a, .finite .. => .infinity a
    | .finite .., .infinity b => .infinity b
    | .finite _ a, .finite _ b => .finite (a + b)

/-- Outcome of subtraction. -/
def subOutcome (x y : Datum) : Outcome := addOutcome x y.neg

/-- Outcome of multiplication. -/
def mulOutcome (x y : Datum) : Outcome :=
  if x.isSignaling || y.isSignaling then .invalid
  else match x, y with
    | .nan _, _ | _, .nan _ => .nan
    | .infinity _, .infinity _ => .infinity (x.negative ^^ y.negative)
    | .infinity _, .finite _ b | .finite _ b, .infinity _ =>
      if b = 0 then .invalid else .infinity (x.negative ^^ y.negative)
    | .finite _ a, .finite _ b => .finite (a * b)

/-- Outcome of division. -/
def divOutcome (x y : Datum) : Outcome :=
  if x.isSignaling || y.isSignaling then .invalid
  else match x, y with
    | .nan _, _ | _, .nan _ => .nan
    | .infinity _, .infinity _ => .invalid
    | .infinity _, .finite .. => .infinity (x.negative ^^ y.negative)
    | .finite .., .infinity _ => .finite 0
    | .finite _ a, .finite _ b =>
      if b = 0 then (if a = 0 then .invalid else .divideByZero (x.negative ^^ y.negative))
      else .finite (a / b)

/-- Outcome of square root. -/
def sqrtOutcome : Datum → Outcome
  | .nan signaling => if signaling then .invalid else .nan
  | .infinity negative => if negative then .invalid else .infinity false
  | .finite _ a => if a < 0 then .invalid else .sqrt a

/-- Outcome of fused multiply-add. -/
def fmaOutcome (policy : FmaQuietAddend) (x y z : Datum) : Outcome :=
  if x.isSignaling || y.isSignaling || z.isSignaling then .invalid
  else if zeroTimesInfinity x y then
    if z.isNaN then
      (match policy with | .signalInvalid => .invalid | .noSignal => .nan)
    else .invalid
  else match x, y, z with
    | .nan _, _, _ | _, .nan _, _ | _, _, .nan _ => .nan
    | .finite _ a, .finite _ b, .finite _ c => .finite (a * b + c)
    | .finite .., .finite .., .infinity negative => .infinity negative
    | _, _, .infinity negative =>
      if negative = (x.negative ^^ y.negative) then .infinity negative else .invalid
    | _, _, _ => .infinity (x.negative ^^ y.negative)

/-- Outcome of conversion between formats. -/
def convertOutcome : Datum → Outcome
  | .nan signaling => if signaling then .invalid else .nan
  | .infinity negative => .infinity negative
  | .finite _ value => .finite value

/-- Outcome of integer-to-float conversion. -/
def ofIntOutcome (n : ℤ) : Outcome := .finite n

section Agreement

variable (f : Format) (mode : RoundingMode) (tininess : Tininess)

theorem add_eq_outcome (x y : Datum) :
    add f mode tininess x y = (addOutcome x y).flags (.ieee f mode tininess) := by
  unfold add addOutcome
  split
  · rfl
  · cases x <;> cases y <;> simp only [Outcome.flags] <;> first | rfl | (split <;> rfl)

theorem sub_eq_outcome (x y : Datum) :
    sub f mode tininess x y = (subOutcome x y).flags (.ieee f mode tininess) :=
  add_eq_outcome f mode tininess x y.neg

theorem mul_eq_outcome (x y : Datum) :
    mul f mode tininess x y = (mulOutcome x y).flags (.ieee f mode tininess) := by
  unfold mul mulOutcome
  split
  · rfl
  · cases x <;> cases y <;> simp only [Outcome.flags] <;> first | rfl | (split <;> rfl)

theorem div_eq_outcome (x y : Datum) :
    div f mode tininess x y = (divOutcome x y).flags (.ieee f mode tininess) := by
  unfold div divOutcome
  split
  · rfl
  · cases x <;> cases y <;> simp only [Outcome.flags] <;>
      first
        | rfl
        | (split_ifs <;> rfl)
        | simp [RoundingStage.ieee]

theorem sqrt_eq_outcome (x : Datum) :
    sqrt f mode tininess x = (sqrtOutcome x).flags (.ieee f mode tininess) := by
  cases x with
  | nan s => cases s <;> rfl
  | infinity n => cases n <;> rfl
  | finite n a =>
    simp only [sqrt, sqrtOutcome]
    split <;> rfl

theorem fma_eq_outcome (policy : FmaQuietAddend) (x y z : Datum) :
    fma policy f mode tininess x y z = (fmaOutcome policy x y z).flags (.ieee f mode tininess) := by
  unfold fma fmaOutcome
  split
  · rfl
  · split
    · split
      · cases policy <;> rfl
      · rfl
    · cases x <;> cases y <;> cases z <;> simp only [Outcome.flags] <;>
        first | rfl | (split <;> rfl)

theorem convert_eq_outcome (x : Datum) :
    convert f mode tininess x = (convertOutcome x).flags (.ieee f mode tininess) := by
  cases x with
  | nan s => cases s <;> rfl
  | infinity n => rfl
  | finite n a => rfl

theorem ofInt_eq_outcome (n : ℤ) :
    ofInt f mode tininess n = (ofIntOutcome n).flags (.ieee f mode tininess) := rfl

end Agreement

end Silmaril.Numeric.Ieee754.FlagSpec
