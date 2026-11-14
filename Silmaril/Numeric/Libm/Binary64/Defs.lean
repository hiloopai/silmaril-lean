module

public import Silmaril.Numeric.Libm.Lattice.Defs
public import Silmaril.Numeric.Ieee754.CoreFloat

/-!
# Binary64 vocabulary for libm specifications

Input classifiers, the exact value of a finite input, and builders for the
recurring Annex F special cases (NaN propagation, signed zeros and infinities
returned unchanged, domain and pole errors). Domain errors raise invalid and set
`EDOM`; pole errors raise divide-by-zero and set `ERANGE` (C 2018 §7.12.1).
-/

@[expose] public section

namespace Silmaril.Numeric.Libm.B64

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec

/-! ## Encodings and classifiers -/

/-- The binary64 encoding of a Lean `Float`, for writing constants and tests. -/
def d (x : Float) : F64 := F64.ofFloat x

def posZero : F64 := F64.zero
def negZero : F64 := F64.negativeZero
def posInf : F64 := F64.infinity
def negInf : F64 := F64.neg F64.infinity
def one : F64 := F64.one
def negOne : F64 := F64.neg F64.one

def isNaN (x : F64) : Bool := x.isNaN
def isZero (x : F64) : Bool := x.isZero
def isInf (x : F64) : Bool := x.isInfinite
def isFinite (x : F64) : Bool := x.isFinite
def isPosInf (x : F64) : Bool := x == posInf
def isNegInf (x : F64) : Bool := x == negInf
/-- Sign bit set, on a non-NaN: negative numbers, `-0` and `-∞`. -/
def isNeg (x : F64) : Bool := !x.isNaN && x.signBit
/-- Strictly below zero, `-∞` included. -/
def ltZero (x : F64) : Bool := isNeg x && !x.isZero
/-- Strictly above zero, `+∞` included. -/
def gtZero (x : F64) : Bool := !x.isNaN && !x.signBit && !x.isZero

/-- The exact value of a finite encoding (both zeros give `0`). -/
def value? (x : F64) : Option ℚ := x.toRat?

/-- A finite input with value strictly below `lo` or strictly above `hi`. -/
def outside (lo hi : ℚ) (x : F64) : Bool :=
  match x.toRat? with
  | some a => decide (a < lo) || decide (hi < a)
  | none => false

/-- A finite input equal to `q`. -/
def isValue (q : ℚ) (x : F64) : Bool := x.toRat? == some q

/-- A finite value below `q`, or `-∞`. -/
def below (q : ℚ) (x : F64) : Bool :=
  isNegInf x || match x.toRat? with
    | some a => decide (a < q)
    | none => false

/-- A finite value above `q`, or `+∞`. -/
def above (q : ℚ) (x : F64) : Bool :=
  isPosInf x || match x.toRat? with
    | some a => decide (q < a)
    | none => false

/-- A finite value of magnitude below one. -/
def absLtOne (x : F64) : Bool :=
  match x.toRat? with
  | some a => decide (|a| < 1)
  | none => false

/-- A value of magnitude above one, infinities included. -/
def absGtOne (x : F64) : Bool := below (-1) x || above 1 x

/-- An integral finite value (infinities are not integers here). -/
def isInteger (x : F64) : Bool :=
  match x.toRat? with
  | some a => a.den == 1
  | none => false

/-- An odd integral value. -/
def isOddInteger (x : F64) : Bool :=
  match x.toRat? with
  | some a => a.den == 1 && a.num % 2 == 1
  | none => false

/-- The positive value of a nonzero rational with the sign bit of `x`. -/
def withSignOf (x : F64) (r : ℝ) : ℝ := if x.signBit then -r else r

/-! ## Exact results on finite inputs -/

open Classical in
/-- The exact result `R a` of a unary function on finite inputs `a` with `D a`. -/
noncomputable def onFinite (D : ℝ → Prop) (R : ℝ → ℝ) (x : F64) : Option ℝ :=
  match x.toRat? with
  | some a => if D a then some (R a) else none
  | none => none

open Classical in
/-- The exact result `R a b` of a binary function on finite inputs with `D a b`. -/
noncomputable def onFinite2 (D : ℝ → ℝ → Prop) (R : ℝ → ℝ → ℝ) (p : F64 × F64) : Option ℝ :=
  match p.1.toRat?, p.2.toRat? with
  | some a, some b => if D a b then some (R a b) else none
  | _, _ => none

/-! ## Special-case builders -/

/-- `f(NaN)` is a NaN. -/
def nanIn (name : String := "f(NaN) = NaN") : SpecialCase F64 F64 :=
  { name, applies := isNaN, expect := fun _ => .nan }

/-- `f(x, y)` is a NaN when either argument is. -/
def nanIn2 (name : String := "f(NaN, y) = f(x, NaN) = NaN") : SpecialCase (F64 × F64) F64 :=
  { name, applies := fun p => isNaN p.1 || isNaN p.2, expect := fun _ => .nan }

/-- `f(x) = x`, bit for bit, on the inputs `p` (for example `sin(±0) = ±0`). -/
def same (name : String) (p : F64 → Bool) : SpecialCase F64 F64 :=
  { name, applies := p, expect := fun x => .bits x }

/-- `f(x) = y`, bit for bit, on the inputs `p`. -/
def const {α : Type} (name : String) (p : α → Bool) (y : F64) : SpecialCase α F64 :=
  { name, applies := p, expect := fun _ => .bits y }

/-- `f(x)` is the correctly rounded value of the real constant `r(x)`. -/
def near {α : Type} (name : String) (p : α → Bool) (r : α → ℝ) : SpecialCase α F64 :=
  { name, applies := p, expect := fun x => .near (r x) }

/-- Invalid operation flag. -/
def invalid : Flags := Flags.singleton .invalidOperation

/-- Divide-by-zero flag. -/
def divByZero : Flags := Flags.singleton .divisionByZero

/-- Overflow and inexact flags. -/
def overflowFlags : Flags := Flags.union (Flags.singleton .overflow) (Flags.singleton .inexact)

/-- A domain error: a NaN, invalid, and `errno = EDOM`. -/
def domainError {α : Type} (name : String) (p : α → Bool) : SpecialCase α F64 :=
  { name, applies := p, expect := fun _ => .nan, raises := invalid, errno := some .edom }

/-- A pole error: an exact infinity `y`, divide-by-zero, and `errno = ERANGE`. -/
def poleError {α : Type} (name : String) (p : α → Bool) (y : α → F64) : SpecialCase α F64 :=
  { name, applies := p, expect := fun x => .bits (y x), raises := divByZero, errno := some .erange }

open Classical in
/-- A range error by overflow: when the exact result overflows binary64 under
round-to-nearest, the overflow and inexact flags are raised and `errno` is
`ERANGE` (C 2018 §7.12.1, Annex F.10). The returned value is left to the
accuracy nodes (an overflowing correctly rounded result is `±∞`). -/
noncomputable def overflow {α : Type} (exact : α → Option ℝ) : SpecialCase α F64 where
  name := "overflow: range error"
  applies x := decide (∃ r, exact x = some r ∧ Overflows .binary64 .nearestTiesToEven r)
  expect _ := .any
  raises := overflowFlags
  errno := some .erange

/-! ## Executable checks on sample inputs -/

/-- Check an expectation on a returned encoding. `near` constants are not checked
here (they are real numbers); `any` always passes. -/
def check : Expect F64 → F64 → Bool
  | .nan, y => y.isNaN
  | .bits z, y => y == z
  | .near _, _ => true
  | .any, _ => true

/-- Every applicable special case holds for `ref` on the sample inputs `xs`. -/
def checkCases {α : Type} (cases : List (SpecialCase α F64)) (ref : α → F64) (xs : List α) : Bool :=
  xs.all fun x => cases.all fun c => !c.applies x || check (c.expect x) (ref x)

/-- Sample inputs: both zeros, both infinities, a quiet and a signaling NaN, the
smallest subnormal, the largest finite number, halfway cases and ordinary values. -/
def samples : List F64 :=
  [posZero, negZero, posInf, negInf, F64.canonicalNaN, F64.ofBits 0x7ff0000000000001,
    F64.ofBits 1, F64.maxFinite, d 0.5, d (-0.5), d 1.0, d (-1.0), d 1.5, d (-1.5), d 2.5,
    d (-2.5), d 3.75, d (-3.75), d 1e300, d (-1e-300), d 0.1, d 2.0, d (-2.0)]

/-- Sample pairs, from a smaller list. -/
def samplePairs : List (F64 × F64) :=
  let xs := [posZero, negZero, posInf, negInf, F64.canonicalNaN, F64.ofBits 1, d 1.0, d (-1.5),
    d 2.5, d (-7.0), d 0.1, d 1e300]
  xs.flatMap fun x => xs.map fun y => (x, y)

end Silmaril.Numeric.Libm.B64
