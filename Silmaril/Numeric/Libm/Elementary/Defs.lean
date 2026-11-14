module

public import Silmaril.Numeric.Libm.Binary64.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Batch 2: the elementary `double` functions

`exp`, `exp2`, `exp10`, `expm1`, `log`, `log2`, `log10`, `log1p`, `pow`, `cbrt`,
`hypot`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`,
`tanh`, `asinh`, `acosh`, `atanh`, `tgamma` and `lgamma`.

Each `Spec` takes its exact result from Mathlib's real functions (`Real.exp`,
`Real.log`, `Real.logb`, `Real.rpow`, `Real.sin`, `Real.arctan`, `Complex.arg`,
`Real.arsinh`, `Real.Gamma`, …) on the finite inputs of its domain, and lists
the special cases of C 2018 Annex F.10 with the flags and `errno` of §7.12.1.
Every function also has the generic overflow range error (`B64.overflow`).
Results are rounded by the lattice nodes: `CorrectlyRounded`, `ErrorGlobal k`,
`CRWithin n` (see `Silmaril.Numeric.Libm.Glibc.Defs` for documented bounds).

Constants that Annex F gives as `±π`, `±π/2`, `±3π/4` or `±π/4` are required to
be correctly rounded (`Expect.near`).

Not specified yet: `erf`, `erfc`, the Bessel functions, `fma`, `nextafter`,
`ilogb`/`logb`, `remquo`, `lrint`/`lround` and the `float`/`long double`
variants.
-/

@[expose] public section

namespace Silmaril.Numeric.Libm.Double

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec Silmaril.Numeric.Libm.B64
open Real

/-- A unary function with exact result `R` on finite inputs in `D`: NaN
propagation, the listed Annex F cases and the overflow range error. -/
noncomputable def unary (name : String) (D : ℝ → Prop) (R : ℝ → ℝ)
    (cases : List (SpecialCase F64 F64)) : Spec F64 F64 where
  name := name
  exact := onFinite D R
  special := nanIn :: cases ++ [overflow (onFinite D R)]

/-! ## Exponentials and logarithms -/

/-- The special cases shared by `exp`, `exp2` and `exp10` (Annex F.10.3.1–2). -/
def expCases (name : String) : List (SpecialCase F64 F64) :=
  [const s!"{name}(±0) = 1" isZero one, const s!"{name}(-∞) = +0" isNegInf posZero,
    const s!"{name}(+∞) = +∞" isPosInf posInf]

noncomputable def exp : Spec F64 F64 := unary "exp" (fun _ => True) Real.exp (expCases "exp")
noncomputable def exp2 : Spec F64 F64 :=
  unary "exp2" (fun _ => True) (fun a => (2 : ℝ) ^ a) (expCases "exp2")
/-- `exp10` (C23 §7.12.6.4). -/
noncomputable def exp10 : Spec F64 F64 :=
  unary "exp10" (fun _ => True) (fun a => (10 : ℝ) ^ a) (expCases "exp10")

/-- `expm1` (Annex F.10.3.3). -/
noncomputable def expm1 : Spec F64 F64 :=
  unary "expm1" (fun _ => True) (fun a => Real.exp a - 1)
    [same "expm1(±0) = ±0" isZero, const "expm1(+∞) = +∞" isPosInf posInf,
      const "expm1(-∞) = -1" isNegInf negOne]

/-- The special cases shared by `log`, `log2` and `log10` (Annex F.10.3.7–8, 11). -/
def logCases (name : String) : List (SpecialCase F64 F64) :=
  [poleError s!"{name}(±0) = -∞" isZero (fun _ => negInf),
    const s!"{name}(1) = +0" (isValue 1) posZero,
    domainError s!"{name}(x < 0)" ltZero,
    const s!"{name}(+∞) = +∞" isPosInf posInf]

noncomputable def log : Spec F64 F64 := unary "log" (0 < ·) Real.log (logCases "log")
noncomputable def log2 : Spec F64 F64 := unary "log2" (0 < ·) (Real.logb 2) (logCases "log2")
noncomputable def log10 : Spec F64 F64 := unary "log10" (0 < ·) (Real.logb 10) (logCases "log10")

/-- `log1p` (Annex F.10.3.9). -/
noncomputable def log1p : Spec F64 F64 :=
  unary "log1p" (-1 < ·) (fun a => Real.log (1 + a))
    [same "log1p(±0) = ±0" isZero, poleError "log1p(-1) = -∞" (isValue (-1)) (fun _ => negInf),
      domainError "log1p(x < -1)" (below (-1)), const "log1p(+∞) = +∞" isPosInf posInf]

/-! ## Powers and roots -/

/-- `cbrt` (Annex F.10.4.1): the real cube root. -/
noncomputable def cbrt : Spec F64 F64 :=
  unary "cbrt" (fun _ => True) (fun a => if a < 0 then -(|a| ^ (1 / 3 : ℝ)) else |a| ^ (1 / 3 : ℝ))
    [same "cbrt(±0) = ±0" isZero, same "cbrt(±∞) = ±∞" isInf]

/-- `hypot` (Annex F.10.4.3): an infinite argument gives `+∞`, even with a NaN. -/
noncomputable def hypot : Spec (F64 × F64) F64 where
  name := "hypot"
  exact := onFinite2 (fun _ _ => True) (fun a b => Real.sqrt (a ^ 2 + b ^ 2))
  special :=
    [const "hypot(±∞, y) = hypot(x, ±∞) = +∞" (fun p => isInf p.1 || isInf p.2) posInf,
      { name := "hypot with a NaN and no infinity"
        applies := fun p => (isNaN p.1 || isNaN p.2) && !isInf p.1 && !isInf p.2
        expect := fun _ => .nan },
      overflow (onFinite2 (fun _ _ => True) (fun a b => Real.sqrt (a ^ 2 + b ^ 2)))]

/-- The exact domain of `pow`: positive bases, negative bases with integral
exponents, and zero bases with nonnegative exponents. -/
def PowDomain (a b : ℝ) : Prop := 0 < a ∨ (a < 0 ∧ ∃ n : ℤ, b = n) ∨ (a = 0 ∧ 0 ≤ b)

/-- `pow` (Annex F.10.4.4). The exact result is `Real.rpow`, which agrees with
the integer power on negative bases (`Real.rpow_intCast`). -/
noncomputable def pow : Spec (F64 × F64) F64 where
  name := "pow"
  exact := onFinite2 PowDomain (fun a b => a ^ b)
  special :=
    [const "pow(x, ±0) = 1 for any x, even a NaN" (fun p => isZero p.2) one,
      const "pow(+1, y) = 1 for any y, even a NaN" (fun p => p.1 == one) one,
      { name := "pow with a NaN otherwise"
        applies := fun p => (isNaN p.1 || isNaN p.2) && !isZero p.2 && !(p.1 == one)
        expect := fun _ => .nan },
      poleError "pow(±0, y) = ±∞ for odd integral y < 0"
        (fun p => isZero p.1 && isOddInteger p.2 && ltZero p.2) (fun p => F64.copySign posInf p.1),
      const "pow(±0, -∞) = +∞" (fun p => isZero p.1 && isNegInf p.2) posInf,
      poleError "pow(±0, y) = +∞ for finite y < 0, not an odd integer"
        (fun p => isZero p.1 && isFinite p.2 && ltZero p.2 && !isOddInteger p.2) (fun _ => posInf),
      { name := "pow(±0, y) = ±0 for odd integral y > 0"
        applies := fun p => isZero p.1 && isOddInteger p.2 && gtZero p.2
        expect := fun p => .bits p.1 },
      const "pow(±0, y) = +0 for y > 0, not an odd integer"
        (fun p => isZero p.1 && gtZero p.2 && !isOddInteger p.2) posZero,
      const "pow(-1, ±∞) = 1" (fun p => p.1 == negOne && isInf p.2) one,
      domainError "pow(x, y) for finite x < 0 and finite non-integral y"
        (fun p => isFinite p.1 && ltZero p.1 && isFinite p.2 && !isInteger p.2),
      const "pow(x, -∞) = +∞ for |x| < 1" (fun p => absLtOne p.1 && isNegInf p.2) posInf,
      const "pow(x, -∞) = +0 for |x| > 1" (fun p => absGtOne p.1 && isNegInf p.2) posZero,
      const "pow(x, +∞) = +0 for |x| < 1" (fun p => absLtOne p.1 && isPosInf p.2) posZero,
      const "pow(x, +∞) = +∞ for |x| > 1" (fun p => absGtOne p.1 && isPosInf p.2) posInf,
      const "pow(-∞, y) = -0 for odd integral y < 0"
        (fun p => isNegInf p.1 && isOddInteger p.2 && ltZero p.2) negZero,
      const "pow(-∞, y) = +0 for y < 0, not an odd integer"
        (fun p => isNegInf p.1 && ltZero p.2 && !isOddInteger p.2) posZero,
      const "pow(-∞, y) = -∞ for odd integral y > 0"
        (fun p => isNegInf p.1 && isOddInteger p.2 && gtZero p.2) negInf,
      const "pow(-∞, y) = +∞ for y > 0, not an odd integer"
        (fun p => isNegInf p.1 && gtZero p.2 && !isOddInteger p.2) posInf,
      const "pow(+∞, y) = +0 for y < 0" (fun p => isPosInf p.1 && ltZero p.2) posZero,
      const "pow(+∞, y) = +∞ for y > 0" (fun p => isPosInf p.1 && gtZero p.2) posInf,
      overflow (onFinite2 PowDomain (fun a b => a ^ b))]

/-! ## Trigonometric functions -/

noncomputable def sin : Spec F64 F64 :=
  unary "sin" (fun _ => True) Real.sin
    [same "sin(±0) = ±0" isZero, domainError "sin(±∞)" isInf]

noncomputable def cos : Spec F64 F64 :=
  unary "cos" (fun _ => True) Real.cos
    [const "cos(±0) = 1" isZero one, domainError "cos(±∞)" isInf]

noncomputable def tan : Spec F64 F64 :=
  unary "tan" (fun a => Real.cos a ≠ 0) Real.tan
    [same "tan(±0) = ±0" isZero, domainError "tan(±∞)" isInf]

/-- Inputs outside `[-1, 1]`, infinities included. -/
def outsideUnit (x : F64) : Bool := absGtOne x

noncomputable def asin : Spec F64 F64 :=
  unary "asin" (fun a => |a| ≤ 1) Real.arcsin
    [same "asin(±0) = ±0" isZero, domainError "asin(|x| > 1)" outsideUnit]

noncomputable def acos : Spec F64 F64 :=
  unary "acos" (fun a => |a| ≤ 1) Real.arccos
    [const "acos(1) = +0" (isValue 1) posZero, domainError "acos(|x| > 1)" outsideUnit]

noncomputable def atan : Spec F64 F64 :=
  unary "atan" (fun _ => True) Real.arctan
    [same "atan(±0) = ±0" isZero, near "atan(±∞) = ±π/2" isInf (fun x => withSignOf x (π / 2))]

/-- `atan2(y, x)` (Annex F.10.1.4): the argument of `x + iy`. -/
noncomputable def atan2 : Spec (F64 × F64) F64 where
  name := "atan2"
  exact := onFinite2 (fun y _ => y ≠ 0) (fun y x => Complex.arg ⟨x, y⟩)
  special :=
    [nanIn2,
      { name := "atan2(±0, x) = ±0 for x > 0 or x = +0"
        applies := fun p => isZero p.1 && !isNaN p.2 && !p.2.signBit
        expect := fun p => .bits (F64.copySign posZero p.1) },
      near "atan2(±0, x) = ±π for x < 0 or x = -0" (fun p => isZero p.1 && isNeg p.2)
        (fun p => withSignOf p.1 π),
      near "atan2(±y, -∞) = ±π for finite y > 0"
        (fun p => isFinite p.1 && !isZero p.1 && isNegInf p.2) (fun p => withSignOf p.1 π),
      { name := "atan2(±y, +∞) = ±0 for finite y > 0"
        applies := fun p => isFinite p.1 && !isZero p.1 && isPosInf p.2
        expect := fun p => .bits (F64.copySign posZero p.1) },
      near "atan2(±∞, x) = ±π/2 for finite x" (fun p => isInf p.1 && isFinite p.2)
        (fun p => withSignOf p.1 (π / 2)),
      near "atan2(±∞, -∞) = ±3π/4" (fun p => isInf p.1 && isNegInf p.2)
        (fun p => withSignOf p.1 (3 * π / 4)),
      near "atan2(±∞, +∞) = ±π/4" (fun p => isInf p.1 && isPosInf p.2)
        (fun p => withSignOf p.1 (π / 4))]

/-! ## Hyperbolic functions -/

noncomputable def sinh : Spec F64 F64 :=
  unary "sinh" (fun _ => True) Real.sinh [same "sinh(±0) = ±0" isZero, same "sinh(±∞) = ±∞" isInf]

noncomputable def cosh : Spec F64 F64 :=
  unary "cosh" (fun _ => True) Real.cosh
    [const "cosh(±0) = 1" isZero one, const "cosh(±∞) = +∞" isInf posInf]

noncomputable def tanh : Spec F64 F64 :=
  unary "tanh" (fun _ => True) Real.tanh
    [same "tanh(±0) = ±0" isZero, const "tanh(+∞) = +1" isPosInf one,
      const "tanh(-∞) = -1" isNegInf negOne]

noncomputable def asinh : Spec F64 F64 :=
  unary "asinh" (fun _ => True) Real.arsinh
    [same "asinh(±0) = ±0" isZero, same "asinh(±∞) = ±∞" isInf]

noncomputable def acosh : Spec F64 F64 :=
  unary "acosh" (1 ≤ ·) (fun a => Real.log (a + Real.sqrt (a ^ 2 - 1)))
    [const "acosh(1) = +0" (isValue 1) posZero, domainError "acosh(x < 1)" (below 1),
      const "acosh(+∞) = +∞" isPosInf posInf]

noncomputable def atanh : Spec F64 F64 :=
  unary "atanh" (fun a => |a| < 1) (fun a => Real.log ((1 + a) / (1 - a)) / 2)
    [same "atanh(±0) = ±0" isZero,
      poleError "atanh(±1) = ±∞" (fun x => isValue 1 x || isValue (-1) x)
        (fun x => F64.copySign posInf x),
      domainError "atanh(|x| > 1)" outsideUnit]

/-! ## Gamma functions -/

/-- Not a pole of `Γ`: not zero or a negative integer. -/
def GammaDomain (a : ℝ) : Prop := ∀ n : ℕ, a ≠ -(n : ℝ)

/-- `tgamma` (Annex F.10.5.4). -/
noncomputable def tgamma : Spec F64 F64 :=
  unary "tgamma" GammaDomain Real.Gamma
    [poleError "tgamma(±0) = ±∞" isZero (fun x => F64.copySign posInf x),
      domainError "tgamma(x) for a negative integer x" (fun x => ltZero x && isInteger x),
      domainError "tgamma(-∞)" isNegInf, const "tgamma(+∞) = +∞" isPosInf posInf]

/-- `lgamma` (Annex F.10.5.3): `log |Γ(x)|`. -/
noncomputable def lgamma : Spec F64 F64 :=
  unary "lgamma" GammaDomain (fun a => Real.log |Real.Gamma a|)
    [const "lgamma(1) = +0" (isValue 1) posZero, const "lgamma(2) = +0" (isValue 2) posZero,
      poleError "lgamma(x) = +∞ for a nonpositive integer x"
        (fun x => isZero x || (ltZero x && isInteger x)) (fun _ => posInf),
      const "lgamma(±∞) = +∞" isInf posInf]

/-! ## The batch -/

/-- The unary functions of batch 2, by name. -/
noncomputable def batch2Unary : List (Spec F64 F64) :=
  [exp, exp2, exp10, expm1, log, log2, log10, log1p, cbrt, sin, cos, tan, asin, acos, atan,
    sinh, cosh, tanh, asinh, acosh, atanh, tgamma, lgamma]

/-- Batch 2, in catalogue form. -/
noncomputable def batch2 : List Entry :=
  batch2Unary.map Spec.entry ++ [pow.entry, hypot.entry, atan2.entry]

end Silmaril.Numeric.Libm.Double
