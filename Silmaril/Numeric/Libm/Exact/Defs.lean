module

public import Silmaril.Numeric.Libm.Binary64.Defs

/-!
# Batch 1: the exact and correctly rounded `double` functions

`fabs`, `copysign`, `floor`, `ceil`, `trunc`, `round`, `rint`, `nearbyint`,
`fmod`, `remainder`, `fmin`, `fmax`, `ldexp`, `scalbn`, `sqrt`, `frexp` and
`modf`. Every result of these functions is representable (or, for `sqrt`,
`ldexp` and `scalbn`, correctly rounded) in every conforming libm, so their
specifications pin results down completely.

Each function has a pure reference `Ref.f` on the IEEE model of
`Silmaril.Numeric.Ieee754` and a `Spec` whose `exact` field is the
mathematical result (`roundInt` for the integral roundings, `Real.sqrt`, …).
`rint` and `nearbyint` are specified in the default rounding direction
(round-to-nearest, ties to even): the floating-point environment is not
modelled. `frexp` and `modf` return pairs and are catalogue entries with their
own validity predicates (`FrexpOk`, `ModfOk`).

C 2018 §7.12.6–7.12.12 and Annex F.10.3–F.10.9; IEEE 754-2019 §5.3, §5.5, §9.6.
-/

@[expose] public section

namespace Silmaril.Numeric.Libm.Double

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec Silmaril.Numeric.Libm.B64

/-! ## Pure reference functions -/

namespace Ref

def fabs (x : F64) : F64 := F64.abs x
def copysign (p : F64 × F64) : F64 := F64.copySign p.1 p.2
def floor (x : F64) : F64 := F64.floor x
def ceil (x : F64) : F64 := F64.ceil x
def trunc (x : F64) : F64 := F64.trunc x
/-- C `round`: halfway cases away from zero. -/
def round (x : F64) : F64 := F64.roundIntegral .nearestTiesToAway x
/-- `rint` in the default rounding direction. -/
def rint (x : F64) : F64 := F64.nearest x
/-- `nearbyint` in the default rounding direction (as `rint`, without inexact). -/
def nearbyint (x : F64) : F64 := F64.nearest x
def sqrt (x : F64) : F64 := F64.sqrt x
def fmod (p : F64 × F64) : F64 := F64.fmod p.1 p.2
def remainder (p : F64 × F64) : F64 := F64.remainder p.1 p.2
def fmin (p : F64 × F64) : F64 := F64.minimumNumber p.1 p.2
def fmax (p : F64 × F64) : F64 := F64.maximumNumber p.1 p.2
/-- `ldexp(x, n) = x · 2ⁿ`, rounded once. -/
def ldexp (p : F64 × ℤ) : F64 := F64.scaleB p.1 p.2
def scalbn (p : F64 × ℤ) : F64 := F64.scaleB p.1 p.2

/-- `frexp`: a significand in `[1/2, 1)` and an exponent; zeros, infinities and
NaNs are returned unchanged with exponent `0`. -/
def frexp (x : F64) : F64 × ℤ :=
  match x.toRat? with
  | some a => if a = 0 then (x, 0) else
    let e := Int.log 2 |a| + 1
    (F64.scaleB x (-e), e)
  | none => (x, 0)

/-- `modf`: the fractional and integral parts, both with the sign of `x`. -/
def modf (x : F64) : F64 × F64 :=
  if x.isNaN then (x, x)
  else if x.isInfinite then (F64.copySign F64.zero x, x)
  else
    let i := F64.trunc x
    (F64.copySign (F64.sub x i) x, i)

end Ref

/-! ## Specifications -/

/-- The special cases of `integral`. -/
def integralCases (name : String) (mode : RoundingMode) (inexact : Bool) :
    List (SpecialCase F64 F64) :=
  [nanIn, same s!"{name}(±0) = ±0" isZero, same s!"{name}(±∞) = ±∞" isInf,
    { name := s!"{name}(x) = ±0 has the sign of x"
      applies := fun x => isFinite x && !isZero x && (F64.roundIntegral mode x).isZero
      expect := fun x => .bits (F64.copySign F64.zero x) },
    { name := s!"{name}(x) non-integral raises inexact"
      applies := fun x => inexact && isFinite x && !isInteger x
      expect := fun _ => .any
      raises := Flags.singleton .inexact }]

/-- Integral roundings: `floor`, `ceil`, `trunc`, `round`, `rint`, `nearbyint`
(Annex F.10.6). A zero result keeps the sign of the argument
(`ceil(-0.5) = -0`). `rint` raises inexact when the result differs from the
argument; the others do not. -/
noncomputable def integral (name : String) (mode : RoundingMode) (inexact : Bool) :
    Spec F64 F64 where
  name := name
  exact := onFinite (fun _ => True) (fun a => (roundInt mode a : ℝ))
  special := integralCases name mode inexact

noncomputable def floor : Spec F64 F64 := integral "floor" .towardNegative false
noncomputable def ceil : Spec F64 F64 := integral "ceil" .towardPositive false
noncomputable def trunc : Spec F64 F64 := integral "trunc" .towardZero false
noncomputable def round : Spec F64 F64 := integral "round" .nearestTiesToAway false
noncomputable def rint : Spec F64 F64 := integral "rint" .nearestTiesToEven true
noncomputable def nearbyint : Spec F64 F64 := integral "nearbyint" .nearestTiesToEven false

/-- The special cases of `fabs`. -/
def fabsCases : List (SpecialCase F64 F64) :=
  [nanIn, const "fabs(±0) = +0" isZero posZero, const "fabs(±∞) = +∞" isInf posInf]

/-- `fabs` (Annex F.10.4.2): the magnitude; `fabs(±0) = +0`, `fabs(±∞) = +∞`. -/
noncomputable def fabs : Spec F64 F64 where
  name := "fabs"
  exact := onFinite (fun _ => True) (fun a => |a|)
  special := fabsCases

/-- The special cases of `copysign`. -/
def copysignCases : List (SpecialCase (F64 × F64) F64) :=
  [{ name := "copysign(x, y) on zero, infinite or NaN x is bitwise"
     applies := fun p => !isFinite p.1 || isZero p.1
     expect := fun p => .bits (F64.copySign p.1 p.2) }]

/-- `copysign` (Annex F.10.8.1, IEEE 754 §5.5.1): the magnitude of `x` with the
sign bit of `y`, bit for bit, for NaNs, zeros and infinities too. -/
noncomputable def copysign : Spec (F64 × F64) F64 where
  name := "copysign"
  exact p := (onFinite (fun _ => True) (fun a => withSignOf p.2 |a|) p.1)
  special := copysignCases

/-- The special cases of `sqrt`. -/
def sqrtCases : List (SpecialCase F64 F64) :=
  [nanIn, same "sqrt(±0) = ±0" isZero, const "sqrt(+∞) = +∞" isPosInf posInf,
    domainError "sqrt(x < 0)" ltZero]

/-- `sqrt` (Annex F.10.4.5): correctly rounded; `sqrt(-0) = -0`, and negative
arguments are domain errors. -/
noncomputable def sqrt : Spec F64 F64 where
  name := "sqrt"
  exact := onFinite (0 ≤ ·) Real.sqrt
  special := sqrtCases

/-- The special cases of `fmod`. -/
def fmodCases : List (SpecialCase (F64 × F64) F64) :=
  [nanIn2,
    domainError "fmod(±∞, y)" (fun p => isInf p.1 && !isNaN p.2),
    domainError "fmod(x, ±0)" (fun p => isZero p.2 && !isNaN p.1),
    { name := "fmod(±0, y) = ±0"
      applies := fun p => isZero p.1 && !isZero p.2 && !isNaN p.2
      expect := fun p => .bits p.1 },
    { name := "fmod(x, ±∞) = x"
      applies := fun p => isFinite p.1 && isInf p.2
      expect := fun p => .bits p.1 },
    { name := "a zero fmod has the sign of x"
      applies := fun p => isFinite p.1 && isFinite p.2 && !isZero p.2 && (Ref.fmod p).isZero
      expect := fun p => .bits (F64.copySign F64.zero p.1) }]

/-- `fmod` (§7.12.10.1, Annex F.10.7.1): `x - n·y` with `n = trunc(x / y)`,
exact; the result has the sign of `x`. -/
noncomputable def fmod : Spec (F64 × F64) F64 where
  name := "fmod"
  exact := onFinite2 (fun _ b => b ≠ 0) (fun a b => a - (roundInt .towardZero (a / b) : ℝ) * b)
  special := fmodCases

/-- The special cases of `remainder`. -/
def remainderCases : List (SpecialCase (F64 × F64) F64) :=
  [nanIn2,
    domainError "remainder(±∞, y)" (fun p => isInf p.1 && !isNaN p.2),
    domainError "remainder(x, ±0)" (fun p => isZero p.2 && !isNaN p.1),
    { name := "remainder(x, ±∞) = x"
      applies := fun p => isFinite p.1 && isInf p.2
      expect := fun p => .bits p.1 },
    { name := "a zero remainder has the sign of x"
      applies := fun p => isFinite p.1 && isFinite p.2 && !isZero p.2 && (Ref.remainder p).isZero
      expect := fun p => .bits (F64.copySign F64.zero p.1) }]

/-- `remainder` (§7.12.10.2, Annex F.10.7.2, IEEE 754 §5.3.1): `x - n·y` with `n`
the nearest integer to `x / y`, ties to even; exact; a zero has the sign of `x`. -/
noncomputable def remainder : Spec (F64 × F64) F64 where
  name := "remainder"
  exact := onFinite2 (fun _ b => b ≠ 0)
    (fun a b => a - (roundInt .nearestTiesToEven (a / b) : ℝ) * b)
  special := remainderCases

/-- The special cases of `minmax`. -/
def minmaxCases (name : String) (isMax : Bool) : List (SpecialCase (F64 × F64) F64) :=
  [
    { name := s!"{name}(NaN, y) = y"
      applies := fun p => isNaN p.1 && !isNaN p.2
      expect := fun p => .bits p.2 },
    { name := s!"{name}(x, NaN) = x"
      applies := fun p => !isNaN p.1 && isNaN p.2
      expect := fun p => .bits p.1 },
    { name := s!"{name}(NaN, NaN) = NaN"
      applies := fun p => isNaN p.1 && isNaN p.2
      expect := fun _ => .nan },
    { name := s!"{name} with an infinite argument"
      applies := fun p => !isNaN p.1 && !isNaN p.2 && (isInf p.1 || isInf p.2)
      expect := fun p => .bits (if isMax then Ref.fmax p else Ref.fmin p) }]

/-- `fmin`/`fmax` (§7.12.12, Annex F.10.9.2–3): a NaN argument is treated as
missing data. Either zero may be returned for `(+0, -0)`. -/
noncomputable def minmax (name : String) (isMax : Bool) : Spec (F64 × F64) F64 where
  name := name
  exact := onFinite2 (fun _ _ => True) (fun a b => if isMax then max a b else min a b)
  special := minmaxCases name isMax

noncomputable def fmin : Spec (F64 × F64) F64 := minmax "fmin" false
noncomputable def fmax : Spec (F64 × F64) F64 := minmax "fmax" true

/-- `ldexp`/`scalbn` (§7.12.6.6, §7.12.6.13, Annex F.10.3.6, F.10.3.13): `x · 2ⁿ`,
correctly rounded; zeros and infinities are returned unchanged. -/
noncomputable def scale (name : String) : Spec (F64 × ℤ) F64 where
  name := name
  exact p := onFinite (fun _ => True) (fun a => a * (2 : ℝ) ^ p.2) p.1
  special := [{ name := s!"{name}(NaN, n) = NaN"
                applies := fun p => isNaN p.1
                expect := fun _ => .nan },
    { name := s!"{name}(±0, n) = ±0"
      applies := fun p => isZero p.1
      expect := fun p => .bits p.1 },
    { name := s!"{name}(±∞, n) = ±∞"
      applies := fun p => isInf p.1
      expect := fun p => .bits p.1 },
    overflow (fun p => onFinite (fun _ => True) (fun a => a * (2 : ℝ) ^ p.2) p.1)]

noncomputable def ldexp : Spec (F64 × ℤ) F64 := scale "ldexp"
noncomputable def scalbn : Spec (F64 × ℤ) F64 := scale "scalbn"

/-! ## `frexp` and `modf` -/

/-- `frexp` (§7.12.6.4, Annex F.10.3.4): `x = m · 2ᵉ` with `1/2 ≤ |m| < 1`;
`frexp(±0) = (±0, 0)`; infinities and NaNs are returned with an unspecified
exponent. -/
def FrexpOk (x : F64) (out : F64 × ℤ) : Prop :=
  match x.toRat? with
  | some a =>
    if a = 0 then out = (x, 0)
    else ∃ m, out.1.toRat? = some m ∧ a = m * 2 ^ out.2 ∧ 1 / 2 ≤ |m| ∧ |m| < 1
  | none => if x.isNaN then out.1.isNaN = true else out.1 = x

/-- `modf` (§7.12.6.12, Annex F.10.3.12): the fractional and integral parts,
both with the sign of `x`; `modf(±∞) = (±0, ±∞)`. -/
def ModfOk (x : F64) (out : F64 × F64) : Prop :=
  if x.isNaN then out.1.isNaN = true ∧ out.2.isNaN = true
  else if x.isInfinite then out = (F64.copySign F64.zero x, x)
  else ∃ a, x.toRat? = some a ∧
    out.2.toRat? = some (roundInt .towardZero a : ℚ) ∧
    out.1.toRat? = some (a - (roundInt .towardZero a : ℚ)) ∧
    out.1.signBit = x.signBit ∧ out.2.signBit = x.signBit

/-- The `frexp` catalogue entry; every level asks for the same exact result. -/
def frexpEntry : Entry where
  name := "frexp"
  In := F64
  Out := F64 × ℤ
  valid _ impl := ∀ x, FrexpOk x (impl x).value

/-- The `modf` catalogue entry. -/
def modfEntry : Entry where
  name := "modf"
  In := F64
  Out := F64 × F64
  valid _ impl := ∀ x, ModfOk x (impl x).value

/-! ## The batch -/

/-- Batch 1, in catalogue form. -/
noncomputable def batch1 : List Entry :=
  [fabs.entry, copysign.entry, floor.entry, ceil.entry, trunc.entry, round.entry, rint.entry,
    nearbyint.entry, fmod.entry, remainder.entry, fmin.entry, fmax.entry, ldexp.entry,
    scalbn.entry, sqrt.entry, frexpEntry, modfEntry]

end Silmaril.Numeric.Libm.Double
