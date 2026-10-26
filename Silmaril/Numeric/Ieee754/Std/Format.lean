module

public import Silmaril.Numeric.Ieee754.Std.Round

/-!
# Binary formats, delivered results, overflow, underflow and flags

A `BinFormat` is an IEEE 754-2019 binary format given by its precision `p` and
maximum exponent `emax` (§3.3, Table 3.2; `emin = 1 - emax`). The finite values
are the magnitudes of `grid` (precision `p`, least quantum exponent
`emin - (p - 1)`, so gradual underflow is built in) up to `maxFinite`.

`RoundSpec f tin mode neg x res flags` specifies the delivered datum and the
raised flags for an exact nonzero-or-zero value of sign `neg` and magnitude
`x ≥ 0`, in any ordered field with a floor:

* the value is rounded as though the exponent range were unbounded above
  (`Grid.RoundMag`); a result above `maxFinite` overflows (§7.4) to the
  direction-dependent `overflowResult` (infinity, or the largest finite number);
* `inexact` is raised when the delivered value differs from the exact one,
  including on overflow (§7.6);
* `underflow` is raised when the result is tiny and inexact (§7.5, default
  handling). Tininess detection is a parameter: `beforeRounding` compares the
  exact magnitude with `2^emin`; `afterRounding` compares the value rounded with
  unbounded exponent range *and* precision `p`. x86 (SSE and x87) and RISC-V
  detect tininess after rounding (SoftFloat's `8086`, `8086-SSE` and `RISCV`
  specializations select `softfloat_tininess_afterRounding`; RISC-V
  Unprivileged ISA §"F" extension; Intel SDM Vol. 1 §4.9.1.5).
* the result carries the sign of the exact value; an exact zero carries the
  zero sign chosen by the operation (§6.3).

`roundQ` is the executable version on rationals and `roundQ_spec` proves that it
meets `RoundSpec`, which is functional (`RoundSpec.unique`).

`Exact` describes the exact outcome of an operation before delivery: a NaN
(signaling invalid or not), an exact infinity (signaling division by zero or
not), or a signed exact magnitude. `Deliver` and `deliverQ` extend the rounding
specification to it.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

/-- A binary floating-point format: precision `p ≥ 2` and `emax ≥ 1`. -/
structure BinFormat where
  prec : ℕ
  emax : ℕ
  two_le_prec : 2 ≤ prec := by decide
  one_le_emax : 1 ≤ emax := by decide
  deriving DecidableEq, Repr

namespace BinFormat

/-- IEEE 754-2019 Table 3.5 binary16. -/
def binary16 : BinFormat := { prec := 11, emax := 15 }
/-- IEEE 754-2019 Table 3.5 binary32. -/
def binary32 : BinFormat := { prec := 24, emax := 127 }
/-- IEEE 754-2019 Table 3.5 binary64. -/
def binary64 : BinFormat := { prec := 53, emax := 1023 }
/-- IEEE 754-2019 Table 3.5 binary128. -/
def binary128 : BinFormat := { prec := 113, emax := 16383 }
/-- bfloat16 (not an IEEE interchange format): binary32's exponent range with
8 significand bits. -/
def bfloat16 : BinFormat := { prec := 8, emax := 127 }
/-- The x87 double extended format (Intel SDM Vol. 1 §4.2.2): 64 significand
bits, 15 exponent bits. This is IEEE 754-2019's binary64 extended format. -/
def x87Extended : BinFormat := { prec := 64, emax := 16383 }
/-- x87 precision control: rounding to `p` bits with the extended exponent range
(Intel SDM Vol. 1 §8.1.5.2; FPU control word PC = 00b single, 10b double). -/
def x87PrecisionSingle : BinFormat := { prec := 24, emax := 16383 }
def x87PrecisionDouble : BinFormat := { prec := 53, emax := 16383 }

variable (f : BinFormat)

def emin : ℤ := 1 - (f.emax : ℤ)

/-- The least quantum exponent: the exponent of the least subnormal. -/
def qmin : ℤ := f.emin - ((f.prec : ℤ) - 1)

/-- Finite values below overflow, with gradual underflow. -/
def grid : Grid := ⟨f.prec, some f.qmin⟩

/-- Precision `p` with unbounded exponent range, for tininess after rounding. -/
def gridUnbounded : Grid := ⟨f.prec, none⟩

/-- The largest finite magnitude `(2^p - 1) * 2^(emax - p + 1)`. -/
def maxFinite : ℚ := (2 ^ f.prec - 1) * (2 : ℚ) ^ ((f.emax : ℤ) - ((f.prec : ℤ) - 1))

theorem one_le_prec : 1 ≤ f.prec := le_trans (by decide) f.two_le_prec

end BinFormat

/-- A floating-point datum at the value level. NaN payloads and signs are a
bit-level concern, governed by a NaN policy (`Std.NaN`). -/
inductive Datum where
  | nan (signaling : Bool)
  | inf (neg : Bool)
  | fin (neg : Bool) (mag : ℚ)
  deriving DecidableEq, Repr

namespace Datum

def isNaN : Datum → Bool
  | .nan _ => true
  | _ => false

def isSignaling : Datum → Bool
  | .nan s => s
  | _ => false

def neg : Datum → Datum
  | .nan s => .nan s
  | .inf n => .inf (!n)
  | .fin n m => .fin (!n) m

/-- Sign bit of a non-NaN datum. -/
def signBit : Datum → Bool
  | .nan _ => false
  | .inf n => n
  | .fin n _ => n

end Datum

/-- Signed value of a sign and a magnitude. -/
def signed (neg : Bool) (mag : ℚ) : ℚ := if neg then -mag else mag

/-- Result of an overflowing rounding of a value of sign `neg` (IEEE 754-2019 §7.4). -/
def overflowResult (f : BinFormat) (mode : RoundingMode) (neg : Bool) : Datum :=
  match mode with
  | .nearestTiesToEven | .nearestTiesToAway => .inf neg
  | .towardZero => .fin neg f.maxFinite
  | .towardPositive => if neg then .fin neg f.maxFinite else .inf neg
  | .towardNegative => if neg then .inf neg else .fin neg f.maxFinite

section Spec

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- Tininess of a nonzero exact magnitude `x` whose unbounded-exponent rounding is `ru`. -/
def Tiny (f : BinFormat) (tin : TininessDetection) (x : K) (ru : ℚ) : Prop :=
  match tin with
  | .beforeRounding => x < (2 : K) ^ f.emin
  | .afterRounding => (ru : K) < (2 : K) ^ f.emin

instance (f : BinFormat) (tin : TininessDetection) (x : K) (ru : ℚ) :
    Decidable (Tiny f tin x ru) := by
  unfold Tiny
  cases tin <;> infer_instance

/-- Delivered datum and flags for the exact value of sign `neg`, magnitude `x`. -/
def RoundSpec (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode) (neg : Bool)
    (x : K) (res : Datum) (fl : Flags) : Prop :=
  ∃ r ru : ℚ, f.grid.RoundMag mode neg x (r : K) ∧ f.gridUnbounded.RoundMag mode neg x (ru : K) ∧
    res = (if f.maxFinite < r then overflowResult f mode neg else .fin neg r) ∧
    fl = { overflow := decide (f.maxFinite < r)
           inexact := decide (f.maxFinite < r ∨ (r : K) ≠ x)
           underflow := decide (x ≠ 0 ∧ Tiny f tin x ru ∧ (r : K) ≠ x) }

/-- Exact outcome of an operation, before delivery to a format. -/
inductive Exact (K : Type*) where
  /-- A NaN result; `invalid` says whether invalid operation is signaled. -/
  | nan (invalid : Bool)
  /-- An exact infinity; `divByZero` says whether division by zero is signaled. -/
  | inf (neg : Bool) (divByZero : Bool)
  /-- An exact value of sign `neg` and magnitude `mag ≥ 0` (zero sign included). -/
  | num (neg : Bool) (mag : K)

/-- Delivery of an exact outcome (IEEE 754-2019 §7 default exception handling). -/
def Deliver (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode) :
    Exact K → Datum → Flags → Prop
  | .nan inv, res, fl => res = .nan false ∧ fl = { invalidOperation := inv }
  | .inf neg dz, res, fl => res = .inf neg ∧ fl = { divisionByZero := dz }
  | .num neg x, res, fl => RoundSpec f tin mode neg |x| res fl

theorem RoundSpec.unique {f : BinFormat} {tin : TininessDetection} {mode : RoundingMode}
    {neg : Bool} {x : K} {res res' : Datum} {fl fl' : Flags}
    (h : RoundSpec f tin mode neg x res fl) (h' : RoundSpec f tin mode neg x res' fl') :
    res = res' ∧ fl = fl' := by
  obtain ⟨r, ru, hr, hru, rfl, rfl⟩ := h
  obtain ⟨r', ru', hr', hru', rfl, rfl⟩ := h'
  have e1 : r = r' := by exact_mod_cast hr.unique hr'
  have e2 : ru = ru' := by exact_mod_cast hru.unique hru'
  subst e1 e2
  exact ⟨rfl, rfl⟩

theorem Deliver.unique {f : BinFormat} {tin : TininessDetection} {mode : RoundingMode}
    {e : Exact K} {res res' : Datum} {fl fl' : Flags}
    (h : Deliver f tin mode e res fl) (h' : Deliver f tin mode e res' fl') :
    res = res' ∧ fl = fl' := by
  cases e with
  | nan inv => exact ⟨h.1.trans h'.1.symm, h.2.trans h'.2.symm⟩
  | inf neg dz => exact ⟨h.1.trans h'.1.symm, h.2.trans h'.2.symm⟩
  | num neg x => exact RoundSpec.unique h h'

end Spec

/-! ## Executable delivery on rationals -/

/-- Executable rounding and flags. -/
def roundQ (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode) (neg : Bool)
    (x : ℚ) : Datum × Flags :=
  let r := f.grid.roundMagQ mode neg x
  let ru := f.gridUnbounded.roundMagQ mode neg x
  ((if f.maxFinite < r then overflowResult f mode neg else .fin neg r),
    { overflow := decide (f.maxFinite < r)
      inexact := decide (f.maxFinite < r ∨ r ≠ x)
      underflow := decide (x ≠ 0 ∧ Tiny f tin x ru ∧ r ≠ x) })

theorem roundQ_spec (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode) (neg : Bool)
    {x : ℚ} (hx : 0 ≤ x) : RoundSpec f tin mode neg x (roundQ f tin mode neg x).1
      (roundQ f tin mode neg x).2 :=
  ⟨f.grid.roundMagQ mode neg x, f.gridUnbounded.roundMagQ mode neg x,
    f.grid.roundMagQ_spec f.one_le_prec mode neg hx,
    f.gridUnbounded.roundMagQ_spec f.one_le_prec mode neg hx, rfl, rfl⟩

/-- Executable delivery. -/
def deliverQ (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode) :
    Exact ℚ → Datum × Flags
  | .nan inv => (.nan false, { invalidOperation := inv })
  | .inf neg dz => (.inf neg, { divisionByZero := dz })
  | .num neg x => roundQ f tin mode neg |x|

/-- The executable delivery meets the specification. -/
theorem deliverQ_spec (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode)
    (e : Exact ℚ) : Deliver f tin mode e (deliverQ f tin mode e).1 (deliverQ f tin mode e).2 := by
  cases e with
  | nan inv => exact ⟨rfl, rfl⟩
  | inf neg dz => exact ⟨rfl, rfl⟩
  | num neg x => exact roundQ_spec f tin mode neg (abs_nonneg x)

/-- Delivery is determined: the executable result is the only specified one. -/
theorem deliver_iff (f : BinFormat) (tin : TininessDetection) (mode : RoundingMode)
    (e : Exact ℚ) (res : Datum) (fl : Flags) :
    Deliver f tin mode e res fl ↔ deliverQ f tin mode e = (res, fl) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (deliverQ_spec f tin mode e).unique h
    rw [← h1, ← h2]
  · intro h
    have := deliverQ_spec f tin mode e
    rw [h] at this
    exact this

end Silmaril.Numeric.Ieee754.Std
