module

public import Silmaril.Numeric.Ieee754.Std.NaN

/-!
# ISA floating-point profiles over the `Std` core

An `Isa` fixes the implementation-defined parameters of IEEE 754-2019 for one
architecture: tininess detection (§7.5), the NaN function (§6.2.3), the NaN
result of format conversions, the integer results of invalid float-to-integer
conversions (§5.8), and whether `fma(∞, 0, qNaN)` signals invalid (§7.2(c)).
Every operation is then the executable `runOp` on the exact outcome of
`Std.Ops`, so each one meets its specification (`Isa.*_spec`) and, by
`OpSpec.mono`, the chaotic specification `OpSpec E (anyNaN E)` (`Isa.*_chaos`).

Profiles:
* `x86SSE`: SSE/AVX scalar arithmetic (Intel SDM Vol. 1 §4.8.3, §11.5; tininess
  after rounding; integer indefinite);
* `riscv`: RISC-V F/D/Q/Zfh (canonical NaN, saturating conversions);
* `x87`: x87 FPU NaN choice (larger significand) with the x87 encoding.

They match SoftFloat 3e's `8086-SSE`, `RISCV` and `8086` specializations, which
is what the TestFloat vectors check.

Scope of each profile as a model of hardware:
* `x86SSE` is SSE/AVX with `MXCSR.DAZ = MXCSR.FTZ = 0`; `Std.Chaos` gives
  `Mxcsr.Spec`, which takes the flush bits as a parameter, and the chaotic
  `Mxcsr.Unknown`, which contains every setting. The x86 denormal-operand flag
  `MXCSR.DE` is not among the five IEEE `Flags`.
* `x87` is the x87 FPU only on the x87 double extended encoding (and on the
  precision-control formats `BinFormat.x87PrecisionSingle/Double`). On binary32
  and binary64 it is SoftFloat's `8086` functions, not an x87 instruction
  sequence: `FLD m32; FADD; FSTP m32` rounds in extended range under precision
  control and then again on the store.
* `rem` is an IEEE operation without an SSE/AVX or RISC-V instruction (a libm-level
  function there); on x87 it is `FPREM1`.
* `fma` with `fmaInfZeroDefault` (SoftFloat `8086-SSE`, x87) offers the NaN
  function `fmaNaNOperands`, not `[x, y, z]`, so the inclusion
  `NaNSpec.ofFun I.nan ≤ NaNSpec.propagating` gives a propagation guarantee
  relative to that list; `Isa.fma_softfloat8086SSE_not_propagating` (in
  `Std.Chaos`) shows the operand-level reading fails. `fma_chaos` and `FmaChaos`
  do not depend on the operands.

Minimum and maximum are given at the bit level, because x86 returns an operand's
encoding unchanged; the variants are x86 `MINSS/MAXSS`, IEEE 754-2008
`minNum/maxNum`, IEEE 754-2019 `minimum/maximum` and `minimumNumber/maximumNumber`.
`MinMaxChaos` (the result is an operand or a quiet NaN) contains all of them.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

/-- NaN result of converting the NaN `x` of `E₁` to `E₂`, keeping the
top-aligned payload and the sign, and quieting (x86 `CVTSS2SD` etc.;
SoftFloat's common NaN form). -/
def convertPayload (E₁ E₂ : Encoding) (x : Fields) : Fields :=
  let p := x.frac % 2 ^ E₁.payloadBits
  let p' := if E₁.payloadBits ≤ E₂.payloadBits then p <<< (E₂.payloadBits - E₁.payloadBits)
    else p >>> (E₁.payloadBits - E₂.payloadBits)
  E₂.quiet ⟨x.sign, 2 ^ E₂.expBits - 1, p'⟩

/-- An architecture's IEEE 754 implementation choices. -/
structure Isa where
  tin : TininessDetection
  nan : Encoding → List Fields → Fields
  nanConvert : Encoding → Encoding → Fields → Fields
  intPolicy : IntOverflowPolicy
  fmaInfZeroQNaN : FmaInfZeroQNaN
  /-- Whether `fma(∞, 0, NaN)` delivers the NaN function's default (as if the
  invalid product were a default NaN that wins propagation; SoftFloat) rather
  than propagating from the operands. -/
  fmaInfZeroDefault : Bool := false

namespace Isa

/-- x86 SSE/AVX/FMA as implemented in hardware (Intel SDM), with `MXCSR.DAZ =
MXCSR.FTZ = 0`: `fma(∞, 0, qNaN)` returns the quiet NaN addend without signaling.
Checked on an i7-8700 against every TestFloat level-1 binary32/binary64 `mulAdd`
vector with a NaN operand, in the four x86 rounding directions, with
`VFMADD132`, `VFMADD213` and `VFMADD231` agreeing on each
(`scripts/ieee754/fma-nan-check.sh x86hw`). -/
def x86SSE : Isa where
  tin := .afterRounding
  nan E := NaNFun.x86SSE E (E.defaultNaN true)
  nanConvert := convertPayload
  intPolicy := IntOverflowPolicy.x86Indefinite
  fmaInfZeroQNaN := false

/-- SoftFloat 3e's `8086-SSE` specialization: as `x86SSE`, except that
`fma(∞, 0, qNaN)` signals invalid and returns the default NaN. -/
def softfloat8086SSE : Isa :=
  { x86SSE with fmaInfZeroQNaN := true, fmaInfZeroDefault := true }

def riscv : Isa where
  tin := .afterRounding
  nan E := NaNFun.riscv (E.defaultNaN false)
  nanConvert _ E₂ _ := E₂.defaultNaN false
  intPolicy := IntOverflowPolicy.riscvSaturate
  fmaInfZeroQNaN := true

def x87 : Isa where
  tin := .afterRounding
  nan E := NaNFun.x87 E (E.defaultNaN true)
  nanConvert := convertPayload
  intPolicy := IntOverflowPolicy.x86Indefinite
  fmaInfZeroQNaN := true
  fmaInfZeroDefault := true

/-- The profile's NaN function always yields a NaN. -/
def NaNSound (I : Isa) : Prop := ∀ (E : Encoding) (ins : List Fields), E.isNaN (I.nan E ins) = true

variable (I : Isa) (E : Encoding)

def add (mode : RoundingMode) (x y : Fields) : Fields × Flags :=
  runOp E (I.nan E) I.tin mode [x, y] (exactAdd mode (E.decode x) (E.decode y))

def sub (mode : RoundingMode) (x y : Fields) : Fields × Flags :=
  runOp E (I.nan E) I.tin mode [x, y] (exactSub mode (E.decode x) (E.decode y))

def mul (mode : RoundingMode) (x y : Fields) : Fields × Flags :=
  runOp E (I.nan E) I.tin mode [x, y] (exactMul (E.decode x) (E.decode y))

def div (mode : RoundingMode) (x y : Fields) : Fields × Flags :=
  runOp E (I.nan E) I.tin mode [x, y] (exactDiv (E.decode x) (E.decode y))

/-- Whether `x * y` is `∞ × 0` (in either order). -/
def infTimesZero (x y : Datum) : Bool :=
  match x, y with
  | .inf _, .fin _ n => decide (n = 0)
  | .fin _ m, .inf _ => decide (m = 0)
  | _, _ => false

/-- The operands offered to the NaN function by `fma`. With
`fmaInfZeroDefault`, an invalid `∞ × 0` product is the default NaN (`I.nan E []`)
and is propagated against the addend, as SoftFloat does
(`propagateNaN(defaultNaN, c)`). NaN-policy statements about `fma` (`fma_spec`)
are relative to this list: the result need not be an operand of `[x, y, z]`
quieted. -/
def fmaNaNOperands (x y z : Fields) : List Fields :=
  if I.fmaInfZeroDefault && infTimesZero (E.decode x) (E.decode y) then [I.nan E [], z]
  else [x, y, z]

/-- `x * y + z`; operands are listed for the NaN function in the order given. -/
def fma (mode : RoundingMode) (x y z : Fields) : Fields × Flags :=
  runOp E (I.nan E) I.tin mode (I.fmaNaNOperands E x y z)
    (exactFma I.fmaInfZeroQNaN mode (E.decode x) (E.decode y) (E.decode z))

def rem (x y : Fields) : Fields × Flags :=
  runOp E (I.nan E) I.tin .nearestTiesToEven [x, y] (exactRem (E.decode x) (E.decode y))

def sqrt (mode : RoundingMode) (x : Fields) : Fields × Flags :=
  runSqrt E (I.nan E) I.tin mode x

/-- roundToIntegral in direction `dir`; `exact` selects roundToIntegralExact. -/
def roundToIntegral (dir : RoundingMode) (exact : Bool) (x : Fields) : Fields × Flags :=
  let p := exactRoundToIntegral dir (E.decode x)
  let o := runOp E (I.nan E) I.tin dir [x] p.1
  (o.1, { o.2 with inexact := o.2.inexact || (exact && p.2) })

/-- Conversion from `E₁` to `E₂`. -/
def convert (E₁ E₂ : Encoding) (mode : RoundingMode) (x : Fields) : Fields × Flags :=
  runOp E₂ (fun _ => I.nanConvert E₁ E₂ x) I.tin mode [x] (exactConvert (E₁.decode x))

def ofInt (mode : RoundingMode) (n : ℤ) : Fields × Flags :=
  runOp E (I.nan E) I.tin mode [] (exactOfInt n)

def toInt (t : IntFormat) (dir : RoundingMode) (exact : Bool) (x : Fields) : ℤ × Flags :=
  Std.toInt I.intPolicy t dir exact (E.decode x)

def compare (signaling : Bool) (x y : Fields) : Option Ordering × Flags :=
  compareOp signaling (E.decode x) (E.decode y)

/-! ### Specifications -/

theorem add_spec (mode : RoundingMode) (x y : Fields) :
    OpSpec E (NaNSpec.ofFun (I.nan E)) I.tin mode [x, y] (exactAdd mode (E.decode x) (E.decode y))
      (I.add E mode x y).1 (I.add E mode x y).2 := runOp_spec ..

theorem sub_spec (mode : RoundingMode) (x y : Fields) :
    OpSpec E (NaNSpec.ofFun (I.nan E)) I.tin mode [x, y] (exactSub mode (E.decode x) (E.decode y))
      (I.sub E mode x y).1 (I.sub E mode x y).2 := runOp_spec ..

theorem mul_spec (mode : RoundingMode) (x y : Fields) :
    OpSpec E (NaNSpec.ofFun (I.nan E)) I.tin mode [x, y] (exactMul (E.decode x) (E.decode y))
      (I.mul E mode x y).1 (I.mul E mode x y).2 := runOp_spec ..

theorem div_spec (mode : RoundingMode) (x y : Fields) :
    OpSpec E (NaNSpec.ofFun (I.nan E)) I.tin mode [x, y] (exactDiv (E.decode x) (E.decode y))
      (I.div E mode x y).1 (I.div E mode x y).2 := runOp_spec ..

theorem fma_spec (mode : RoundingMode) (x y z : Fields) :
    OpSpec E (NaNSpec.ofFun (I.nan E)) I.tin mode (I.fmaNaNOperands E x y z)
      (exactFma I.fmaInfZeroQNaN mode (E.decode x) (E.decode y) (E.decode z))
      (I.fma E mode x y z).1 (I.fma E mode x y z).2 := runOp_spec ..

theorem rem_spec (x y : Fields) :
    OpSpec E (NaNSpec.ofFun (I.nan E)) I.tin .nearestTiesToEven [x, y]
      (exactRem (E.decode x) (E.decode y)) (I.rem E x y).1 (I.rem E x y).2 := runOp_spec ..

theorem sqrt_spec (mode : RoundingMode) (x : Fields) :
    OpSpec E (NaNSpec.ofFun (I.nan E)) I.tin mode [x] (exactSqrt (E.decode x))
      (I.sqrt E mode x).1 (I.sqrt E mode x).2 := runSqrt_spec ..

theorem ofInt_spec (mode : RoundingMode) (n : ℤ) :
    OpSpec E (NaNSpec.ofFun (I.nan E)) I.tin mode [] (exactOfInt n)
      (I.ofInt E mode n).1 (I.ofInt E mode n).2 := runOp_spec ..

theorem convert_spec (E₁ E₂ : Encoding) (mode : RoundingMode) (x : Fields) :
    OpSpec E₂ (NaNSpec.ofFun (fun _ => I.nanConvert E₁ E₂ x)) I.tin mode [x]
      (exactConvert (E₁.decode x)) (I.convert E₁ E₂ mode x).1 (I.convert E₁ E₂ mode x).2 :=
  runOp_spec ..

/-! ### The chaotic variant contains each profile -/


theorem nanSpec_le_anyNaN (h : I.NaNSound) : NaNSpec.ofFun (I.nan E) ≤ NaNSpec.anyNaN E := by
  intro ins out hout
  simp only [NaNSpec.ofFun] at hout
  subst hout
  exact h E ins

theorem x86SSE_nanSound : x86SSE.NaNSound := fun E ins =>
  (NaNSpec.x86SSE_le_propagating E _ (E.defaultNaN_quiet true) ins _ rfl).1.1

theorem softfloat8086SSE_nanSound : softfloat8086SSE.NaNSound := x86SSE_nanSound

theorem riscv_nanSound : riscv.NaNSound := fun E ins =>
  (NaNSpec.riscv_le_quietNaN E _ (E.defaultNaN_quiet false) ins _ rfl).1

theorem x87_nanSound : x87.NaNSound := fun E ins =>
  (NaNSpec.x87_le_propagating E _ (E.defaultNaN_quiet true) ins _ rfl).1.1

theorem x86SSE_nan_le_propagating (E : Encoding) :
    NaNSpec.ofFun (x86SSE.nan E) ≤ NaNSpec.propagating E :=
  NaNSpec.x86SSE_le_propagating E _ (E.defaultNaN_quiet true)

theorem x87_nan_le_propagating (E : Encoding) :
    NaNSpec.ofFun (x87.nan E) ≤ NaNSpec.propagating E :=
  NaNSpec.x87_le_propagating E _ (E.defaultNaN_quiet true)

theorem riscv_nan_le_quietNaN (E : Encoding) :
    NaNSpec.ofFun (riscv.nan E) ≤ NaNSpec.quietNaN E :=
  NaNSpec.riscv_le_quietNaN E _ (E.defaultNaN_quiet false)

theorem add_chaos (h : I.NaNSound) (mode : RoundingMode) (x y : Fields) :
    OpSpec E (NaNSpec.anyNaN E) I.tin mode [x, y] (exactAdd mode (E.decode x) (E.decode y))
      (I.add E mode x y).1 (I.add E mode x y).2 :=
  (I.add_spec E mode x y).mono (I.nanSpec_le_anyNaN E h)

theorem mul_chaos (h : I.NaNSound) (mode : RoundingMode) (x y : Fields) :
    OpSpec E (NaNSpec.anyNaN E) I.tin mode [x, y] (exactMul (E.decode x) (E.decode y))
      (I.mul E mode x y).1 (I.mul E mode x y).2 :=
  (I.mul_spec E mode x y).mono (I.nanSpec_le_anyNaN E h)

theorem div_chaos (h : I.NaNSound) (mode : RoundingMode) (x y : Fields) :
    OpSpec E (NaNSpec.anyNaN E) I.tin mode [x, y] (exactDiv (E.decode x) (E.decode y))
      (I.div E mode x y).1 (I.div E mode x y).2 :=
  (I.div_spec E mode x y).mono (I.nanSpec_le_anyNaN E h)

theorem sqrt_chaos (h : I.NaNSound) (mode : RoundingMode) (x : Fields) :
    OpSpec E (NaNSpec.anyNaN E) I.tin mode [x] (exactSqrt (E.decode x))
      (I.sqrt E mode x).1 (I.sqrt E mode x).2 :=
  (I.sqrt_spec E mode x).mono (I.nanSpec_le_anyNaN E h)

theorem fma_chaos (h : I.NaNSound) (mode : RoundingMode) (x y z : Fields) :
    OpSpec E (NaNSpec.anyNaN E) I.tin mode (I.fmaNaNOperands E x y z)
      (exactFma I.fmaInfZeroQNaN mode (E.decode x) (E.decode y) (E.decode z))
      (I.fma E mode x y z).1 (I.fma E mode x y z).2 :=
  (I.fma_spec E mode x y z).mono (I.nanSpec_le_anyNaN E h)

/-- The chaotic fused multiply-add: the `fma(∞, 0, qNaN)` invalid choice is
left open and any NaN may result (`anyNaN` ignores the operand list). Both x86
variants (hardware and SoftFloat) and RISC-V satisfy it. -/
def FmaChaos (E : Encoding) (tin : TininessDetection) (mode : RoundingMode) (x y z : Fields)
    (out : Fields) (fl : Flags) : Prop :=
  ∃ b : FmaInfZeroQNaN, OpSpec E (NaNSpec.anyNaN E) tin mode []
    (exactFma b mode (E.decode x) (E.decode y) (E.decode z)) out fl

theorem fma_fmaChaos (h : I.NaNSound) (mode : RoundingMode) (x y z : Fields) :
    FmaChaos E I.tin mode x y z (I.fma E mode x y z).1 (I.fma E mode x y z).2 := by
  obtain ⟨res, hd, hn, he⟩ := I.fma_chaos E h mode x y z
  exact ⟨_, res, hd, hn, he⟩

/-- One statement for every ISA: x86 SSE, x87 and RISC-V results all satisfy the
chaotic specification of addition. -/
theorem add_chaos_all (mode : RoundingMode) (x y : Fields) :
    OpSpec E (NaNSpec.anyNaN E) .afterRounding mode [x, y]
        (exactAdd mode (E.decode x) (E.decode y)) (x86SSE.add E mode x y).1
        (x86SSE.add E mode x y).2 ∧
      OpSpec E (NaNSpec.anyNaN E) .afterRounding mode [x, y]
        (exactAdd mode (E.decode x) (E.decode y)) (x87.add E mode x y).1
        (x87.add E mode x y).2 ∧
      OpSpec E (NaNSpec.anyNaN E) .afterRounding mode [x, y]
        (exactAdd mode (E.decode x) (E.decode y)) (riscv.add E mode x y).1
        (riscv.add E mode x y).2 :=
  ⟨x86SSE.add_chaos E x86SSE_nanSound mode x y, x87.add_chaos E x87_nanSound mode x y,
    riscv.add_chaos E riscv_nanSound mode x y⟩

end Isa

/-! ## Minimum and maximum -/

/-- Minimum/maximum semantics. -/
inductive MinMaxRule where
  /-- x86 `MINSS/MINSD/MAXSS/MAXSD` (Intel SDM Vol. 2): `x < y ? x : y` (min),
  `x > y ? x : y` (max); the second operand is returned unchanged if either is a
  NaN or both are zeros; invalid for any NaN operand. -/
  | x86
  /-- IEEE 754-2008 §5.3.1 `minNum/maxNum`: a quiet NaN operand is ignored;
  a signaling NaN gives a NaN and invalid; `-0 < +0` (a choice: 2008 leaves it open). -/
  | minNum2008
  /-- IEEE 754-2019 §9.6 `minimum/maximum`: NaN if either is a NaN; `-0 < +0`. -/
  | minimum2019
  /-- IEEE 754-2019 §9.6 `minimumNumber/maximumNumber`: a NaN is ignored if the other
  operand is a number (signaling NaNs still signal invalid); `-0 < +0` (RISC-V
  `FMIN/FMAX` from F 2.2). -/
  | minimumNumber2019
  deriving DecidableEq, Repr

/-- The numeric minimum (`isMax = false`) or maximum, with `-0 < +0`. -/
def numericMinMax (E : Encoding) (isMax : Bool) (x y : Fields) : Fields :=
  match (E.decode x).compareValue (E.decode y) with
  | some .lt => if isMax then y else x
  | some .gt => if isMax then x else y
  | _ => if x.sign = y.sign then x else if (x.sign = isMax) then y else x

def minMax (E : Encoding) (nan : List Fields → Fields) (rule : MinMaxRule) (isMax : Bool)
    (x y : Fields) : Fields × Flags :=
  let dx := E.decode x
  let dy := E.decode y
  let snan := dx.isSignaling || dy.isSignaling
  match rule with
  | .x86 =>
    let first := match dx.compareValue dy with
      | some .lt => !isMax
      | some .gt => isMax
      | _ => false
    (if first then x else y, { invalidOperation := dx.isNaN || dy.isNaN })
  | .minNum2008 =>
    if snan then (nan [x, y], { invalidOperation := true })
    else if dx.isNaN then (if dy.isNaN then nan [x, y] else y, {})
    else if dy.isNaN then (x, {})
    else (numericMinMax E isMax x y, {})
  | .minimum2019 =>
    if dx.isNaN || dy.isNaN then (nan [x, y], { invalidOperation := snan })
    else (numericMinMax E isMax x y, {})
  | .minimumNumber2019 =>
    if dx.isNaN && dy.isNaN then (nan [x, y], { invalidOperation := snan })
    else if dx.isNaN then (y, { invalidOperation := snan })
    else if dy.isNaN then (x, { invalidOperation := snan })
    else (numericMinMax E isMax x y, {})

/-- The chaotic minimum/maximum: an operand's encoding, or a quiet NaN. -/
def MinMaxChaos (E : Encoding) (x y out : Fields) : Prop :=
  out = x ∨ out = y ∨ NaNSpec.quietNaN E [x, y] out

theorem numericMinMax_cases (E : Encoding) (isMax : Bool) (x y : Fields) :
    numericMinMax E isMax x y = x ∨ numericMinMax E isMax x y = y := by
  unfold numericMinMax
  split <;> split_ifs <;> simp

theorem minMax_chaos (E : Encoding) (nan : List Fields → Fields)
    (hnan : NaNSpec.ofFun nan ≤ NaNSpec.quietNaN E) (rule : MinMaxRule) (isMax : Bool)
    (x y : Fields) : MinMaxChaos E x y (minMax E nan rule isMax x y).1 := by
  have hq : NaNSpec.quietNaN E [x, y] (nan [x, y]) := hnan _ _ rfl
  have hn := numericMinMax_cases E isMax x y
  unfold MinMaxChaos minMax
  cases rule <;> dsimp only <;> (try split_ifs) <;> simp_all <;> tauto

end Silmaril.Numeric.Ieee754.Std
