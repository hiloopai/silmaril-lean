module

public import Silmaril.Numeric.Float.Classify
public import Silmaril.Numeric.Integer

/-!
# Architecture floating-point profiles

IEEE 754-2019 fixes the numerical value of a correctly rounded operation, but
leaves several choices to implementations, and architectures add modes outside
the standard. A `Profile` records those choices for one floating-point unit
configuration, so that one set of profile-parametric operations
(`Silmaril.Numeric.Float.Ops`) serves x86 SSE, RISC-V F/D, AArch64 and a later
software implementation.

The choices are:

* NaN results (IEEE 754-2019 §6.2.3 only asks that a propagated NaN carry the
  payload of an input NaN): `NaNPropagation`, `defaultNaNNegative`, and the
  per-instruction `FmaNaNRule`.
* Subnormal flushing, which is outside IEEE 754: `flushInputs` (x86 MXCSR.DAZ,
  AArch64 FPCR.FZ on inputs), `flushResults` (x86 MXCSR.FZ, AArch64 FPCR.FZ on
  results) and the flags raised when a result is flushed.
* Tininess detection (IEEE 754-2019 §7.5: before or after rounding).
* Minimum/maximum semantics, which differ per instruction: `MinMaxRule`.
* Out-of-range and NaN float-to-integer results (IEEE 754-2019 §5.8 and §7.2
  only require the invalid exception): `IntOverflowRule`.
* Signaling versus quiet comparison is selected per instruction by the operations
  in `Ops`; every architecture here provides both kinds.

The rounding direction is not part of a profile. Every operation in `Ops` takes
it as an explicit argument, and the instruction layer supplies it from the
architecture's state: the dynamic control register (x86 MXCSR.RC, RISC-V `frm`,
AArch64 FPCR.RMode) or a direction encoded in the instruction. `RoundingSelect`
names that choice and `RoundingSelect.resolve` turns it into a direction, so the
dynamic direction has one source of truth, the architectural register.

The concrete profiles and the manual section for each field live in
`Silmaril.Numeric.Float.Instances`. They are specifications transcribed from
architecture manuals, not measurements of hardware.

Exception flags come from the architecture-independent specification in
`Silmaril.Numeric.Ieee754.Flags` (`FlagSpec`), applied to the operands after
input flushing and with the profile's tininess detection. Beyond the choice of
tininess detection, a profile changes the IEEE flags in four ways only: input
flushing changes the operands the flags are computed from; result flushing
replaces the flags of a tiny result by `flushFlags` (`Profile.stage`);
`toIntSignalsInexact` selects, for every float-to-integer conversion, whether it
is IEEE `convertToIntegerExact…` (raising inexact) or `convertToInteger…`; and
individual instructions choose which IEEE operation they are (a quiet or
signaling comparison, the fused multiply-add quiet-NaN policy, x86 `MINSS`
behaving as a signaling comparison).
-/

@[expose] public section

namespace Silmaril.Numeric.Float

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Ieee754

/-- Which NaN an operation with NaN operands returns. -/
inductive NaNPropagation where
  /-- Always the profile's default NaN (RISC-V; AArch64 with FPCR.DN = 1). -/
  | defaultNaN
  /-- The first NaN operand in operand order, quieted (x86 SSE, Intel SDM Vol. 1
  Table 4-7: "first source operand" when both are NaNs). -/
  | firstNaN
  /-- The first signaling NaN operand if there is one, otherwise the first quiet
  NaN operand, quieted (AArch64 with FPCR.DN = 0, Arm `FPProcessNaNs`). -/
  | signalingFirst
  deriving DecidableEq, Repr

/-- The role of a fused multiply-add operand in `a * b + c`. -/
inductive FmaRole where
  | multiplicand1
  | multiplicand2
  | addend
  deriving DecidableEq, Repr

/-- NaN handling of fused multiply-add, which varies per architecture and, on x86,
per encoding form (132/213/231). -/
structure FmaNaNRule where
  /-- The order in which operands are examined by the profile's `NaNPropagation`. -/
  priority : List FmaRole
  /-- Whether `(±∞ × ±0) + qNaN` returns the default NaN instead of the addend. -/
  infZeroQuietNaNIsDefault : Bool
  /-- Whether `(±∞ × ±0) + qNaN` signals invalid; IEEE 754-2019 §7.2(c) makes this
  implementation-defined. -/
  infZeroQuietNaNInvalid : Bool
  deriving DecidableEq, Repr

/-- The exception specification's policy for `(±∞ × ±0) + qNaN` selected by a rule. -/
def FmaNaNRule.quietAddend (rule : FmaNaNRule) : FlagSpec.FmaQuietAddend :=
  if rule.infZeroQuietNaNInvalid then .signalInvalid else .noSignal

/-- Minimum and maximum semantics. `isMax` selects maximum throughout. -/
inductive MinMaxRule where
  /-- x86 `MINSS/MINSD/MAXSS/MAXSD` (Intel SDM Vol. 2 instruction pseudo-code):
  `if src1 < src2 then src1 else src2` for minimum. If either operand is a NaN,
  or both are zeros of any sign, the *second* operand is returned unchanged, even
  a signaling NaN. Invalid is signaled for any NaN operand. -/
  | x86
  /-- IEEE 754-2008 §5.3.1 `minNum`/`maxNum`: a single quiet NaN operand is
  ignored; a signaling NaN yields a NaN and invalid. The standard leaves the result
  for zeros of opposite sign open; this model orders `-0 < +0` as AArch64
  `FMINNM`/`FMAXNM` (Arm `FPMinNum`, `FPMaxNum`) do. -/
  | minNum
  /-- IEEE 754-2019 §9.6 `minimum`/`maximum`: NaN if either operand is a NaN,
  `-0 < +0` (AArch64 `FMIN`/`FMAX`, Arm `FPMin`/`FPMax`; WebAssembly `fmin`/`fmax`
  up to the choice of NaN). -/
  | minimum
  /-- IEEE 754-2019 §9.6 `minimumNumber`/`maximumNumber`: a NaN operand, quiet or
  signaling, is ignored if the other operand is a number; `-0 < +0`
  (RISC-V `FMIN`/`FMAX` since F 2.2). -/
  | minimumNumber
  deriving DecidableEq, Repr

/-- Float-to-integer results for NaN and out-of-range operands. Every rule signals
invalid for these operands; in-range conversions agree across rules. -/
inductive IntOverflowRule where
  /-- x86 "integer indefinite": the most negative signed value for signed targets
  (Intel SDM Vol. 2, `CVTSD2SI`/`CVTTSD2SI`/`CVTTSS2SI`: "the indefinite integer
  value (80000000H) is returned", or 8000000000000000H with REX.W), and `2^w - 1`
  for the AVX-512 unsigned conversions (`VCVTTSD2USI`). -/
  | indefinite
  /-- Saturate to the nearest bound; NaN yields the maximum (RISC-V `FCVT`,
  Unprivileged ISA "F" extension, conversion table). -/
  | saturateNaNToMax
  /-- Saturate to the nearest bound; NaN yields zero (AArch64 `FCVTZS`/`FCVTZU`,
  Arm `FPToFixed`; also WebAssembly `trunc_sat`). -/
  | saturateNaNToZero
  deriving DecidableEq, Repr

/-- Where an instruction takes its rounding direction from. -/
inductive RoundingSelect where
  /-- The dynamic control register (x86 MXCSR.RC, RISC-V `frm`, AArch64 FPCR.RMode). -/
  | dynamic
  /-- A direction fixed by the instruction encoding. -/
  | static (mode : RoundingMode)
  deriving DecidableEq, Repr

/-- The direction an instruction rounds in, given the current value of the dynamic
control register. -/
def RoundingSelect.resolve (dynamic : RoundingMode) : RoundingSelect → RoundingMode
  | .dynamic => dynamic
  | .static mode => mode

@[simp] theorem RoundingSelect.resolve_dynamic (dynamic : RoundingMode) :
    RoundingSelect.dynamic.resolve dynamic = dynamic := rfl

@[simp] theorem RoundingSelect.resolve_static (dynamic mode : RoundingMode) :
    (RoundingSelect.static mode).resolve dynamic = mode := rfl

/-- One floating-point unit configuration. -/
structure Profile where
  /-- NaN results of arithmetic with NaN operands. -/
  propagation : NaNPropagation
  /-- Sign of the default NaN; its trailing significand is always the quiet bit. -/
  defaultNaNNegative : Bool
  /-- Replace subnormal operands by zeros of the same sign before operating. -/
  flushInputs : Bool
  /-- Replace tiny nonzero results, exact or inexact, by zeros of the sign of the
  exact result. Tininess follows `tininess`. -/
  flushResults : Bool
  /-- Flags raised when a result is flushed; these replace all flags the
  operation would raise under IEEE default handling (which, for a tiny result,
  are at most underflow and inexact). -/
  flushFlags : Flags
  /-- Tininess detection (IEEE 754-2019 §7.5), used both for the underflow flag
  and for deciding which results are flushed. -/
  tininess : TininessDetection
  /-- Semantics of the architecture's base scalar minimum/maximum instruction. -/
  minMax : MinMaxRule
  /-- Float-to-integer results for NaN and out-of-range operands. -/
  intOverflow : IntOverflowRule
  /-- Whether float-to-integer conversions raise inexact when the integer differs
  from the operand, that is, whether they are IEEE 754-2019 §5.8
  `convertToIntegerExact…` operations rather than `convertToInteger…`. -/
  toIntSignalsInexact : Bool
  deriving DecidableEq, Repr

namespace Profile

/-- The default NaN of this profile in format `fmt`. -/
def defaultNaN (p : Profile) (fmt : Format) : Bits fmt := Bits.defaultNaN fmt p.defaultNaNNegative

/-- Input flushing, applied to every operand of a non-bitwise operation. -/
def flushInput (p : Profile) {fmt : Format} (b : Bits fmt) : Bits fmt :=
  if p.flushInputs then Bits.flushSubnormal b else b

@[simp] theorem flushInput_of_false (p : Profile) {fmt : Format} (b : Bits fmt)
    (h : p.flushInputs = false) : p.flushInput b = b := by
  simp [flushInput, h]

@[simp] theorem isNaN_flushInput (p : Profile) {fmt : Format} (b : Bits fmt) :
    (p.flushInput b).isNaN = b.isNaN := by
  unfold flushInput
  split <;> simp

@[simp] theorem isSignalingNaN_flushInput (p : Profile) {fmt : Format} (b : Bits fmt) :
    (p.flushInput b).isSignalingNaN = b.isSignalingNaN := by
  unfold flushInput
  split <;> simp

/-- The operand as the exception specification sees it after input flushing:
`FlagSpec.flushInput` (denormals-are-zero) of the classified operand when the
profile flushes inputs. -/
def inputDatum (p : Profile) {fmt : Format} (b : Bits fmt) : FlagSpec.Datum :=
  if p.flushInputs then FlagSpec.flushInput fmt b.datum else b.datum

theorem datum_flushInput (p : Profile) {fmt : Format} (b : Bits fmt) :
    (p.flushInput b).datum = p.inputDatum b := by
  unfold flushInput inputDatum
  split
  · exact Bits.datum_flushSubnormal b
  · rfl

@[simp] theorem inputDatum_of_false (p : Profile) {fmt : Format} (b : Bits fmt)
    (h : p.flushInputs = false) : p.inputDatum b = b.datum := by
  simp [inputDatum, h]

/-- The output-flushing control of the exception specification that this profile
applies when `flushResults` holds. Every profile here describes masked (x86) or
non-trapping (RISC-V, AArch64) exceptions, so the control is always used with the
underflow exception masked and `requiresUnderflowMasked` has no effect; it is set
so that the x86 control is exactly `FlushToZero.maskedUnderflowInexact`
(`x86SSE_flushControl`). -/
def flushControl (p : Profile) : FlagSpec.FlushToZero where
  requiresUnderflowMasked := true
  raises := p.flushFlags

/-- The stage that classifies exact finite results: the IEEE classification
(IEEE 754-2019 §§7.4–7.6), or output flushing when `flushResults` holds. -/
def stage (p : Profile) (fmt : Format) (mode : RoundingMode) : FlagSpec.RoundingStage :=
  if p.flushResults then .flushToZero p.flushControl true fmt mode p.tininess
  else .ieee fmt mode p.tininess

theorem stage_of_flushResults_false (p : Profile) (fmt : Format) (mode : RoundingMode)
    (h : p.flushResults = false) : p.stage fmt mode = .ieee fmt mode p.tininess := by
  simp [stage, h]

end Profile

/-- The value of an operation together with the IEEE flags it raises and whether a
subnormal operand was seen before input flushing. The last is a raw fact from
which an architecture derives its own non-IEEE status (x86 MXCSR.DE, AArch64
FPSR.IDC); the rules for those bits differ and are left to the instruction layer. -/
structure Outcome (α : Type) where
  value : α
  flags : Flags := Flags.empty
  subnormalOperand : Bool := false
  deriving DecidableEq, Repr

/-- A core IEEE operation on decoded, non-NaN operands, rounded once to the
destination format. `convert` covers format conversion of an exact source value. -/
inductive CoreOp where
  | add (x y : UnpackedFloat)
  | sub (x y : UnpackedFloat)
  | mul (x y : UnpackedFloat)
  | div (x y : UnpackedFloat)
  | sqrt (x : UnpackedFloat)
  | fma (x y z : UnpackedFloat)
  | convert (x : UnpackedFloat)

end Silmaril.Numeric.Float
