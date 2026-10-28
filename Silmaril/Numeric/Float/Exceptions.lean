module

public import Silmaril.Numeric.Float.Flags

/-!
# Exception conditions outside IEEE default handling

The profile operations report the IEEE default flags (`Silmaril.Numeric.Float.Ops`)
and a raw subnormal-operand indication (`Outcome.subnormalOperand`). Two further
conditions recur across architectures and are stated here once, so that an
instruction layer instantiates them instead of re-deriving them:

* **Underflow with the trap enabled.** IEEE 754-2019 §7.5 signals the underflow
  exception whenever a tiny nonzero result is detected; default handling raises
  the underflow flag only when that result is also inexact, while alternate
  handling (for example a trap) sees every tiny result. `Profile.tinyOutcome` decides tininess of an exact result
  with the profile's tininess detection, and `Profile.underflowCondition` is the
  underflow condition with or without the trap. Two readings of the manuals fit
  it: x86 with MXCSR.UM = 0 (SDM Vol. 1 §4.9.1.5), used by `Silmaril.X86.Float`,
  and AArch64 with FPCR.UFE = 1 (Arm `FPRoundBase` signals underflow for a tiny
  result when it is inexact or the trap is enabled); no AArch64 layer uses it
  yet.
* **Subnormal operands.** Neither IEEE flag covers them. Two architecture rules
  are provided as readings of the manuals, not as hardware facts:
  `Outcome.denormalAfterPriority` is the x86 denormal-operand condition DE before
  its DAZ and per-instruction gating (a subnormal operand, reported only when no
  operand is a NaN and neither invalid nor divide-by-zero is detected, SDM Vol. 1
  §4.9.2 priority), and `Outcome.inputDenormalFlushed` is the AArch64 input
  denormal condition IDC (a subnormal operand replaced by zero because input
  flushing is on, Arm `FPUnpackBase` with FPCR.FZ = 1, raised while unpacking and
  so independently of the other operands).

The two subnormal rules differ, which is why the profile operations report only
the raw fact.
-/

@[expose] public section

namespace Silmaril.Numeric.Float

open Float.Model
open Silmaril.Numeric.Ieee754

namespace Profile

variable (p : Profile)

/-- Whether an exact result is tiny under the profile's tininess detection
(IEEE 754-2019 §7.5). -/
def tinyOutcome (fmt : Format) (mode : RoundingMode) (o : FlagSpec.Outcome) : Bool :=
  decide (o.IsTiny fmt p.tininess mode)

theorem tinyOutcome_iff (fmt : Format) (mode : RoundingMode) (o : FlagSpec.Outcome) :
    p.tinyOutcome fmt mode o = true ↔ o.IsTiny fmt p.tininess mode :=
  decide_eq_true_iff

/-- The underflow condition of an operation that raised `flags` from the exact
result `o`. Without the trap it is the underflow flag; with the trap enabled it
also holds for a tiny exact result (IEEE 754-2019 §7.5). -/
def underflowCondition (trapped : Bool) (fmt : Format) (mode : RoundingMode)
    (o : FlagSpec.Outcome) (flags : Flags) : Bool :=
  flags.underflow || (trapped && p.tinyOutcome fmt mode o)

@[simp] theorem underflowCondition_untrapped (fmt : Format) (mode : RoundingMode)
    (o : FlagSpec.Outcome) (flags : Flags) :
    p.underflowCondition false fmt mode o flags = flags.underflow := by
  simp [underflowCondition]

/-- The IEEE default underflow flag of an outcome implies tininess. -/
theorem isTiny_of_ieee_underflow (fmt : Format) (mode : RoundingMode) (o : FlagSpec.Outcome)
    (h : (o.flags (.ieee fmt mode p.tininess)).underflow = true) :
    o.IsTiny fmt p.tininess mode := by
  cases o with
  | finite v =>
    simp only [FlagSpec.Outcome.flags, FlagSpec.RoundingStage.ieee] at h
    exact ((FlagSpec.roundingFlags_underflow fmt mode p.tininess v).mp h).1
  | sqrt a =>
    simp only [FlagSpec.Outcome.flags, FlagSpec.RoundingStage.ieee, FlagSpec.sqrtRoundingFlags,
      decide_eq_true_eq] at h
    exact h.1
  | _ => simp [FlagSpec.Outcome.flags, FlagSpec.invalid, FlagSpec.divideByZero, Flags.singleton,
      Flags.empty, Flags.ofFunction] at h

/-- With the trap enabled and the IEEE flags of the same outcome, the underflow
condition is tininess alone: every tiny result signals underflow, exact or not. -/
theorem underflowCondition_trapped_ieee (fmt : Format) (mode : RoundingMode)
    (o : FlagSpec.Outcome) :
    p.underflowCondition true fmt mode o (o.flags (.ieee fmt mode p.tininess)) =
      p.tinyOutcome fmt mode o := by
  unfold underflowCondition
  cases h : (o.flags (.ieee fmt mode p.tininess)).underflow
  · simp
  · simp [(p.tinyOutcome_iff fmt mode o).mpr (p.isTiny_of_ieee_underflow fmt mode o h)]

end Profile

namespace Outcome

variable {α : Type}

/-- A subnormal operand was seen, no operand is a NaN (`nanOperand` false), and
neither invalid nor divide-by-zero is raised: the x86 denormal-operand condition
before DAZ and per-instruction gating (SDM Vol. 1 §4.9.2: a NaN operand, invalid
and divide-by-zero take precedence over the denormal-operand exception). -/
def denormalAfterPriority (nanOperand : Bool) (o : Outcome α) : Bool :=
  o.subnormalOperand && !nanOperand && !o.flags.invalidOperation && !o.flags.divisionByZero

/-- A subnormal operand was replaced by a zero because the profile flushes
inputs: the AArch64 input-denormal condition FPSR.IDC as read from Arm
`FPUnpackBase` with FPCR.FZ = 1 and FPCR.AH = 0. -/
def inputDenormalFlushed (p : Profile) (o : Outcome α) : Bool :=
  p.flushInputs && o.subnormalOperand

theorem denormalAfterPriority_imp (nanOperand : Bool) (o : Outcome α)
    (h : o.denormalAfterPriority nanOperand = true) :
    o.subnormalOperand = true ∧ nanOperand = false ∧ o.flags.invalidOperation = false ∧
      o.flags.divisionByZero = false := by
  simp only [denormalAfterPriority, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end Outcome

end Silmaril.Numeric.Float
