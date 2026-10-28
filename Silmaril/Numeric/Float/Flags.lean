module

public import Silmaril.Numeric.Float.Instances

/-!
# Exception flags of the profile operations

Every profile operation computes its flags with the architecture-independent
specification `Silmaril.Numeric.Ieee754.Flags` (`FlagSpec`). This module states
the result for each operation in two forms:

* `…_flags`, for every profile: the IEEE flags of the operands after input
  flushing (`Profile.inputDatum`, which is `FlagSpec.flushInput` of the classified
  operand when the profile flushes inputs), except that when the profile flushes
  results and the exact result is tiny under the profile's tininess detection,
  the flags are `Profile.flushFlags` instead (`flags_stage`);
* `…_flags_ieee`, when the profile flushes neither inputs nor results: exactly
  the IEEE default flags of the unmodified operands (`FlagSpec.add`,
  `FlagSpec.sqrt`, `FlagSpec.fma`, …), with the profile's tininess detection.

Result values and flags use the same flush decision: `flushSign?` is `some`
exactly when `flags_stage` replaces the flags (`flushSign?_isSome_iff`).

Some operations do not depend on flushing at all: comparisons and minimum/maximum
(`compare_flags`, `minMaxWith_flags`, since input flushing never changes a NaN)
and integer-to-float conversion (`ofInt_flags`, since integers are never tiny).

## x86 SSE

For `Profile.x86SSE` (Intel SDM Vol. 1 §4.9, §10.2.3; Vol. 2 instruction pages):

* tininess is detected after rounding, and FZ with masked underflow is the
  specification's `FlushToZero.maskedUnderflowInexact` (`x86SSE_stage`); with DAZ
  clear, for a finite exact result, FZ changes the flags exactly when that result
  is tiny and exactly representable (`x86_binary_flags_eq_ieee_iff`);
* `UCOMISS`/`UCOMISD` signal invalid only for signaling NaNs and `COMISS`/`COMISD`
  for any NaN (`x86_ucomis_flags`, `x86_comis_flags`);
* `MINSS`/`MAXSS` signal invalid for any NaN operand, which differs from the IEEE
  minimum/maximum exactly when some operand is a quiet NaN and none is signaling
  (`x86_minMax_flags`, `x86_minMax_flags_eq_ieee_iff`);
* `CVT(T)SS2SI`/`CVT(T)SD2SI` signal invalid exactly when the conversion is out of
  range or the operand is a NaN or infinity, and then return the integer indefinite
  value (`toInt_invalid_iff`, `x86_toInt_of_invalid`).
-/

@[expose] public section

namespace Silmaril.Numeric.Float

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Ieee754
open Silmaril.Numeric.Ieee754.FlagSpec (Datum)

namespace Profile

variable (p : Profile) {fmt : Format}

/-! ## The rounding stage and result flushing -/

/-- The value of an operation is replaced by a zero exactly when the profile
flushes results and the exact result is tiny. -/
theorem flushSign?_isSome_iff (fmt : Format) (mode : RoundingMode) (o : FlagSpec.Outcome) :
    (p.flushSign? fmt mode o).isSome = true ↔
      p.flushResults = true ∧ o.IsTiny fmt p.tininess mode := by
  unfold flushSign?
  cases p.flushResults
  · simp
  · cases o <;> simp only [FlagSpec.Outcome.IsTiny, ↓reduceIte, Option.isSome_none,
      Bool.false_eq_true, true_and] <;> split <;> simp_all

/-- The rounding stage raises the IEEE flags, except for a tiny exact result of a
flushing profile, which raises `flushFlags`. -/
theorem flags_stage (fmt : Format) (mode : RoundingMode) (o : FlagSpec.Outcome) :
    o.flags (p.stage fmt mode) =
      if p.flushResults = true ∧ o.IsTiny fmt p.tininess mode then p.flushFlags
      else o.flags (.ieee fmt mode p.tininess) := by
  unfold stage
  cases hf : p.flushResults
  · simp
  · simp only [↓reduceIte]
    rw [FlagSpec.Outcome.flags_flushToZero]
    have hen : p.flushControl.Enabled true := Or.inr rfl
    simp only [hen, true_and]
    rfl

theorem flags_stage_of_false (fmt : Format) (mode : RoundingMode) (o : FlagSpec.Outcome)
    (h : p.flushResults = false) : o.flags (p.stage fmt mode) = o.flags (.ieee fmt mode p.tininess) :=
  by rw [stage_of_flushResults_false p fmt mode h]

/-! ## Arithmetic, square root, fused multiply-add and conversion -/

/-- Flags of `add`, `sub`, `mul` and `div`, for every profile. -/
theorem binary_flags (op : ArithOp) (mode : RoundingMode) (x y : Bits fmt) :
    (p.binary fmt op mode x y).flags =
      if p.flushResults = true ∧
          (op.outcome (p.inputDatum x) (p.inputDatum y)).IsTiny fmt p.tininess mode then
        p.flushFlags
      else op.ieeeFlags fmt mode p.tininess (p.inputDatum x) (p.inputDatum y) := by
  simp only [binary, datum_flushInput]
  rw [flags_stage, ArithOp.ieeeFlags_eq_outcome]

/-- Without flushing, `add`, `sub`, `mul` and `div` raise the IEEE flags. -/
theorem binary_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (op : ArithOp) (mode : RoundingMode) (x y : Bits fmt) :
    (p.binary fmt op mode x y).flags = op.ieeeFlags fmt mode p.tininess x.datum y.datum := by
  rw [binary_flags]
  simp [hin, hout]

theorem add_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x y : Bits fmt) :
    (p.add fmt mode x y).flags = FlagSpec.add fmt mode p.tininess x.datum y.datum :=
  p.binary_flags_ieee hin hout .add mode x y

theorem sub_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x y : Bits fmt) :
    (p.sub fmt mode x y).flags = FlagSpec.sub fmt mode p.tininess x.datum y.datum :=
  p.binary_flags_ieee hin hout .sub mode x y

theorem mul_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x y : Bits fmt) :
    (p.mul fmt mode x y).flags = FlagSpec.mul fmt mode p.tininess x.datum y.datum :=
  p.binary_flags_ieee hin hout .mul mode x y

theorem div_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x y : Bits fmt) :
    (p.div fmt mode x y).flags = FlagSpec.div fmt mode p.tininess x.datum y.datum :=
  p.binary_flags_ieee hin hout .div mode x y

/-- Flags of square root, for every profile. -/
theorem sqrt_flags (mode : RoundingMode) (x : Bits fmt) :
    (p.sqrt fmt mode x).flags =
      if p.flushResults = true ∧ (FlagSpec.sqrtOutcome (p.inputDatum x)).IsTiny fmt p.tininess mode
      then p.flushFlags
      else FlagSpec.sqrt fmt mode p.tininess (p.inputDatum x) := by
  simp only [sqrt, datum_flushInput]
  rw [flags_stage, FlagSpec.sqrt_eq_outcome]

theorem sqrt_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x : Bits fmt) :
    (p.sqrt fmt mode x).flags = FlagSpec.sqrt fmt mode p.tininess x.datum := by
  rw [sqrt_flags]
  simp [hin, hout]

/-- Flags of fused multiply-add, for every profile. The rule's
`infZeroQuietNaNInvalid` is the `FmaQuietAddend` policy of IEEE 754-2019 §7.2(c). -/
theorem fmaWith_flags (rule : FmaNaNRule) (mode : RoundingMode) (a b c : Bits fmt) :
    (p.fmaWith fmt rule mode a b c).flags =
      if p.flushResults = true ∧ (FlagSpec.fmaOutcome rule.quietAddend (p.inputDatum a)
          (p.inputDatum b) (p.inputDatum c)).IsTiny fmt p.tininess mode
      then p.flushFlags
      else FlagSpec.fma rule.quietAddend fmt mode p.tininess (p.inputDatum a) (p.inputDatum b)
        (p.inputDatum c) := by
  simp only [fmaWith, datum_flushInput]
  rw [flags_stage, FlagSpec.fma_eq_outcome]

theorem fmaWith_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (rule : FmaNaNRule) (mode : RoundingMode) (a b c : Bits fmt) :
    (p.fmaWith fmt rule mode a b c).flags =
      FlagSpec.fma rule.quietAddend fmt mode p.tininess a.datum b.datum c.datum := by
  rw [fmaWith_flags]
  simp [hin, hout]

/-- Flags of format conversion, classified in the destination format. -/
theorem convert_flags {src dst : Format} (mode : RoundingMode) (x : Bits src) :
    (p.convert src dst mode x).flags =
      if p.flushResults = true ∧ (FlagSpec.convertOutcome (p.inputDatum x)).IsTiny dst p.tininess mode
      then p.flushFlags
      else FlagSpec.convert dst mode p.tininess (p.inputDatum x) := by
  simp only [convert, datum_flushInput]
  rw [flags_stage, FlagSpec.convert_eq_outcome]

theorem convert_flags_ieee {src dst : Format} (hin : p.flushInputs = false)
    (hout : p.flushResults = false) (mode : RoundingMode) (x : Bits src) :
    (p.convert src dst mode x).flags = FlagSpec.convert dst mode p.tininess x.datum := by
  rw [convert_flags]
  simp [hin, hout]

/-- Integer-to-float conversion raises the IEEE flags for every profile: an
integer result is never tiny, so result flushing never applies. -/
theorem ofInt_flags (mode : RoundingMode) (n : Int) :
    (p.ofInt fmt mode n).flags = FlagSpec.ofInt fmt mode p.tininess n := by
  simp only [ofInt]
  have h : ¬ (p.flushResults = true ∧ (FlagSpec.ofIntOutcome n).IsTiny fmt p.tininess mode) :=
    fun h => FlagSpec.not_isTiny_ofIntOutcome fmt p.tininess mode n h.2
  rw [flags_stage, FlagSpec.ofInt_eq_outcome]
  simp only [h, ↓reduceIte]

/-! ## Round to integral and float-to-integer conversion -/

theorem roundToIntegral_flags (mode : RoundingMode) (signalInexact : Bool) (x : Bits fmt) :
    (p.roundToIntegral fmt mode signalInexact x).flags =
      FlagSpec.roundToIntegral mode signalInexact (p.inputDatum x) := by
  simp only [roundToIntegral, datum_flushInput]

theorem roundToIntegral_flags_ieee (hin : p.flushInputs = false) (mode : RoundingMode)
    (signalInexact : Bool) (x : Bits fmt) :
    (p.roundToIntegral fmt mode signalInexact x).flags =
      FlagSpec.roundToIntegral mode signalInexact x.datum := by
  rw [roundToIntegral_flags, inputDatum_of_false p x hin]

theorem toInt_flags (target : IntFormat) (mode : RoundingMode) (x : Bits fmt) :
    (p.toInt fmt target mode x).flags =
      FlagSpec.toInt target mode p.toIntSignalsInexact (p.inputDatum x) := by
  simp only [toInt, datum_flushInput]

theorem toInt_flags_ieee (hin : p.flushInputs = false) (target : IntFormat) (mode : RoundingMode)
    (x : Bits fmt) :
    (p.toInt fmt target mode x).flags =
      FlagSpec.toInt target mode p.toIntSignalsInexact x.datum := by
  rw [toInt_flags, inputDatum_of_false p x hin]

/-- A float-to-integer conversion signals invalid exactly when the executable
conversion fails, that is, exactly when it returns `intOverflowResult`. -/
theorem toInt_invalid_iff (target : IntFormat) (mode : RoundingMode) (x : Bits fmt) :
    (p.toInt fmt target mode x).flags.invalidOperation = true ↔
      Integer.fromFloat? target (p.flushInput x).value mode = none := by
  simp only [toInt, Integer.fromFloat?, Bits.toInt?_value]
  cases (p.flushInput x).datum with
  | nan s => simp [FlagSpec.toInt, Bits.finiteValue?]
  | infinity s => simp [FlagSpec.toInt, Bits.finiteValue?]
  | finite s v =>
    simp only [FlagSpec.toInt, Bits.finiteValue?, Option.map_some, Option.bind_some,
      Integer.ofInt?]
    by_cases hr : FlagSpec.roundInt mode v < target.minValue ∨
        target.maxValue < FlagSpec.roundInt mode v
    · have hr' : ¬ (target.minValue ≤ FlagSpec.roundInt mode v ∧
          FlagSpec.roundInt mode v ≤ target.maxValue) := by
        omega
      simp [hr, hr']
    · have hr' : target.minValue ≤ FlagSpec.roundInt mode v ∧
          FlagSpec.roundInt mode v ≤ target.maxValue := by
        omega
      simp only [hr, hr', ↓reduceIte, and_self, reduceCtorEq, iff_false]
      split <;> simp

/-- When a conversion signals invalid, it returns the profile's out-of-range
result. -/
theorem toInt_value_of_invalid (target : IntFormat) (mode : RoundingMode) (x : Bits fmt)
    (h : (p.toInt fmt target mode x).flags.invalidOperation = true) :
    (p.toInt fmt target mode x).value =
      intOverflowResult p.intOverflow target (p.flushInput x).value mode := by
  have hn := (p.toInt_invalid_iff target mode x).mp h
  simp only [toInt, hn]

/-- A conversion that does not signal invalid returns the exactly rounded integer. -/
theorem toInt_value_of_not_invalid (target : IntFormat) (mode : RoundingMode) (x : Bits fmt)
    (h : (p.toInt fmt target mode x).flags.invalidOperation = false) :
    ∃ n, Integer.fromFloat? target (p.flushInput x).value mode = some n ∧
      (p.toInt fmt target mode x).value = n.bits := by
  have hn : Integer.fromFloat? target (p.flushInput x).value mode ≠ none := fun hn => by
    rw [(p.toInt_invalid_iff target mode x).mpr hn] at h
    cases h
  obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp hn
  exact ⟨n, hn, by simp only [toInt, hn]⟩

/-! ## Comparisons and minimum/maximum -/

/-- Comparison flags do not depend on input flushing. -/
theorem compare_flags (signaling : Bool) (x y : Bits fmt) :
    (p.compare signaling x y).flags = FlagSpec.compare signaling x.datum y.datum := by
  simp only [compare, datum_flushInput, inputDatum]
  split
  · exact FlagSpec.compare_flushInput fmt signaling x.datum y.datum
  · rfl

/-- Comparison flags in terms of the encodings. -/
theorem compare_flags_eq (signaling : Bool) (x y : Bits fmt) :
    (p.compare signaling x y).flags =
      if x.isSignalingNaN || y.isSignalingNaN || (signaling && (x.isNaN || y.isNaN)) then
        FlagSpec.invalid
      else Flags.empty := by
  rw [compare_flags]
  simp [FlagSpec.compare]

theorem comparePredicate_flags (P : Predicate) (x y : Bits fmt) :
    (p.comparePredicate P x y).flags = FlagSpec.compare P.signaling x.datum y.datum :=
  p.compare_flags P.signaling x y

/-- Minimum/maximum flags do not depend on input flushing. -/
theorem minMaxWith_flags (rule : MinMaxRule) (isMax : Bool) (x y : Bits fmt) :
    (p.minMaxWith rule isMax x y).flags = rule.flags x.datum y.datum := by
  simp only [minMaxWith, datum_flushInput, inputDatum]
  split
  · cases rule <;> simp [MinMaxRule.flags]
  · rfl

/-- The IEEE minimum/maximum rules raise the IEEE flags: invalid exactly for a
signaling NaN operand. -/
theorem minMaxWith_flags_ieee (rule : MinMaxRule) (hrule : rule ≠ .x86) (isMax : Bool)
    (x y : Bits fmt) :
    (p.minMaxWith rule isMax x y).flags = FlagSpec.minMax x.datum y.datum := by
  rw [minMaxWith_flags]
  cases rule
  · exact absurd rfl hrule
  all_goals rfl

end Profile

/-! ## x86 SSE -/

section X86

variable (c : MXCSRControl) {fmt : Format}

theorem x86SSE_tininess : (Profile.x86SSE c).tininess = .afterRounding := rfl

/-- x86 FZ is the specification's masked-underflow flush rule (SDM Vol. 1
§10.2.3.3). -/
theorem x86SSE_flushControl :
    (Profile.x86SSE c).flushControl = FlagSpec.FlushToZero.maskedUnderflowInexact := by
  simp only [Profile.flushControl, Profile.x86SSE, underflowInexact,
    FlagSpec.FlushToZero.maskedUnderflowInexact]
  decide

/-- The x86 SSE rounding stage: after-rounding tininess, and with FZ the
masked-underflow flush rule. -/
theorem x86SSE_stage (mode : RoundingMode) :
    (Profile.x86SSE c).stage fmt mode =
      if c.flushToZero then .flushToZero .maskedUnderflowInexact true fmt mode .afterRounding
      else .ieee fmt mode .afterRounding := by
  rw [Profile.stage, x86SSE_flushControl]
  rfl

/-- With DAZ clear and FZ set, a finite exact result `v` raises the flags of the
masked-underflow flush rule. -/
theorem x86_binary_flags_ftz (hdaz : c.denormalsAreZeros = false) (hftz : c.flushToZero = true)
    (op : ArithOp) (mode : RoundingMode) (x y : Bits fmt) {v : ℚ}
    (hv : op.outcome x.datum y.datum = .finite v) :
    ((Profile.x86SSE c).binary fmt op mode x y).flags =
      FlagSpec.roundingFlagsFlushed .maskedUnderflowInexact true fmt mode .afterRounding v := by
  have hin : (Profile.x86SSE c).flushInputs = false := hdaz
  simp only [Profile.binary, Profile.datum_flushInput, Profile.inputDatum_of_false _ _ hin, hv,
    x86SSE_stage, hftz, ↓reduceIte]
  rfl

/-- With DAZ clear, x86 arithmetic with a finite exact result `v` raises the IEEE
flags unless FZ is set and `v` is tiny (after rounding) and exactly representable;
FZ then reports underflow and inexact where IEEE reports nothing. -/
theorem x86_binary_flags_eq_ieee_iff (hdaz : c.denormalsAreZeros = false) (op : ArithOp)
    (mode : RoundingMode) (x y : Bits fmt) {v : ℚ}
    (hv : op.outcome x.datum y.datum = .finite v) :
    ((Profile.x86SSE c).binary fmt op mode x y).flags =
        op.ieeeFlags fmt mode .afterRounding x.datum y.datum ↔
      (c.flushToZero = true →
        ¬ (FlagSpec.Tiny fmt .afterRounding mode v ∧ FlagSpec.Representable fmt v)) := by
  rw [ArithOp.ieeeFlags_eq_outcome, hv]
  cases hftz : c.flushToZero
  · have := (Profile.x86SSE c).binary_flags_ieee hdaz hftz op mode x y
    simp only [this, ArithOp.ieeeFlags_eq_outcome, hv, Bool.false_eq_true, false_implies,
      iff_true]
    rfl
  · rw [x86_binary_flags_ftz c hdaz hftz op mode x y hv]
    simp only [forall_const]
    exact FlagSpec.roundingFlagsFlushed_eq_roundingFlags_iff fmt mode .afterRounding v

/-- `UCOMISS`/`UCOMISD` signal invalid only for signaling NaN operands. -/
theorem x86_ucomis_flags (x y : Bits fmt) :
    ((Profile.x86SSE c).compare false x y).flags =
      if x.isSignalingNaN || y.isSignalingNaN then FlagSpec.invalid else Flags.empty := by
  rw [Profile.compare_flags_eq]
  simp

/-- `COMISS`/`COMISD` signal invalid for any NaN operand, quiet or signaling. -/
theorem x86_comis_flags (x y : Bits fmt) :
    ((Profile.x86SSE c).compare true x y).flags =
      if x.isNaN || y.isNaN then FlagSpec.invalid else Flags.empty := by
  rw [Profile.compare_flags, FlagSpec.compare_true, Bits.datum_isNaN, Bits.datum_isNaN]

/-- `MINSS`/`MINSD`/`MAXSS`/`MAXSD` signal invalid for any NaN operand. -/
theorem x86_minMax_flags (isMax : Bool) (x y : Bits fmt) :
    ((Profile.x86SSE c).minMaxBase isMax x y).flags =
      if x.isNaN || y.isNaN then FlagSpec.invalid else Flags.empty := by
  rw [Profile.minMaxBase, Profile.minMaxWith_flags]
  simp only [Profile.x86SSE, MinMaxRule.flags]
  rw [FlagSpec.compare_true, Bits.datum_isNaN, Bits.datum_isNaN]

/-- The x86 minimum/maximum flags are the IEEE minimum/maximum flags unless some
operand is a quiet NaN and neither is a signaling NaN. -/
theorem x86_minMax_flags_eq_ieee_iff (isMax : Bool) (x y : Bits fmt) :
    ((Profile.x86SSE c).minMaxBase isMax x y).flags = FlagSpec.minMax x.datum y.datum ↔
      ((x.isNaN || y.isNaN) = true → (x.isSignalingNaN || y.isSignalingNaN) = true) := by
  rw [Profile.minMaxBase, Profile.minMaxWith_flags]
  simp only [Profile.x86SSE, MinMaxRule.flags]
  rw [FlagSpec.compare_true_eq_minMax_iff, Bits.datum_isNaN, Bits.datum_isNaN,
    Bits.datum_isSignaling, Bits.datum_isSignaling]

/-- An x86 float-to-integer conversion that signals invalid returns the integer
indefinite value: the most negative signed value, or `2^w - 1` for the AVX-512
unsigned forms. -/
theorem x86_toInt_of_invalid (target : IntFormat) (mode : RoundingMode) (x : Bits fmt)
    (h : ((Profile.x86SSE c).toInt fmt target mode x).flags.invalidOperation = true) :
    ((Profile.x86SSE c).toInt fmt target mode x).value =
      (Integer.ofIntWrapping target (match target.signedness with
        | .signed => target.minValue
        | .unsigned => target.maxValue)).bits := by
  rw [Profile.toInt_value_of_invalid _ target mode x h]
  rfl

/-- x86 conversions to integer raise precision for inexact in-range results. -/
theorem x86_toInt_flags_ieee (hdaz : c.denormalsAreZeros = false) (target : IntFormat)
    (mode : RoundingMode) (x : Bits fmt) :
    ((Profile.x86SSE c).toInt fmt target mode x).flags = FlagSpec.toInt target mode true x.datum :=
  Profile.toInt_flags_ieee _ hdaz target mode x

end X86

/-! ## RISC-V and AArch64 -/

theorem riscvFD_tininess : Profile.riscvFD.tininess = .afterRounding := rfl

theorem aarch64_tininess (c : FPCRControl) : (Profile.aarch64 c).tininess = .beforeRounding := rfl

/-! RISC-V F/D never flushes (§11.4), so every operation raises the IEEE flags,
with after-rounding tininess where tininess matters. -/

section RiscV

variable {fmt : Format} (mode : RoundingMode)

theorem riscv_add_flags (x y : Bits fmt) :
    (Profile.riscvFD.add fmt mode x y).flags =
      FlagSpec.add fmt mode .afterRounding x.datum y.datum :=
  Profile.add_flags_ieee _ rfl rfl mode x y

theorem riscv_sub_flags (x y : Bits fmt) :
    (Profile.riscvFD.sub fmt mode x y).flags =
      FlagSpec.sub fmt mode .afterRounding x.datum y.datum :=
  Profile.sub_flags_ieee _ rfl rfl mode x y

theorem riscv_mul_flags (x y : Bits fmt) :
    (Profile.riscvFD.mul fmt mode x y).flags =
      FlagSpec.mul fmt mode .afterRounding x.datum y.datum :=
  Profile.mul_flags_ieee _ rfl rfl mode x y

theorem riscv_div_flags (x y : Bits fmt) :
    (Profile.riscvFD.div fmt mode x y).flags =
      FlagSpec.div fmt mode .afterRounding x.datum y.datum :=
  Profile.div_flags_ieee _ rfl rfl mode x y

theorem riscv_sqrt_flags (x : Bits fmt) :
    (Profile.riscvFD.sqrt fmt mode x).flags = FlagSpec.sqrt fmt mode .afterRounding x.datum :=
  Profile.sqrt_flags_ieee _ rfl rfl mode x

/-- `FMADD` and relatives signal invalid for `(±∞ × ±0) + qNaN` (§11.6). -/
theorem riscv_fma_flags (a b c : Bits fmt) :
    (Profile.riscvFD.fmaWith fmt riscvFmaNaNRule mode a b c).flags =
      FlagSpec.fma .signalInvalid fmt mode .afterRounding a.datum b.datum c.datum :=
  Profile.fmaWith_flags_ieee _ rfl rfl riscvFmaNaNRule mode a b c

theorem riscv_convert_flags {src dst : Format} (x : Bits src) :
    (Profile.riscvFD.convert src dst mode x).flags =
      FlagSpec.convert dst mode .afterRounding x.datum :=
  Profile.convert_flags_ieee _ rfl rfl mode x

/-- `FCVT.W.S` and relatives set NX for an inexact in-range result (§11.7). -/
theorem riscv_toInt_flags (target : IntFormat) (x : Bits fmt) :
    (Profile.riscvFD.toInt fmt target mode x).flags = FlagSpec.toInt target mode true x.datum :=
  Profile.toInt_flags_ieee _ rfl target mode x

theorem riscv_ofInt_flags (n : Int) :
    (Profile.riscvFD.ofInt fmt mode n).flags = FlagSpec.ofInt fmt mode .afterRounding n :=
  Profile.ofInt_flags _ mode n

end RiscV

/-- The AArch64 flush rule (`FPRoundBase` with FPCR.FZ = 1): a tiny result, with
tininess before rounding, raises Underflow alone. -/
theorem aarch64_flushControl (c : FPCRControl) :
    (Profile.aarch64 c).flushControl = { requiresUnderflowMasked := true, raises := underflowOnly } :=
  rfl

end Silmaril.Numeric.Float
