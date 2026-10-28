module

public import Silmaril.Numeric.Float.Wasm
public import Silmaril.Numeric.Float.Flags

/-!
# The interface a software floating-point implementation must meet

A `FloatImpl fmt` is any bit-level implementation of one format's scalar
operations, for example an integer-only software floating-point library for a
target without an FPU (a future x86 softfloat, or RISC-V without F/D).
`FloatImpl.Correct p impl` states that it returns exactly the profile's result
bits, IEEE exception flags and subnormal-operand indication for every operation
of that format (arithmetic, square root, fused multiply-add, minimum/maximum,
comparison, round-to-integral and the integer conversions), every input, every
rounding direction and every instruction variant the operations take as an
argument. `FloatImpl.CorrectValues p impl` is the weaker statement about result
bits only, so that an implementation can be verified for values before its flag
generation is.

Conversion between two formats involves two formats and is a separate
interface, `ConvertImpl src dst`, with the same `Correct`/`CorrectValues`
statements against `Profile.convert` (x86 `CVTSS2SD`/`CVTSD2SS`, RISC-V
`FCVT.D.S`/`FCVT.S.D`, AArch64 `FCVT`, WebAssembly `promote`/`demote`).
`SoftFloat p` bundles a binary32 and a binary64 implementation with both
conversions between them, which is the interface of a scalar unit as the
instruction layers here use it.

The reference implementations `FloatImpl.reference` and `ConvertImpl.reference`
are the profile operations themselves, so they are correct by definition
(`FloatImpl.reference_correct`, `ConvertImpl.reference_correct`). Its arithmetic
is already integer-only: `Silmaril.Numeric.Ieee754.Rounding` computes with natural
number significands and exact residuals. Its flags are the exception
specification `Silmaril.Numeric.Ieee754.Flags`, which decides tininess, overflow
and inexactness over `ℚ`; it is executable but not intended to be fast. A faster
implementation only has to prove `Correct` (or `CorrectValues`), and then inherits
every theorem proved about the profile: the WebAssembly admission results
(`CorrectValues.add_admitted32`, `ConvertImpl.CorrectValues.promote_admitted` and
the other transfer lemmas below) and the flag characterizations of
`Silmaril.Numeric.Float.Flags` (`Correct.add_flags_ieee`,
`ConvertImpl.Correct.convert_flags_ieee`, …).
-/

@[expose] public section

namespace Silmaril.Numeric.Float

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Ieee754
open Silmaril.Wasm Silmaril.Wasm.Numerics

/-- A bit-level implementation of the scalar operations of one format. -/
structure FloatImpl (fmt : Format) where
  add : RoundingMode → Bits fmt → Bits fmt → Outcome (Bits fmt)
  sub : RoundingMode → Bits fmt → Bits fmt → Outcome (Bits fmt)
  mul : RoundingMode → Bits fmt → Bits fmt → Outcome (Bits fmt)
  div : RoundingMode → Bits fmt → Bits fmt → Outcome (Bits fmt)
  sqrt : RoundingMode → Bits fmt → Outcome (Bits fmt)
  fma : FmaNaNRule → RoundingMode → Bits fmt → Bits fmt → Bits fmt → Outcome (Bits fmt)
  minMax : MinMaxRule → Bool → Bits fmt → Bits fmt → Outcome (Bits fmt)
  compare : Bool → Bits fmt → Bits fmt → Outcome (Option Ordering)
  roundToIntegral : RoundingMode → Bool → Bits fmt → Outcome (Bits fmt)
  toInt : (target : IntFormat) → RoundingMode → Bits fmt → Outcome (BitVec target.width)
  ofInt : RoundingMode → Int → Outcome (Bits fmt)


namespace FloatImpl

variable {fmt : Format}

/-- The profile operations, packaged as an implementation. -/
def reference (p : Profile) (fmt : Format) : FloatImpl fmt where
  add := p.add fmt
  sub := p.sub fmt
  mul := p.mul fmt
  div := p.div fmt
  sqrt := p.sqrt fmt
  fma := p.fmaWith fmt
  minMax := p.minMaxWith
  compare := p.compare
  roundToIntegral := p.roundToIntegral fmt
  toInt := p.toInt fmt
  ofInt := p.ofInt fmt

/-- `impl` returns the profile's outcome (bits, IEEE flags, subnormal indication)
for every operation and input. -/
structure Correct (p : Profile) (impl : FloatImpl fmt) : Prop where
  add : ∀ mode x y, impl.add mode x y = p.add fmt mode x y
  sub : ∀ mode x y, impl.sub mode x y = p.sub fmt mode x y
  mul : ∀ mode x y, impl.mul mode x y = p.mul fmt mode x y
  div : ∀ mode x y, impl.div mode x y = p.div fmt mode x y
  sqrt : ∀ mode x, impl.sqrt mode x = p.sqrt fmt mode x
  fma : ∀ rule mode a b c, impl.fma rule mode a b c = p.fmaWith fmt rule mode a b c
  minMax : ∀ rule isMax x y, impl.minMax rule isMax x y = p.minMaxWith rule isMax x y
  compare : ∀ signaling x y, impl.compare signaling x y = p.compare signaling x y
  roundToIntegral : ∀ mode signalInexact x,
    impl.roundToIntegral mode signalInexact x = p.roundToIntegral fmt mode signalInexact x
  toInt : ∀ target mode x, impl.toInt target mode x = p.toInt fmt target mode x
  ofInt : ∀ mode n, impl.ofInt mode n = p.ofInt fmt mode n

/-- `impl` returns the profile's result bits for every operation and input. -/
structure CorrectValues (p : Profile) (impl : FloatImpl fmt) : Prop where
  add : ∀ mode x y, (impl.add mode x y).value = (p.add fmt mode x y).value
  sub : ∀ mode x y, (impl.sub mode x y).value = (p.sub fmt mode x y).value
  mul : ∀ mode x y, (impl.mul mode x y).value = (p.mul fmt mode x y).value
  div : ∀ mode x y, (impl.div mode x y).value = (p.div fmt mode x y).value
  sqrt : ∀ mode x, (impl.sqrt mode x).value = (p.sqrt fmt mode x).value
  fma : ∀ rule mode a b c,
    (impl.fma rule mode a b c).value = (p.fmaWith fmt rule mode a b c).value
  minMax : ∀ rule isMax x y,
      (impl.minMax rule isMax x y).value = (p.minMaxWith rule isMax x y).value
  compare : ∀ signaling x y, (impl.compare signaling x y).value = (p.compare signaling x y).value
  roundToIntegral : ∀ mode signalInexact x,
    (impl.roundToIntegral mode signalInexact x).value =
      (p.roundToIntegral fmt mode signalInexact x).value
  toInt : ∀ target mode x,
      (impl.toInt target mode x).value = (p.toInt fmt target mode x).value
  ofInt : ∀ mode n, (impl.ofInt mode n).value = (p.ofInt fmt mode n).value

/-- The reference implementation is correct for its own profile. -/
theorem reference_correct (p : Profile) (fmt : Format) :
    Correct p (reference p fmt) where
  add _ _ _ := rfl
  sub _ _ _ := rfl
  mul _ _ _ := rfl
  div _ _ _ := rfl
  sqrt _ _ := rfl
  fma _ _ _ _ _ := rfl
  minMax _ _ _ _ := rfl
  compare _ _ _ := rfl
  roundToIntegral _ _ _ := rfl
  toInt _ _ _ := rfl
  ofInt _ _ := rfl

/-- A correct implementation is the reference implementation. -/
theorem Correct.eq_reference {p : Profile} {impl : FloatImpl fmt}
    (h : Correct p impl) : impl = reference p fmt := by
  cases impl
  simp only [reference, mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext <;>
    first
      | exact h.add _ _ _
      | exact h.sub _ _ _
      | exact h.mul _ _ _
      | exact h.div _ _ _
      | exact h.sqrt _ _
      | exact h.fma _ _ _ _ _
      | exact h.minMax _ _ _ _
      | exact h.compare _ _ _
      | exact h.roundToIntegral _ _ _
      | exact h.toInt _ _ _
      | exact h.ofInt _ _

/-- Two correct implementations agree everywhere. -/
theorem Correct.unique {p : Profile} {impl₁ impl₂ : FloatImpl fmt}
    (h₁ : Correct p impl₁) (h₂ : Correct p impl₂) : impl₁ = impl₂ :=
  h₁.eq_reference.trans h₂.eq_reference.symm

end FloatImpl

namespace FloatImpl

variable {fmt : Format}

/-- Full correctness implies correctness of result bits. -/
theorem Correct.values {p : Profile} {impl : FloatImpl fmt}
    (h : Correct p impl) : CorrectValues p impl where
  add mode x y := by rw [h.add]
  sub mode x y := by rw [h.sub]
  mul mode x y := by rw [h.mul]
  div mode x y := by rw [h.div]
  sqrt mode x := by rw [h.sqrt]
  fma rule mode a b c := by rw [h.fma]
  minMax rule isMax x y := by rw [h.minMax]
  compare signaling x y := by rw [h.compare]
  roundToIntegral mode signalInexact x := by rw [h.roundToIntegral]
  toInt target mode x := by rw [h.toInt]
  ofInt mode n := by rw [h.ofInt]

/-! ## Flag transfer lemmas

A correct implementation raises the flags characterized in
`Silmaril.Numeric.Float.Flags`. Without flushing these are the IEEE default flags. -/

section Flags

variable {p : Profile} {impl : FloatImpl fmt} (h : Correct p impl)
include h

theorem Correct.add_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x y : Bits fmt) :
    (impl.add mode x y).flags = FlagSpec.add fmt mode p.tininess x.datum y.datum := by
  rw [h.add]
  exact p.add_flags_ieee hin hout mode x y

theorem Correct.sub_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x y : Bits fmt) :
    (impl.sub mode x y).flags = FlagSpec.sub fmt mode p.tininess x.datum y.datum := by
  rw [h.sub]
  exact p.sub_flags_ieee hin hout mode x y

theorem Correct.mul_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x y : Bits fmt) :
    (impl.mul mode x y).flags = FlagSpec.mul fmt mode p.tininess x.datum y.datum := by
  rw [h.mul]
  exact p.mul_flags_ieee hin hout mode x y

theorem Correct.div_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x y : Bits fmt) :
    (impl.div mode x y).flags = FlagSpec.div fmt mode p.tininess x.datum y.datum := by
  rw [h.div]
  exact p.div_flags_ieee hin hout mode x y

theorem Correct.sqrt_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x : Bits fmt) :
    (impl.sqrt mode x).flags = FlagSpec.sqrt fmt mode p.tininess x.datum := by
  rw [h.sqrt]
  exact p.sqrt_flags_ieee hin hout mode x

theorem Correct.fma_flags_ieee (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (rule : FmaNaNRule) (mode : RoundingMode) (a b c : Bits fmt) :
    (impl.fma rule mode a b c).flags =
      FlagSpec.fma rule.quietAddend fmt mode p.tininess a.datum b.datum c.datum := by
  rw [h.fma]
  exact p.fmaWith_flags_ieee hin hout rule mode a b c

theorem Correct.compare_flags (signaling : Bool) (x y : Bits fmt) :
    (impl.compare signaling x y).flags = FlagSpec.compare signaling x.datum y.datum := by
  rw [h.compare]
  exact p.compare_flags signaling x y

theorem Correct.minMax_flags (rule : MinMaxRule) (isMax : Bool) (x y : Bits fmt) :
    (impl.minMax rule isMax x y).flags = rule.flags x.datum y.datum := by
  rw [h.minMax]
  exact p.minMaxWith_flags rule isMax x y

theorem Correct.roundToIntegral_flags_ieee (hin : p.flushInputs = false) (mode : RoundingMode)
    (signalInexact : Bool) (x : Bits fmt) :
    (impl.roundToIntegral mode signalInexact x).flags =
      FlagSpec.roundToIntegral mode signalInexact x.datum := by
  rw [h.roundToIntegral]
  exact p.roundToIntegral_flags_ieee hin mode signalInexact x

theorem Correct.toInt_flags_ieee (hin : p.flushInputs = false) (target : IntFormat)
    (mode : RoundingMode) (x : Bits fmt) :
    (impl.toInt target mode x).flags =
      FlagSpec.toInt target mode p.toIntSignalsInexact x.datum := by
  rw [h.toInt]
  exact p.toInt_flags_ieee hin target mode x

theorem Correct.ofInt_flags (mode : RoundingMode) (n : Int) :
    (impl.ofInt mode n).flags = FlagSpec.ofInt fmt mode p.tininess n := by
  rw [h.ofInt]
  exact p.ofInt_flags mode n

end Flags

/-! ## WebAssembly transfer lemmas

Each lemma restates a theorem of `Silmaril.Numeric.Float.Wasm` for any
implementation whose result bits are correct. -/

section Transfer

variable {p : Profile} (hin : p.flushInputs = false)
include hin

/-- binary32 `add`/`sub`/`mul`/`div` of a value-correct implementation are admitted. -/
theorem CorrectValues.binary_admitted32 {impl : FloatImpl .binary32} (h : CorrectValues p impl)
    (hout : p.flushResults = false) (x y : BitVec 32) :
    floatBinOpRel .f32 .add x y (impl.add .nearestTiesToEven x y).value ∧
    floatBinOpRel .f32 .sub x y (impl.sub .nearestTiesToEven x y).value ∧
    floatBinOpRel .f32 .mul x y (impl.mul .nearestTiesToEven x y).value ∧
    floatBinOpRel .f32 .div x y (impl.div .nearestTiesToEven x y).value := by
  rw [h.add, h.sub, h.mul, h.div]
  exact ⟨Silmaril.Numeric.Float.binary_admitted32 p hin hout .add _ rfl x y,
    Silmaril.Numeric.Float.binary_admitted32 p hin hout .sub _ rfl x y,
    Silmaril.Numeric.Float.binary_admitted32 p hin hout .mul _ rfl x y,
    Silmaril.Numeric.Float.binary_admitted32 p hin hout .div _ rfl x y⟩

/-- binary64 `add`/`sub`/`mul`/`div` of a value-correct implementation are admitted. -/
theorem CorrectValues.binary_admitted64 {impl : FloatImpl .binary64} (h : CorrectValues p impl)
    (hout : p.flushResults = false) (x y : BitVec 64) :
    floatBinOpRel .f64 .add x y (impl.add .nearestTiesToEven x y).value ∧
    floatBinOpRel .f64 .sub x y (impl.sub .nearestTiesToEven x y).value ∧
    floatBinOpRel .f64 .mul x y (impl.mul .nearestTiesToEven x y).value ∧
    floatBinOpRel .f64 .div x y (impl.div .nearestTiesToEven x y).value := by
  rw [h.add, h.sub, h.mul, h.div]
  exact ⟨Silmaril.Numeric.Float.binary_admitted64 p hin hout .add _ rfl x y,
    Silmaril.Numeric.Float.binary_admitted64 p hin hout .sub _ rfl x y,
    Silmaril.Numeric.Float.binary_admitted64 p hin hout .mul _ rfl x y,
    Silmaril.Numeric.Float.binary_admitted64 p hin hout .div _ rfl x y⟩

/-- binary32 `add` alone, the most common use. -/
theorem CorrectValues.add_admitted32 {impl : FloatImpl .binary32} (h : CorrectValues p impl)
    (hout : p.flushResults = false) (x y : BitVec 32) :
    floatBinOpRel .f32 .add x y (impl.add .nearestTiesToEven x y).value :=
  (h.binary_admitted32 hin hout x y).1

/-- binary32 `sqrt`. -/
theorem CorrectValues.sqrt_admitted32 {impl : FloatImpl .binary32} (h : CorrectValues p impl)
    (hout : p.flushResults = false) (x : BitVec 32) :
    floatUnOpRel .f32 .sqrt x (impl.sqrt .nearestTiesToEven x).value := by
  rw [h.sqrt]
  exact Silmaril.Numeric.Float.sqrt_admitted32 p hin hout x

/-- binary64 `sqrt`. -/
theorem CorrectValues.sqrt_admitted64 {impl : FloatImpl .binary64} (h : CorrectValues p impl)
    (hout : p.flushResults = false) (x : BitVec 64) :
    floatUnOpRel .f64 .sqrt x (impl.sqrt .nearestTiesToEven x).value := by
  rw [h.sqrt]
  exact Silmaril.Numeric.Float.sqrt_admitted64 p hin hout x

/-- binary32 `ceil`/`floor`/`trunc`/`nearest` in their static direction. -/
theorem CorrectValues.roundToIntegral_admitted32 {impl : FloatImpl .binary32}
    (h : CorrectValues p impl) (op : Wasm.FloatUnOp) (mode : RoundingMode)
    (hop : wasmIntegralMode? op = some mode) (signalInexact : Bool) (x : BitVec 32) :
    floatUnOpRel .f32 op x (impl.roundToIntegral mode signalInexact x).value := by
  rw [h.roundToIntegral]
  exact Silmaril.Numeric.Float.roundToIntegral_admitted32 p hin op mode hop signalInexact x

/-- binary64 `ceil`/`floor`/`trunc`/`nearest` in their static direction. -/
theorem CorrectValues.roundToIntegral_admitted64 {impl : FloatImpl .binary64}
    (h : CorrectValues p impl) (op : Wasm.FloatUnOp) (mode : RoundingMode)
    (hop : wasmIntegralMode? op = some mode) (signalInexact : Bool) (x : BitVec 64) :
    floatUnOpRel .f64 op x (impl.roundToIntegral mode signalInexact x).value := by
  rw [h.roundToIntegral]
  exact Silmaril.Numeric.Float.roundToIntegral_admitted64 p hin op mode hop signalInexact x

/-- binary32 `min`/`max`. -/
theorem CorrectValues.minMax_admitted_iff32 {impl : FloatImpl .binary32} (h : CorrectValues p impl)
    (rule : MinMaxRule) (isMax : Bool) (x y : BitVec 32) :
    floatBinOpRel .f32 (if isMax then .max else .min) x y (impl.minMax rule isMax x y).value ↔
      rule.agreesWithWasm (fmt := .binary32) isMax x y = true := by
  rw [h.minMax]
  exact Silmaril.Numeric.Float.minMax_admitted_iff32 p hin rule isMax x y

/-- binary64 `min`/`max`. -/
theorem CorrectValues.minMax_admitted_iff64 {impl : FloatImpl .binary64} (h : CorrectValues p impl)
    (rule : MinMaxRule) (isMax : Bool) (x y : BitVec 64) :
    floatBinOpRel .f64 (if isMax then .max else .min) x y (impl.minMax rule isMax x y).value ↔
      rule.agreesWithWasm (fmt := .binary64) isMax x y = true := by
  rw [h.minMax]
  exact Silmaril.Numeric.Float.minMax_admitted_iff64 p hin rule isMax x y

/-- binary32 comparisons. -/
theorem CorrectValues.compare_eq32 {impl : FloatImpl .binary32} (h : CorrectValues p impl)
    (op : FloatRelOp) (x y : BitVec 32) :
    bool32 ((wasmPredicate op).eval (impl.compare (wasmPredicate op).signaling x y).value) =
      floatRelOp .f32 op x y := by
  rw [h.compare, ← Silmaril.Numeric.Float.comparePredicate_eq_floatRelOp32 p hin op x y]
  rfl

/-- binary64 comparisons. -/
theorem CorrectValues.compare_eq64 {impl : FloatImpl .binary64} (h : CorrectValues p impl)
    (op : FloatRelOp) (x y : BitVec 64) :
    bool32 ((wasmPredicate op).eval (impl.compare (wasmPredicate op).signaling x y).value) =
      floatRelOp .f64 op x y := by
  rw [h.compare, ← Silmaril.Numeric.Float.comparePredicate_eq_floatRelOp64 p hin op x y]
  rfl

/-- binary32 truncation agrees with WebAssembly `trunc` whenever it does not trap. -/
theorem CorrectValues.toInt_of_truncFloat_ok32 {impl : FloatImpl .binary32}
    (h : CorrectValues p impl) (target : IntType) (sign : Wasm.Signedness) {x : BitVec 32}
    {v : IntValue target} (hv : truncFloat .f32 target sign x = .ok v) :
    (impl.toInt (integerFormat target sign) .towardZero x).value = v := by
  rw [h.toInt]
  exact Silmaril.Numeric.Float.toInt_of_truncFloat_ok32 p hin target sign hv

/-- binary64 truncation agrees with WebAssembly `trunc` whenever it does not trap. -/
theorem CorrectValues.toInt_of_truncFloat_ok64 {impl : FloatImpl .binary64}
    (h : CorrectValues p impl) (target : IntType) (sign : Wasm.Signedness) {x : BitVec 64}
    {v : IntValue target} (hv : truncFloat .f64 target sign x = .ok v) :
    (impl.toInt (integerFormat target sign) .towardZero x).value = v := by
  rw [h.toInt]
  exact Silmaril.Numeric.Float.toInt_of_truncFloat_ok64 p hin target sign hv

omit hin in
/-- binary32 integer-to-float conversion equals WebAssembly `convert`. -/
theorem CorrectValues.ofInt_eq_convertInt32 {impl : FloatImpl .binary32}
    (h : CorrectValues p impl) (source : IntType) (sign : Wasm.Signedness)
    (x : IntValue source) :
    convertInt source .f32 sign x =
      (impl.ofInt .nearestTiesToEven
        (match sign with | .signed => x.toInt | .unsigned => (x.toNat : Int))).value := by
  rw [h.ofInt]
  exact Silmaril.Numeric.Float.ofInt_eq_convertInt32 p source sign x

omit hin in
/-- binary64 integer-to-float conversion equals WebAssembly `convert`. -/
theorem CorrectValues.ofInt_eq_convertInt64 {impl : FloatImpl .binary64}
    (h : CorrectValues p impl) (source : IntType) (sign : Wasm.Signedness)
    (x : IntValue source) :
    convertInt source .f64 sign x =
      (impl.ofInt .nearestTiesToEven
        (match sign with | .signed => x.toInt | .unsigned => (x.toNat : Int))).value := by
  rw [h.ofInt]
  exact Silmaril.Numeric.Float.ofInt_eq_convertInt64 p source sign x

end Transfer

end FloatImpl

/-! ## Conversion between formats -/

/-- A bit-level implementation of conversion from format `src` to format `dst`. -/
structure ConvertImpl (src dst : Format) where
  convert : RoundingMode → Bits src → Outcome (Bits dst)

namespace ConvertImpl

variable {src dst : Format}

/-- The profile's conversion, packaged as an implementation. -/
def reference (p : Profile) (src dst : Format) : ConvertImpl src dst where
  convert := p.convert src dst

/-- `impl` returns the profile's outcome (bits, IEEE flags, subnormal indication)
for every rounding direction and input. -/
structure Correct (p : Profile) (impl : ConvertImpl src dst) : Prop where
  convert : ∀ mode x, impl.convert mode x = p.convert src dst mode x

/-- `impl` returns the profile's result bits for every rounding direction and input. -/
structure CorrectValues (p : Profile) (impl : ConvertImpl src dst) : Prop where
  convert : ∀ mode x, (impl.convert mode x).value = (p.convert src dst mode x).value

theorem reference_correct (p : Profile) (src dst : Format) : Correct p (reference p src dst) :=
  ⟨fun _ _ => rfl⟩

/-- A correct implementation is the reference implementation. -/
theorem Correct.eq_reference {p : Profile} {impl : ConvertImpl src dst} (h : Correct p impl) :
    impl = reference p src dst := by
  cases impl
  simp only [reference, mk.injEq]
  funext mode x
  exact h.convert mode x

theorem Correct.values {p : Profile} {impl : ConvertImpl src dst} (h : Correct p impl) :
    CorrectValues p impl :=
  ⟨fun mode x => by rw [h.convert]⟩

/-- Flags of a correct conversion, for every profile: the IEEE flags classified in
the destination format, or `flushFlags` for a tiny result of a flushing profile. -/
theorem Correct.convert_flags {p : Profile} {impl : ConvertImpl src dst} (h : Correct p impl)
    (mode : RoundingMode) (x : Bits src) :
    (impl.convert mode x).flags =
      if p.flushResults = true ∧
          (FlagSpec.convertOutcome (p.inputDatum x)).IsTiny dst p.tininess mode
      then p.flushFlags
      else FlagSpec.convert dst mode p.tininess (p.inputDatum x) := by
  rw [h.convert]
  exact p.convert_flags mode x

/-- Without flushing, a correct conversion raises the IEEE flags. -/
theorem Correct.convert_flags_ieee {p : Profile} {impl : ConvertImpl src dst}
    (h : Correct p impl) (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (mode : RoundingMode) (x : Bits src) :
    (impl.convert mode x).flags = FlagSpec.convert dst mode p.tininess x.datum := by
  rw [h.convert]
  exact p.convert_flags_ieee hin hout mode x

/-- `f64.promote_f32` of a value-correct implementation is admitted. -/
theorem CorrectValues.promote_admitted {p : Profile} {impl : ConvertImpl .binary32 .binary64}
    (h : CorrectValues p impl) (hin : p.flushInputs = false) (x : BitVec 32) :
    convertRel .promote x (.ok (impl.convert .nearestTiesToEven x).value) := by
  rw [h.convert]
  exact Silmaril.Numeric.Float.promote_admitted p hin x

/-- `f32.demote_f64` of a value-correct implementation is admitted. -/
theorem CorrectValues.demote_admitted {p : Profile} {impl : ConvertImpl .binary64 .binary32}
    (h : CorrectValues p impl) (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (x : BitVec 64) :
    convertRel .demote x (.ok (impl.convert .nearestTiesToEven x).value) := by
  rw [h.convert]
  exact Silmaril.Numeric.Float.demote_admitted p hin hout x

end ConvertImpl

/-! ## A scalar binary32/binary64 unit -/

/-- Implementations of every scalar binary32 and binary64 operation and of both
conversions between the two formats. -/
structure SoftFloat where
  f32 : FloatImpl .binary32
  f64 : FloatImpl .binary64
  promote : ConvertImpl .binary32 .binary64
  demote : ConvertImpl .binary64 .binary32

namespace SoftFloat

/-- The profile operations, packaged as a unit. -/
def reference (p : Profile) : SoftFloat where
  f32 := FloatImpl.reference p .binary32
  f64 := FloatImpl.reference p .binary64
  promote := ConvertImpl.reference p .binary32 .binary64
  demote := ConvertImpl.reference p .binary64 .binary32

/-- Every component returns the profile's outcome. -/
structure Correct (p : Profile) (u : SoftFloat) : Prop where
  f32 : FloatImpl.Correct p u.f32
  f64 : FloatImpl.Correct p u.f64
  promote : ConvertImpl.Correct p u.promote
  demote : ConvertImpl.Correct p u.demote

/-- Every component returns the profile's result bits. -/
structure CorrectValues (p : Profile) (u : SoftFloat) : Prop where
  f32 : FloatImpl.CorrectValues p u.f32
  f64 : FloatImpl.CorrectValues p u.f64
  promote : ConvertImpl.CorrectValues p u.promote
  demote : ConvertImpl.CorrectValues p u.demote

theorem reference_correct (p : Profile) : Correct p (reference p) :=
  ⟨FloatImpl.reference_correct p _, FloatImpl.reference_correct p _,
    ConvertImpl.reference_correct p _ _, ConvertImpl.reference_correct p _ _⟩

theorem Correct.values {p : Profile} {u : SoftFloat} (h : Correct p u) : CorrectValues p u :=
  ⟨h.f32.values, h.f64.values, h.promote.values, h.demote.values⟩

/-- A correct unit is the reference unit. -/
theorem Correct.eq_reference {p : Profile} {u : SoftFloat} (h : Correct p u) :
    u = reference p := by
  cases u
  simp only [reference, mk.injEq]
  exact ⟨h.f32.eq_reference, h.f64.eq_reference, h.promote.eq_reference, h.demote.eq_reference⟩

end SoftFloat

end Silmaril.Numeric.Float
