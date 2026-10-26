module

public import Silmaril.Numeric.Float.Profile

/-!
# Profile-parametric scalar floating-point operations

Every operation takes a `Profile`, a format and raw operand encodings, and returns
an `Outcome`: result bits, IEEE status flags, and whether a subnormal operand was
seen. The numerical value of each non-NaN, non-flushed result is the existing
correctly rounded model in `Silmaril.Numeric.Ieee754.Rounding` (`addRounded`,
`divRounded`, `packRounded`, …), for every IEEE rounding direction. The profile
decides only what those functions leave open:

1. input flushing of subnormal operands (`Profile.flushInput`);
2. NaN results for NaN operands (`pickNaN`) and for invalid operations on
   non-NaN operands (the profile's default NaN);
3. flushing of tiny results (`flushSign?`), using the profile's tininess detection;
4. min/max, float-to-integer and comparison conventions.

## Flags

The flags of every operation are the exception specification of
`Silmaril.Numeric.Ieee754.Flags` (`FlagSpec`) applied to the operands after input
flushing (`Bits.datum` of `Profile.flushInput`):

* arithmetic, square root, fused multiply-add, format conversion and
  integer-to-float conversion evaluate the operation's `FlagSpec.Outcome` in the
  profile's rounding stage (`Profile.stage`), which is the IEEE classification
  (IEEE 754-2019 §§7.4–7.6) with the profile's tininess detection, or output
  flushing when the profile flushes results;
* comparisons use `FlagSpec.compare`, minimum/maximum `FlagSpec.minMax` (or, for
  `MinMaxRule.x86`, the flags of a signaling comparison), round-to-integral
  `FlagSpec.roundToIntegral` and float-to-integer conversion `FlagSpec.toInt`.

The flush decision for result *values* uses the same tininess predicate as the
flags (`FlagSpec.Outcome.IsTiny` of the exact result), so a result is replaced by
a zero exactly when its flags are replaced by `Profile.flushFlags`. The theorems
relating these flags to the IEEE flag functions, with and without flushing, are in
`Silmaril.Numeric.Float.Flags`.

The flags are computed from the exact result, independently of the returned
bits. The executable rounding these operations call delivers the
specification's `FlagSpec.deliver` of the exact value, in every format:
`Rounding.packRounded` (`roundedOf?_unpack_packRounded`), `Rounding.divRounded`
and `Rounding.sqrtRounded` (`Silmaril.Numeric.Ieee754.Flags.DivSqrt`) and, for
`FlagSpec.roundInt`, `Rounding.integralRounded`. `Silmaril.Numeric.Float.Delivered`
lifts this to the profile operations when the profile flushes neither inputs nor
results: on finite operands, `binary`, `sqrt`, `fmaWith`, `convert` and `ofInt`
return an encoding of the delivered result, and inexact is raised exactly when it
differs from the exact result. With result flushing, the FZ path departs from this
by design on exact tiny results; round-to-integral is related only through the
binary32/binary64 wrappers (`F32.roundToIntegralFlags_inexact_iff`).
-/

@[expose] public section

namespace Silmaril.Numeric.Float

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Ieee754
open Silmaril.Numeric.Ieee754.FlagSpec (Datum)

namespace CoreOp

/-- The correctly rounded result bits in the given direction. -/
def round (fmt : Format) (mode : RoundingMode) : CoreOp → Bits fmt
  | .add x y => Rounding.addRounded fmt mode x y
  | .sub x y => Rounding.subRounded fmt mode x y
  | .mul x y => Rounding.mulRounded fmt mode x y
  | .div x y => Rounding.divRounded fmt mode x y
  | .sqrt x => Rounding.sqrtRounded fmt mode x
  | .fma x y z => Rounding.fmaRounded fmt mode x y z
  | .convert x => Rounding.packRounded fmt mode x

/-- The operands of the operation. -/
def operands : CoreOp → List UnpackedFloat
  | .add x y | .sub x y | .mul x y | .div x y => [x, y]
  | .sqrt x | .convert x => [x]
  | .fma x y z => [x, y, z]

end CoreOp

/-- The four binary arithmetic operations of IEEE 754-2019 §5.4.1. -/
inductive ArithOp where
  | add
  | sub
  | mul
  | div
  deriving DecidableEq, Repr

namespace ArithOp

/-- The core operation computing the value. -/
def core : ArithOp → UnpackedFloat → UnpackedFloat → CoreOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div

/-- The exception specification's outcome of the operation. -/
def outcome : ArithOp → Datum → Datum → FlagSpec.Outcome
  | .add => FlagSpec.addOutcome
  | .sub => FlagSpec.subOutcome
  | .mul => FlagSpec.mulOutcome
  | .div => FlagSpec.divOutcome

/-- The IEEE default flags of the operation (`FlagSpec.add`, `sub`, `mul`, `div`). -/
def ieeeFlags : ArithOp → Format → RoundingMode → FlagSpec.Tininess → Datum → Datum → Flags
  | .add => FlagSpec.add
  | .sub => FlagSpec.sub
  | .mul => FlagSpec.mul
  | .div => FlagSpec.div

theorem ieeeFlags_eq_outcome (op : ArithOp) (f : Format) (mode : RoundingMode)
    (tininess : FlagSpec.Tininess) (x y : Datum) :
    op.ieeeFlags f mode tininess x y = (op.outcome x y).flags (.ieee f mode tininess) := by
  cases op
  · exact FlagSpec.add_eq_outcome f mode tininess x y
  · exact FlagSpec.sub_eq_outcome f mode tininess x y
  · exact FlagSpec.mul_eq_outcome f mode tininess x y
  · exact FlagSpec.div_eq_outcome f mode tininess x y

end ArithOp

/-- The flags of a minimum/maximum rule: those of a signaling comparison for x86
`MINSS`/`MAXSS` (invalid for any NaN operand, Intel SDM Vol. 2 `MINSS`,
"SIMD Floating-Point Exceptions: Invalid (including QNaN source operand)"), and
the IEEE minimum/maximum flags (invalid for signaling NaN operands only) for the
IEEE rules. -/
def MinMaxRule.flags : MinMaxRule → Datum → Datum → Flags
  | .x86 => FlagSpec.compare true
  | .minNum | .minimum | .minimumNumber => FlagSpec.minMax

namespace Profile

variable (p : Profile)

/-- The NaN an operation returns when some operand, in the given order, is a NaN. -/
def pickNaN {fmt : Format} (operands : List (Bits fmt)) : Bits fmt :=
  match p.propagation with
  | .defaultNaN => p.defaultNaN fmt
  | .firstNaN =>
    match operands.find? Bits.isNaN with
    | some b => b.quiet
    | none => p.defaultNaN fmt
  | .signalingFirst =>
    match operands.find? Bits.isSignalingNaN with
    | some b => b.quiet
    | none =>
      match operands.find? Bits.isNaN with
      | some b => b.quiet
      | none => p.defaultNaN fmt

/-- When a flushing profile replaces the result of an operation with the given
outcome by a zero, the zero's sign: the sign of the exact result, which is then
tiny (`FlagSpec.Outcome.IsTiny`) and so nonzero. -/
def flushSign? (fmt : Format) (mode : RoundingMode) (o : FlagSpec.Outcome) : Option Sign :=
  if p.flushResults then
    match o with
    | .finite v =>
      if FlagSpec.Tiny fmt p.tininess mode v then
        some (if v < 0 then .negative else .positive)
      else none
    | .sqrt a => if FlagSpec.SqrtTiny fmt p.tininess mode a then some .positive else none
    | _ => none
  else none

/-- The result of a core operation on non-NaN operands: the correctly rounded
bits, the default NaN for an invalid operation, or a flushed zero. -/
def finish (fmt : Format) (mode : RoundingMode) (op : CoreOp) (o : FlagSpec.Outcome) : Bits fmt :=
  let r := op.round fmt mode
  if r.isNaN then p.defaultNaN fmt
  else
    match p.flushSign? fmt mode o with
    | some s => packedZero fmt s
    | none => r

/-- NaN operands take precedence over the numeric computation. -/
def nanOrElse {fmt : Format} (operands : List (Bits fmt)) (numeric : Bits fmt) : Bits fmt :=
  if operands.any Bits.isNaN then p.pickNaN operands else numeric

/-- A binary arithmetic operation. -/
def binary (fmt : Format) (op : ArithOp) (mode : RoundingMode) (x y : Bits fmt) :
    Outcome (Bits fmt) :=
  let x' := p.flushInput x
  let y' := p.flushInput y
  let o := op.outcome x'.datum y'.datum
  { value := p.nanOrElse [x', y'] (p.finish fmt mode (op.core x'.value y'.value) o)
    flags := o.flags (p.stage fmt mode)
    subnormalOperand := x.isSubnormal || y.isSubnormal }

/-- Addition (IEEE 754-2019 §5.4.1). -/
def add (fmt : Format) := p.binary fmt .add
/-- Subtraction (IEEE 754-2019 §5.4.1). -/
def sub (fmt : Format) := p.binary fmt .sub
/-- Multiplication (IEEE 754-2019 §5.4.1). -/
def mul (fmt : Format) := p.binary fmt .mul
/-- Division (IEEE 754-2019 §5.4.1). -/
def div (fmt : Format) := p.binary fmt .div

/-- Square root (IEEE 754-2019 §5.4.1). -/
def sqrt (fmt : Format) (mode : RoundingMode) (x : Bits fmt) : Outcome (Bits fmt) :=
  let x' := p.flushInput x
  let o := FlagSpec.sqrtOutcome x'.datum
  { value := p.nanOrElse [x'] (p.finish fmt mode (.sqrt x'.value) o)
    flags := o.flags (p.stage fmt mode)
    subnormalOperand := x.isSubnormal }

/-- Operands of `a * b + c` in the order a rule examines them. -/
def FmaNaNRule.order {fmt : Format} (rule : FmaNaNRule) (a b c : Bits fmt) : List (Bits fmt) :=
  rule.priority.map fun
    | .multiplicand1 => a
    | .multiplicand2 => b
    | .addend => c

/-- Fused multiply-add `a * b + c` with one rounding (IEEE 754-2019 §5.4.1), with
the per-instruction NaN rule. The rule's `infZeroQuietNaNInvalid` is the
exception specification's `FmaQuietAddend` policy (`FmaNaNRule.quietAddend`). -/
def fmaWith (fmt : Format) (rule : FmaNaNRule) (mode : RoundingMode)
    (a b c : Bits fmt) : Outcome (Bits fmt) :=
  let a' := p.flushInput a
  let b' := p.flushInput b
  let c' := p.flushInput c
  let infZero := (a'.isInfinite && b'.isZero) || (a'.isZero && b'.isInfinite)
  let special := infZero && c'.isQuietNaN
  let o := FlagSpec.fmaOutcome rule.quietAddend a'.datum b'.datum c'.datum
  { value :=
      if a'.isNaN || b'.isNaN || c'.isNaN then
        (if special && rule.infZeroQuietNaNIsDefault then p.defaultNaN fmt
          else p.pickNaN (FmaNaNRule.order rule a' b' c'))
      else p.finish fmt mode (.fma a'.value b'.value c'.value) o
    flags := o.flags (p.stage fmt mode)
    subnormalOperand := a.isSubnormal || b.isSubnormal || c.isSubnormal }

/-- IEEE ordered equality of non-NaN encodings (either zero equals the other). -/
def numericEq {fmt : Format} (x y : Bits fmt) : Bool := x.value.compare y.value == some .eq

/-- IEEE ordered less-than. False when either operand is a NaN. -/
def numericLt {fmt : Format} (x y : Bits fmt) : Bool := x.value.compare y.value == some .lt

/-- Minimum or maximum of two non-NaN encodings, ordering `-0 < +0`. The equal
case mirrors `Ieee754.F32.minimum`/`maximum`: of two equal operands, minimum
returns the first when it is negative and maximum returns the first when it is
positive. -/
def numericMinMax {fmt : Format} (isMax : Bool) (x y : Bits fmt) : Bits fmt :=
  if numericEq x y then (if x.signBit == isMax then y else x)
  else if numericLt x y != isMax then x else y

/-- Minimum (`isMax = false`) or maximum (`isMax = true`) under an explicit rule. -/
def minMaxWith {fmt : Format} (rule : MinMaxRule) (isMax : Bool) (x y : Bits fmt) :
    Outcome (Bits fmt) :=
  let x' := p.flushInput x
  let y' := p.flushInput y
  let anySignaling := x'.isSignalingNaN || y'.isSignalingNaN
  let value : Bits fmt :=
    match rule with
    | .x86 => if (if isMax then numericLt y' x' else numericLt x' y') then x' else y'
    | .minimum => p.nanOrElse [x', y'] (numericMinMax isMax x' y')
    | .minimumNumber =>
      if x'.isNaN && y'.isNaN then p.pickNaN [x', y']
        else if x'.isNaN then y'
        else if y'.isNaN then x'
        else numericMinMax isMax x' y'
    | .minNum =>
      if anySignaling || (x'.isNaN && y'.isNaN) then p.pickNaN [x', y']
        else if x'.isNaN then y'
        else if y'.isNaN then x'
        else numericMinMax isMax x' y'
  { value
    flags := rule.flags x'.datum y'.datum
    subnormalOperand := x.isSubnormal || y.isSubnormal }

/-- The architecture's base minimum/maximum instruction. -/
def minMaxBase {fmt : Format} (isMax : Bool) (x y : Bits fmt) : Outcome (Bits fmt) :=
  p.minMaxWith p.minMax isMax x y

/-- IEEE comparison (IEEE 754-2019 §5.11): `none` is unordered. A signaling
comparison signals invalid for any NaN operand; a quiet one only for signaling
NaNs (`FlagSpec.compare`). -/
def compare {fmt : Format} (signaling : Bool) (x y : Bits fmt) : Outcome (Option Ordering) :=
  let x' := p.flushInput x
  let y' := p.flushInput y
  { value := x'.value.compare y'.value
    flags := FlagSpec.compare signaling x'.datum y'.datum
    subnormalOperand := x.isSubnormal || y.isSubnormal }

/-- Round to an integral value in the given direction (IEEE 754-2019 §5.3.1).
`signalInexact` selects `roundToIntegralExact` (§5.9). Integral values are never
tiny, so no result flushing applies. -/
def roundToIntegral (fmt : Format) (mode : RoundingMode) (signalInexact : Bool) (x : Bits fmt) :
    Outcome (Bits fmt) :=
  let x' := p.flushInput x
  { value := p.nanOrElse [x'] (Rounding.integralRounded fmt mode x'.value)
    flags := FlagSpec.roundToIntegral mode signalInexact x'.datum
    subnormalOperand := x.isSubnormal }

/-- Format conversion (IEEE 754-2019 §5.4.2). A NaN operand yields the default
NaN under `NaNPropagation.defaultNaN` and otherwise `Bits.convertNaN`. -/
def convert (src dst : Format) (mode : RoundingMode) (x : Bits src) : Outcome (Bits dst) :=
  let x' := p.flushInput x
  let o := FlagSpec.convertOutcome x'.datum
  { value :=
      if x'.isNaN then
        (match p.propagation with
          | .defaultNaN => p.defaultNaN dst
          | _ => Bits.convertNaN src dst x')
      else p.finish dst mode (.convert x'.value) o
    flags := o.flags (p.stage dst mode)
    subnormalOperand := x.isSubnormal }

/-- The integer result of a NaN or out-of-range conversion. -/
def intOverflowResult (rule : IntOverflowRule) (target : IntFormat) (v : UnpackedFloat)
    (mode : RoundingMode) : BitVec target.width :=
  match rule with
  | .indefinite =>
    (Integer.ofIntWrapping target (match target.signedness with
      | .signed => target.minValue
      | .unsigned => target.maxValue)).bits
  | .saturateNaNToMax =>
    if v.isNaN then (Integer.ofIntWrapping target target.maxValue).bits
    else (Integer.fromFloatSaturating target v mode).bits
  | .saturateNaNToZero => (Integer.fromFloatSaturating target v mode).bits

/-- Float-to-integer conversion in the given direction (IEEE 754-2019 §5.8). An
in-range result is exact rounding; NaN and out-of-range operands yield
`intOverflowResult`. The flags are `FlagSpec.toInt`: invalid for NaN, infinite and
out-of-range operands, and inexact for an in-range inexact conversion when the
profile's conversions are `convertToIntegerExact…` operations. -/
def toInt (fmt : Format) (target : IntFormat) (mode : RoundingMode) (x : Bits fmt) :
    Outcome (BitVec target.width) :=
  let x' := p.flushInput x
  let v := x'.value
  { value :=
      match Integer.fromFloat? target v mode with
      | some n => n.bits
      | none => intOverflowResult p.intOverflow target v mode
    flags := FlagSpec.toInt target mode p.toIntSignalsInexact x'.datum
    subnormalOperand := x.isSubnormal }

/-- Integer-to-float conversion (IEEE 754-2019 §5.4.1 `convertFromInt`). Integers
are never tiny (`FlagSpec.not_isTiny_ofIntOutcome`), so no result flushing
applies. -/
def ofInt (fmt : Format) (mode : RoundingMode) (n : Int) : Outcome (Bits fmt) :=
  { value := Rounding.packRounded fmt mode (Rounding.ofInt n)
    flags := (FlagSpec.ofIntOutcome n).flags (p.stage fmt mode)
    subnormalOperand := false }

end Profile

/-- A comparison predicate: the result for each IEEE relation, and whether the
predicate signals invalid on quiet NaN operands. -/
structure Predicate where
  less : Bool
  equal : Bool
  greater : Bool
  unordered : Bool
  signaling : Bool
  deriving DecidableEq, Repr

namespace Predicate

/-- Evaluate on an IEEE comparison result. -/
def eval (P : Predicate) : Option Ordering → Bool
  | some .lt => P.less
  | some .eq => P.equal
  | some .gt => P.greater
  | none => P.unordered

/-- Quiet `==` (IEEE `compareQuietEqual`). -/
def eqQuiet : Predicate := ⟨false, true, false, false, false⟩
/-- Quiet `!=` (IEEE `compareQuietNotEqual`, true when unordered). -/
def neQuiet : Predicate := ⟨true, false, true, true, false⟩
/-- Signaling `<` (IEEE `compareSignalingLess`). -/
def ltSignaling : Predicate := ⟨true, false, false, false, true⟩
/-- Signaling `<=` (IEEE `compareSignalingLessEqual`). -/
def leSignaling : Predicate := ⟨true, true, false, false, true⟩
/-- Signaling `>`. -/
def gtSignaling : Predicate := ⟨false, false, true, false, true⟩
/-- Signaling `>=`. -/
def geSignaling : Predicate := ⟨false, true, true, false, true⟩

end Predicate

namespace Profile

/-- Evaluate a comparison predicate. -/
def comparePredicate (p : Profile) {fmt : Format} (P : Predicate) (x y : Bits fmt) : Outcome Bool :=
  let c := p.compare P.signaling x y
  { c with value := P.eval c.value }

end Profile

end Silmaril.Numeric.Float
