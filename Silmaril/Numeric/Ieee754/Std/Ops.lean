module

public import Silmaril.Numeric.Ieee754.Std.Format

/-!
# Exact semantics of the IEEE 754 operations

Each operation is given by its *exact* outcome (`Exact ℚ`) on value-level
operands, following IEEE 754-2019 §5.4 (arithmetic), §5.3.1 (remainder,
roundToIntegral), §5.4.2 and §5.8 (conversions), §6 (infinities, NaNs and
signed zeros) and §7.2 (invalid operation) and §7.3 (division by zero). The
delivered result is then `Deliver` (specification) or `deliverQ` (executable),
which are proved equivalent in `Std.Format`; so for every operation in this
file the executable result is *the* specified result (`*_spec` theorems).

NaN operands produce `.nan`, and a signaling NaN operand signals invalid
(§6.2). Which NaN bit pattern is delivered is decided by a NaN policy at the
bit level (`Std.NaN`). Square root, whose exact value is irrational, is in
`Std.Sqrt`.

Implementation-defined choices are explicit parameters:
* `FmaInfZeroQNaN`: whether `fma(∞, 0, qNaN)` signals invalid (§7.2(c)).
* `IntOverflowPolicy`: the integer delivered by an invalid float-to-integer
  conversion (§5.8 only requires invalid).
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

/-- An exact signed rational as an exact outcome; `zeroNeg` is the sign of an
exact zero. -/
def ofSigned (v : ℚ) (zeroNeg : Bool) : Exact ℚ :=
  if v = 0 then .num zeroNeg 0 else .num (decide (v < 0)) |v|

/-- NaN operands: the outcome when at least one operand is a NaN. -/
def nanOutcome (operands : List Datum) : Option (Exact ℚ) :=
  if operands.any Datum.isNaN then some (.nan (operands.any Datum.isSignaling)) else none

/-- The sign of an exact zero sum of operands with signs `a` and `b` (§6.3). -/
def sumZeroSign (mode : RoundingMode) (a b : Bool) : Bool :=
  if a = b then a else decide (mode = .towardNegative)

/-- Exact addition (§5.4.1, §6.1, §6.3, §7.2(b)). -/
def exactAdd (mode : RoundingMode) (x y : Datum) : Exact ℚ :=
  match nanOutcome [x, y] with
  | some e => e
  | none =>
    match x, y with
    | .inf a, .inf b => if a = b then .inf a false else .nan true
    | .inf a, _ => .inf a false
    | _, .inf b => .inf b false
    | .fin a m, .fin b n => ofSigned (signed a m + signed b n) (sumZeroSign mode a b)
    | _, _ => .nan false

/-- Exact subtraction: addition of the negation (§5.4.1). -/
def exactSub (mode : RoundingMode) (x y : Datum) : Exact ℚ :=
  match nanOutcome [x, y] with
  | some e => e
  | none => exactAdd mode x y.neg

/-- Exact multiplication (§5.4.1, §7.2(a)). -/
def exactMul (x y : Datum) : Exact ℚ :=
  match nanOutcome [x, y] with
  | some e => e
  | none =>
    match x, y with
    | .inf a, .inf b => .inf (a ^^ b) false
    | .inf a, .fin b n => if n = 0 then .nan true else .inf (a ^^ b) false
    | .fin a m, .inf b => if m = 0 then .nan true else .inf (a ^^ b) false
    | .fin a m, .fin b n => .num (a ^^ b) (m * n)
    | _, _ => .nan false

/-- Exact division (§5.4.1, §7.2(e), §7.3). -/
def exactDiv (x y : Datum) : Exact ℚ :=
  match nanOutcome [x, y] with
  | some e => e
  | none =>
    match x, y with
    | .inf _, .inf _ => .nan true
    | .inf a, .fin b _ => .inf (a ^^ b) false
    | .fin a _, .inf b => .num (a ^^ b) 0
    | .fin a m, .fin b n =>
      if n = 0 then (if m = 0 then .nan true else .inf (a ^^ b) true)
      else .num (a ^^ b) (m / n)
    | _, _ => .nan false

/-- Whether `fma(∞, 0, qNaN)` signals invalid (IEEE 754-2019 §7.2(c) leaves it
implementation-defined). SoftFloat and RISC-V signal it. -/
abbrev FmaInfZeroQNaN := Bool

/-- Exact fused multiply-add `x * y + z` (§5.4.1, §7.2(c)). -/
def exactFma (infZeroQNaN : FmaInfZeroQNaN) (mode : RoundingMode) (x y z : Datum) : Exact ℚ :=
  let infZero : Bool := match x, y with
    | .inf _, .fin _ n => decide (n = 0)
    | .fin _ m, .inf _ => decide (m = 0)
    | _, _ => false
  match nanOutcome [x, y] with
  | some _ => .nan (x.isSignaling || y.isSignaling || z.isSignaling)
  | none =>
    match nanOutcome [z] with
    | some (.nan s) => .nan (s || (infZero && infZeroQNaN))
    | some e => e
    | none =>
      if infZero then .nan true else
      match x, y, z with
      | .inf a, .inf b, .inf c => if (a ^^ b) = c then .inf c false else .nan true
      | .inf a, .fin b _, .inf c => if (a ^^ b) = c then .inf c false else .nan true
      | .fin a _, .inf b, .inf c => if (a ^^ b) = c then .inf c false else .nan true
      | .inf a, .inf b, _ => .inf (a ^^ b) false
      | .inf a, .fin b _, _ => .inf (a ^^ b) false
      | .fin a _, .inf b, _ => .inf (a ^^ b) false
      | .fin _ _, .fin _ _, .inf c => .inf c false
      | .fin a m, .fin b n, .fin c k =>
        ofSigned (signed (a ^^ b) (m * n) + signed c k) (sumZeroSign mode (a ^^ b) c)
      | _, _, _ => .nan false

/-- Integer magnitude rounding of a magnitude `x ≥ 0` of sign `neg`. -/
def roundIntMag (mode : RoundingMode) (neg : Bool) (x : ℚ) : ℕ :=
  if pick mode neg (⌊x⌋₊ % 2 = 0) x (⌊x⌋₊ : ℚ) (⌈x⌉₊ : ℚ) = ⌊x⌋₊ then ⌊x⌋₊ else ⌈x⌉₊

/-- Exact IEEE remainder `x - y * n`, `n` the integer nearest `x / y`, ties to
even (§5.3.1). An exact zero has the sign of `x`. -/
def exactRem (x y : Datum) : Exact ℚ :=
  match nanOutcome [x, y] with
  | some e => e
  | none =>
    match x, y with
    | .inf _, _ => .nan true
    | .fin a m, .inf _ => .num a m
    | .fin a m, .fin b n =>
      if n = 0 then .nan true else
      let q := signed a m / signed b n
      let k : ℤ := signed (decide (q < 0)) (roundIntMag .nearestTiesToEven (decide (q < 0)) |q|)
        |>.floor
      ofSigned (signed a m - signed b n * k) a
    | _, _ => .nan false

/-- Exact roundToIntegral in direction `dir` (§5.3.1, §5.9). The value is always
representable; `exactRoundToIntegral` returns the outcome together with whether
the result differs from the operand (raising inexact in the `Exact` variants). -/
def exactRoundToIntegral (dir : RoundingMode) (x : Datum) : Exact ℚ × Bool :=
  match nanOutcome [x] with
  | some e => (e, false)
  | none =>
    match x with
    | .inf a => (.inf a false, false)
    | .fin a m => let n := roundIntMag dir a m; (.num a n, decide ((n : ℚ) ≠ m))
    | _ => (.nan false, false)

/-- Exact conversion from another format: the operand's value (§5.4.2). -/
def exactConvert (x : Datum) : Exact ℚ :=
  match nanOutcome [x] with
  | some e => e
  | none =>
    match x with
    | .inf a => .inf a false
    | .fin a m => .num a m
    | _ => .nan false

/-- Exact conversion from an integer (§5.4.1 convertFromInt); zero is `+0`. -/
def exactOfInt (n : ℤ) : Exact ℚ := ofSigned n false

/-! ## Integer conversion -/

/-- An integer destination format: inclusive bounds. -/
structure IntFormat where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def IntFormat.signed (w : ℕ) : IntFormat := ⟨-(2 ^ (w - 1) : ℤ), 2 ^ (w - 1) - 1⟩
def IntFormat.unsigned (w : ℕ) : IntFormat := ⟨0, 2 ^ w - 1⟩

/-- Why a float-to-integer conversion is invalid. -/
inductive IntInvalid where
  | nan
  | posOverflow
  | negOverflow
  deriving DecidableEq, Repr

/-- Implementation-defined results of invalid float-to-integer conversions. -/
abbrev IntOverflowPolicy := IntFormat → IntInvalid → ℤ

/-- x86 "integer indefinite" (Intel SDM Vol. 2 CVTTSD2SI etc.): the most negative
signed value for signed targets; all ones for the AVX-512 unsigned targets. This
is SoftFloat's `8086-SSE` specialization. -/
def IntOverflowPolicy.x86Indefinite : IntOverflowPolicy := fun t _ =>
  if t.lo < 0 then t.lo else t.hi

/-- RISC-V `FCVT` (Unprivileged ISA, F extension, Table "domains of float-to-integer
conversion"): saturate, NaN gives the maximum. SoftFloat's `RISCV` specialization. -/
def IntOverflowPolicy.riscvSaturate : IntOverflowPolicy := fun t r =>
  match r with
  | .nan | .posOverflow => t.hi
  | .negOverflow => t.lo

/-- Saturate, NaN gives zero (Arm `FCVTZS`, WebAssembly `trunc_sat`). -/
def IntOverflowPolicy.saturateNaNZero : IntOverflowPolicy := fun t r =>
  match r with
  | .nan => 0
  | .posOverflow => t.hi
  | .negOverflow => t.lo

/-- Float-to-integer conversion in direction `dir`; `exact` selects the
`convertToIntegerExact` operations that raise inexact (§5.8). -/
def toInt (policy : IntOverflowPolicy) (t : IntFormat) (dir : RoundingMode) (exact : Bool)
    (x : Datum) : ℤ × Flags :=
  let invalid (r : IntInvalid) : ℤ × Flags := (policy t r, { invalidOperation := true })
  match x with
  | .nan _ => invalid .nan
  | .inf a => invalid (if a then .negOverflow else .posOverflow)
  | .fin a m =>
    let n : ℤ := signed a (roundIntMag dir a m) |>.floor
    if n < t.lo then invalid .negOverflow
    else if t.hi < n then invalid .posOverflow
    else (n, { inexact := exact && decide ((n : ℚ) ≠ signed a m) })

/-- The chaotic (least specified) float-to-integer semantics: on invalid
conversions any integer of the destination may result. -/
def ToIntChaos (t : IntFormat) (dir : RoundingMode) (exact : Bool) (x : Datum)
    (out : ℤ × Flags) : Prop :=
  ∃ policy : IntOverflowPolicy, (∀ r, t.lo ≤ policy t r ∧ policy t r ≤ t.hi) ∧
    out = toInt policy t dir exact x

/-! ## Comparisons (§5.11) -/

/-- Numeric value of a non-NaN datum, with infinities as `none`. -/
def Datum.compareValue : Datum → Datum → Option Ordering
  | .nan _, _ | _, .nan _ => none
  | .inf a, .inf b => some (if a = b then .eq else if a then .lt else .gt)
  | .inf a, .fin _ _ => some (if a then .lt else .gt)
  | .fin _ _, .inf b => some (if b then .gt else .lt)
  | .fin a m, .fin b n => some (compare (signed a m) (signed b n))

/-- Comparison result (`none` is unordered) and flags: quiet comparisons signal
invalid on signaling NaNs only, signaling comparisons on every NaN (§5.11). -/
def compareOp (signaling : Bool) (x y : Datum) : Option Ordering × Flags :=
  (x.compareValue y,
    { invalidOperation := x.isSignaling || y.isSignaling ||
        (signaling && (x.isNaN || y.isNaN)) })

end Silmaril.Numeric.Ieee754.Std
