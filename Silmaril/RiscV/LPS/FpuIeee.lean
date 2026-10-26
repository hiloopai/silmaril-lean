module

public import Silmaril.RiscV.LPS.Fpu
public import Silmaril.Numeric.Float.Instances
public import Silmaril.Numeric.Float.Ops

/-!
# RISC-V F/D over Silmaril's IEEE 754 model

`Silmaril.RiscV.LPS.Fpu` is the literal port of LPS's `Riscv/Fpu.v`: its own rounding
kernel (`roundAux`, `chooseMantissa`, `overflowResult`) over Lean core's `Float.Model`.
This module restates the same operations, with the same signatures (raw bit patterns of
the format's width as `Nat`, and `FFlags`), over Silmaril's own IEEE 754 formalization:

* values: `Silmaril.Numeric.Ieee754.Rounding` (all five IEEE rounding directions,
  gradual underflow, one rounding for FMA, directed overflow);
* flags: the exception specification `Silmaril.Numeric.Ieee754.Flags` (`FlagSpec`),
  computed from the *exact* result over `ℚ` (IEEE 754-2019 §§7.2–7.6), with
  tininess detected after rounding;
* RISC-V choices: `Profile.riscvFD` (canonical NaN, no flushing, saturating
  float-to-integer conversion with NaN to the maximum, FMIN/FMAX as IEEE 754-2019
  `minimumNumber`/`maximumNumber`, NX on inexact conversions), `riscvFmaNaNRule`
  (NV for `∞ × 0 + qNaN`) and the quiet/signalling comparison predicates
  `riscvFeq`, `riscvFlt`, `riscvFle`.

Nothing here is computed by the LPS kernel, so the agreement theorems and test tables
of `Silmaril.RiscV.LPS.FpuAgree` compare two independent implementations.

The seam for the IEEE 754 lane is `Silmaril.Numeric.Float.Profile`: every operation
below is one call into it. A different IEEE back end only has to provide the same
`Profile` operations.

Inputs are read modulo `2 ^ width` (`BitVec.ofNat`), as `Sem.fread` always supplies a
value of the format's width.
-/

@[expose] public section

namespace Silmaril.RiscV.LPS.Ieee

open Silmaril.Numeric Silmaril.Numeric.Float Silmaril.Numeric.Ieee754

/-- The IEEE rounding direction of a RISC-V rounding mode (Unprivileged ISA §11.2,
Table 11.1; IEEE 754-2019 §4.3). -/
def _root_.Silmaril.RiscV.LPS.RMode.toMode : RMode → RoundingMode
  | .rne => .nearestTiesToEven
  | .rtz => .towardZero
  | .rdn => .towardNegative
  | .rup => .towardPositive
  | .rmm => .nearestTiesToAway

/-- IEEE status flags as RISC-V `fflags` (NV, DZ, OF, UF, NX). -/
def ofFlags (fl : Flags) : FFlags :=
  ⟨fl.invalidOperation, fl.divisionByZero, fl.overflow, fl.underflow, fl.inexact⟩

/-- The RISC-V F/D profile. -/
abbrev rv : Profile := Profile.riscvFD

/-- A raw operand as an encoding of the format. -/
def enc (f : FpFormat) (a : Nat) : Bits f := BitVec.ofNat _ a

/-- A float-valued outcome as LPS's `(bits, fflags)`. -/
def out {f : FpFormat} (o : Outcome (Bits f)) : Nat × FFlags := (o.value.toNat, ofFlags o.flags)

/-- `fp_add` over Silmaril IEEE. -/
def fpAdd (f : FpFormat) (md : RMode) (a b : Nat) : Nat × FFlags :=
  out (rv.add f md.toMode (enc f a) (enc f b))

/-- `fp_sub` over Silmaril IEEE. -/
def fpSub (f : FpFormat) (md : RMode) (a b : Nat) : Nat × FFlags :=
  out (rv.sub f md.toMode (enc f a) (enc f b))

/-- `fp_mul` over Silmaril IEEE. -/
def fpMul (f : FpFormat) (md : RMode) (a b : Nat) : Nat × FFlags :=
  out (rv.mul f md.toMode (enc f a) (enc f b))

/-- `fp_div` over Silmaril IEEE. -/
def fpDiv (f : FpFormat) (md : RMode) (a b : Nat) : Nat × FFlags :=
  out (rv.div f md.toMode (enc f a) (enc f b))

/-- `fp_sqrt` over Silmaril IEEE. -/
def fpSqrt (f : FpFormat) (md : RMode) (a : Nat) : Nat × FFlags :=
  out (rv.sqrt f md.toMode (enc f a))

/-- `fp_fma` (`a * b + c`, one rounding) over Silmaril IEEE, with the RISC-V NaN rule. -/
def fpFma (f : FpFormat) (md : RMode) (a b c : Nat) : Nat × FFlags :=
  out (rv.fmaWith f riscvFmaNaNRule md.toMode (enc f a) (enc f b) (enc f c))

/-- A comparison predicate's outcome as LPS's `(bool, fflags)`. -/
def cmp (f : FpFormat) (P : Predicate) (a b : Nat) : Bool × FFlags :=
  let o := rv.comparePredicate P (enc f a) (enc f b)
  (o.value, ofFlags o.flags)

/-- `feq` (quiet). -/
def fpEq (f : FpFormat) (a b : Nat) : Bool × FFlags := cmp f riscvFeq a b
/-- `flt` (signalling). -/
def fpLt (f : FpFormat) (a b : Nat) : Bool × FFlags := cmp f riscvFlt a b
/-- `fle` (signalling). -/
def fpLe (f : FpFormat) (a b : Nat) : Bool × FFlags := cmp f riscvFle a b

/-- `fmin`/`fmax`: IEEE 754-2019 `minimumNumber`/`maximumNumber` (§9.6), the RISC-V F 2.2
semantics. -/
def fpMinMax (f : FpFormat) (isMax : Bool) (a b : Nat) : Nat × FFlags :=
  out (rv.minMaxBase isMax (enc f a) (enc f b))

/-- `fclass` from the IEEE classification of the encoding (Unprivileged ISA §11.9,
Table 11.5). -/
def fpClass (f : FpFormat) (a : Nat) : Nat :=
  let x := enc f a
  let neg := x.signBit
  if x.isSignalingNaN then 2 ^ 8
  else if x.isNaN then 2 ^ 9
  else if x.isInfinite then (if neg then 2 ^ 0 else 2 ^ 7)
  else if x.isZero then (if neg then 2 ^ 3 else 2 ^ 4)
  else if x.isSubnormal then (if neg then 2 ^ 2 else 2 ^ 5)
  else if neg then 2 ^ 1 else 2 ^ 6

/-- The integer format of a conversion. -/
def intFormat (signed : Bool) (bits : Nat) (h : 0 < bits) : IntFormat :=
  ⟨bits, if signed then .signed else .unsigned, h⟩

/-- float → integer, saturating, NaN to the maximum (`fcvt.{w,wu,l,lu}.{s,d}`). A width-0
target does not occur in RISC-V and answers `(0, noFlags)`. -/
def fpToInt (f : FpFormat) (md : RMode) (signed : Bool) (bits : Nat) (a : Nat) :
    Nat × FFlags :=
  if h : 0 < bits then
    let o := rv.toInt f (intFormat signed bits h) md.toMode (enc f a)
    (o.value.toNat, ofFlags o.flags)
  else (0, noFlags)

/-- The integer a `bits`-wide raw source denotes. -/
def intOfRaw (signed : Bool) (bits : Nat) (v : Nat) : Int :=
  let u := v % 2 ^ bits
  if signed && u.testBit (bits - 1) then (u : Int) - 2 ^ bits else u

/-- integer → float (`fcvt.{s,d}.{w,wu,l,lu}`). -/
def fpOfInt (f : FpFormat) (md : RMode) (signed : Bool) (bits : Nat) (v : Nat) :
    Nat × FFlags :=
  out (rv.ofInt f md.toMode (intOfRaw signed bits v))

/-- float → float (`fcvt.s.d`, `fcvt.d.s`). -/
def fpConvert (src dst : FpFormat) (md : RMode) (a : Nat) : Nat × FFlags :=
  out (rv.convert src dst md.toMode (enc src a))

end Silmaril.RiscV.LPS.Ieee
