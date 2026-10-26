module

/-!
# LPS IEEE-754 binary arithmetic with RISC-V exception flags

Hand translation of `theories/Riscv/Fpu.v` (LPS commit `f1006fe8`, MIT). Upstream marks this
file as part of its trusted specification.

`Sem` needs FP operations that return both a result and the five IEEE exception flags,
because in RISC-V the flags are architectural (they accrue into `fcsr[4:0]`).

## Where the rounding kernel comes from

Upstream builds on the Rocq standard library's `SpecFloat` (LGPL-2.1) and on Flocq's
`BinarySingleNaN` (LGPL-3). Neither is translated here. Their role is played by Lean core's
own IEEE model `Float.Model.UnpackedFloat` (Apache-2.0, `Init/Data/Float/Model`), which has
the same structure:

| upstream (SpecFloat / Flocq) | here (Lean core `Float.Model`) |
| --- | --- |
| `spec_float` | `UnpackedFloat` |
| `location` | `UnpackedFloat.Accuracy` |
| `shr_record`, `loc_of_shr_record`, `shr_record_of_loc` | `ExtendedMantissa`, `.accuracy`, `.ofMantissaAndAccuracy` |
| `fexp prec emax (digits + e)` | `Format.targetExponent (totalExponent m e)` |
| `shr_fexp`, `shr` | `shiftToTargetExponent`, `shiftToExponent` |
| `shl_align` | `decreaseExponent` |
| `SFdiv_core_binary`, `SFsqrt_core_binary`, `new_location` | `divCore`, `sqrtCore`, `accuracyOfFraction` |
| `SFcompare` | `UnpackedFloat.compare` |

The two cores choose the same intermediate exponents (`min (e₁ - e₂) (fexp …)`, and
`min (e / 2) (fexp ((digits + e + 1) / 2))`), and `compare` is the same exponent-then-mantissa
comparison of canonical data. Lean core rounds only to nearest-even, so the mode-dependent
rounding choice (Flocq's `choice_mode`) and the overflow result (Flocq's `binary_overflow`)
are written here from the IEEE 754 rules (`chooseMantissa`, `overflowResult`).

Upstream's lemma `round_aux_value` (the value half equals Flocq's `binary_round_aux`) has no
counterpart: its validation here is the upstream test table, ported in
`Silmaril.RiscV.LPS.FpuTests`.

Everything here is a computation on raw bit patterns of the format's width (32 or 64), as
natural numbers. Register width, NaN boxing and the `fcsr` update belong to `Sem`.
-/

@[expose] public section

namespace Silmaril.RiscV.LPS

open Float.Model
open Float.Model.UnpackedFloat (Accuracy ExtendedMantissa Sign)

/-! ## Formats (`format`, `fmt_single`, `fmt_double`) -/

/-- A binary format (`format`). Upstream pins `prec` (significand bits including the implicit
one) and `emax`; Lean's `Format` pins the field widths, from which both derive. -/
abbrev FpFormat := Float.Model.Format

/-- `fmt_single`. -/
abbrev fmtSingle : FpFormat := .binary32
/-- `fmt_double`. -/
abbrev fmtDouble : FpFormat := .binary64

namespace FpFormat

/-- `fp_prec`: significand bits including the implicit one. -/
def prec (f : FpFormat) : Nat := f.mantissaBits
/-- `fp_emax`: the exponent of the infinities. -/
def emax (f : FpFormat) : Int := 2 ^ (f.exponentBits - 1)
/-- `fp_mw`: width of the mantissa field. -/
def mw (f : FpFormat) : Nat := f.mantissaBitsWithoutImplicit
/-- `fp_ew`: width of the exponent field. -/
def ew (f : FpFormat) : Nat := f.exponentBits
/-- `fp_emin`: the exponent of the smallest subnormal. -/
def emin (f : FpFormat) : Int := f.minExponent

end FpFormat

/-! ## Exception flags (`fflags`) -/

/-- The five IEEE flags (`fflags`). -/
structure FFlags where
  /-- Invalid operation (`fl_nv`). -/
  nv : Bool
  /-- Divide by zero (`fl_dz`). -/
  dz : Bool
  /-- Overflow (`fl_of`). -/
  of : Bool
  /-- Underflow (`fl_uf`). -/
  uf : Bool
  /-- Inexact (`fl_nx`). -/
  nx : Bool
  deriving DecidableEq, Repr

/-- `no_flags`. -/
def noFlags : FFlags := ⟨false, false, false, false, false⟩
/-- `nv_flag`. -/
def nvFlag : FFlags := ⟨true, false, false, false, false⟩
/-- `dz_flag`. -/
def dzFlag : FFlags := ⟨false, true, false, false, false⟩
/-- `nx_flag`. -/
def nxFlag : FFlags := ⟨false, false, false, false, true⟩

/-- The `fcsr[4:0]` encoding of the flags (`fflags_bits`). -/
def FFlags.bits (fl : FFlags) : Nat :=
  let b (p : Bool) (i : Nat) := if p then 2 ^ i else 0
  b fl.nx 0 + b fl.uf 1 + b fl.of 2 + b fl.dz 3 + b fl.nv 4

/-! ## Rounding modes (`rmode`) -/

/-- The five architectural rounding modes (`rmode`). -/
inductive RMode where
  | rne | rtz | rdn | rup | rmm
  deriving DecidableEq, Repr

/-- `rmode_of_Z`. -/
def RMode.ofCode : Nat → Option RMode
  | 0 => some .rne
  | 1 => some .rtz
  | 2 => some .rdn
  | 3 => some .rup
  | 4 => some .rmm
  | _ => none

/-- `rmode_of_field`: `rm` is the instruction field, `frm` the `fcsr` rounding mode. A
reserved mode is `none`, an illegal instruction at the `Sem` level. -/
def RMode.ofField (rm frm : Nat) : Option RMode :=
  if rm = 7 then RMode.ofCode frm else RMode.ofCode rm

/-- The rounding choice for a magnitude `m` at accuracy `acc`, with the sign `s` of the
value (`true` for negative). This is the role of Flocq's `choice_mode`, written from the
IEEE 754 rounding-direction attributes. -/
def chooseMantissa (md : RMode) (s : Bool) (m : Nat) (acc : Accuracy) : Nat :=
  let inexact := match acc with | .exact => false | .inexact _ => true
  match md with
  | .rne => acc.roundToNearestEven m
  | .rtz => m
  | .rdn => if inexact && s then m + 1 else m
  | .rup => if inexact && !s then m + 1 else m
  | .rmm =>
    match acc with
    | .inexact .eq | .inexact .gt => m + 1
    | _ => m

/-- `Bool` sign (upstream) to Lean core's `Sign`. -/
def signOf (s : Bool) : Sign := if s then .negative else .positive

/-- The overflow result for a mode and sign: an infinity, or the largest finite value of
that sign (role of Flocq's `binary_overflow`, from IEEE 754 §7.4). -/
def overflowResult (f : FpFormat) (md : RMode) (s : Bool) : UnpackedFloat :=
  let toInf := match md with
    | .rne | .rmm => true
    | .rtz => false
    | .rup => !s
    | .rdn => s
  if toInf then .infinity (signOf s)
  else .finite (signOf s) (2 ^ f.prec - 1) (f.emax - f.prec) (by
    have : 1 < 2 ^ f.prec := Nat.one_lt_two_pow (by simp [FpFormat.prec, Format.mantissaBits])
    omega)

/-! ## Bit patterns -/

/-- `fp_sign_bit`. -/
def fpSignBit (f : FpFormat) (x : Nat) : Bool := x.testBit (f.mw + f.ew)
/-- `fp_exp_field`. -/
def fpExpField (f : FpFormat) (x : Nat) : Nat := (x >>> f.mw) % 2 ^ f.ew
/-- `fp_man_field`. -/
def fpManField (f : FpFormat) (x : Nat) : Nat := x % 2 ^ f.mw

/-- Decode the interchange format (`fp_decode`). -/
def fpDecode (f : FpFormat) (x : Nat) : UnpackedFloat :=
  let s := fpSignBit f x
  let e := fpExpField f x
  let m := fpManField f x
  if e = 0 then
    if h : m = 0 then .zero (signOf s) else .finite (signOf s) m f.emin (Nat.pos_of_ne_zero h)
  else if e = 2 ^ f.ew - 1 then
    if m = 0 then .infinity (signOf s) else .notANumber
  else
    .finite (signOf s) (2 ^ f.mw + m) (e + f.emin - 1) (by have := Nat.two_pow_pos f.mw; omega)

/-- The one NaN this semantics ever produces (`fp_canonical_nan`). -/
def fpCanonicalNan (f : FpFormat) : Nat := ((2 ^ f.ew - 1) <<< f.mw) + (1 <<< (f.mw - 1))

/-- Number of significant bits of a mantissa (`Zdigits2`; `Pos.size`). -/
def digits2 (m : Nat) : Nat := if m = 0 then 0 else m.log2 + 1

/-- Encode into the interchange format (`fp_encode`). -/
def fpEncode (f : FpFormat) (x : UnpackedFloat) : Nat :=
  let sb (s : Sign) : Nat := match s with | .negative => 1 <<< (f.mw + f.ew) | .positive => 0
  match x with
  | .notANumber => fpCanonicalNan f
  | .zero s => sb s
  | .infinity s => sb s + ((2 ^ f.ew - 1) <<< f.mw)
  | .finite s m e _ =>
    if digits2 m < f.prec then sb s + m -- subnormal
    else sb s + ((e - f.emin + 1).toNat <<< f.mw) + (m - 2 ^ f.mw)

/-- A signalling NaN: a NaN whose leading mantissa bit is clear (`fp_is_snan`). -/
def fpIsSnan (f : FpFormat) (x : Nat) : Bool :=
  fpExpField f x == 2 ^ f.ew - 1 && fpManField f x != 0 && !x.testBit (f.mw - 1)

/-- `fp_is_nan`. -/
def fpIsNan (f : FpFormat) (x : Nat) : Bool :=
  fpExpField f x == 2 ^ f.ew - 1 && fpManField f x != 0

/-- Flip the sign bit (`fp_neg`): not an arithmetic negation. -/
def fpNeg (f : FpFormat) (x : Nat) : Nat := x ^^^ (1 <<< (f.mw + f.ew))

/-! ## The rounding kernel, with flags -/

/-- `mk_round_flags`. -/
def mkRoundFlags (of_ uf nx : Bool) : FFlags := ⟨false, false, of_, uf, nx⟩

/-- Tininess detected after rounding: round the same intermediate to `prec` bits as though
the exponent range were unbounded, and test whether the magnitude stays below the smallest
normal (`round_tiny`). -/
def roundTiny (f : FpFormat) (md : RMode) (sx : Bool) (mx : Nat) (ex : Int)
    (lx : Accuracy) : Bool :=
  let (mrs, e') :=
    UnpackedFloat.shiftToExponent mx ex lx (ex + ((digits2 mx : Int) - f.prec))
  let m' := chooseMantissa md sx mrs.mantissa mrs.accuracy
  decide ((digits2 m' : Int) + e' ≤ f.emin + f.prec - 1)

/-- The flag-carrying rounding kernel (`round_aux`). -/
def roundAux (f : FpFormat) (md : RMode) (sx : Bool) (mx : Nat) (ex : Int)
    (lx : Accuracy) : UnpackedFloat × FFlags :=
  let (mrs1, e1) := UnpackedFloat.shiftToTargetExponent f mx ex lx
  let l1 := mrs1.accuracy
  let nx := match l1 with | .exact => false | .inexact _ => true
  let (mrs2, e2) :=
    UnpackedFloat.shiftToTargetExponent f (chooseMantissa md sx mrs1.mantissa l1) e1 .exact
  if h : mrs2.mantissa = 0 then (.zero (signOf sx), mkRoundFlags false nx nx)
  else if e2 ≤ f.emax - f.prec then
    (.finite (signOf sx) mrs2.mantissa e2 (Nat.pos_of_ne_zero h),
      mkRoundFlags false (nx && roundTiny f md sx mx ex lx) nx)
  else (overflowResult f md sx, mkRoundFlags true false true)

/-- Round an exact operand, left-aligning it to the canonical exponent first
(`round_exact`). -/
def roundExact (f : FpFormat) (md : RMode) (sx : Bool) (mx : Nat) (ex : Int) :
    UnpackedFloat × FFlags :=
  let (mz, ez) :=
    UnpackedFloat.decreaseExponent mx ex (f.targetExponent (totalExponent mx ex))
  roundAux f md sx mz ez .exact

/-! ## Exact operands as scaled integers -/

/-- `sf_sign`. -/
def sfSign : UnpackedFloat → Bool
  | .zero s | .infinity s | .finite s .. => s == .negative
  | .notANumber => false

/-- `sf_scaled`: a finite datum as (signed mantissa, exponent); everything else is `(0, 0)`. -/
def sfScaled : UnpackedFloat → Int × Int
  | .finite s m e _ => (if s == .negative then -(m : Int) else m, e)
  | _ => (0, 0)

/-- `scaled_add`. -/
def scaledAdd (a b : Int × Int) : Int × Int :=
  let e := min a.2 b.2
  (a.1 * 2 ^ (a.2 - e).toNat + b.1 * 2 ^ (b.2 - e).toNat, e)

/-- The sign of an exactly zero sum (`zero_sign`). -/
def zeroSign (md : RMode) (sa sb : Bool) : Bool :=
  if sa == sb then sa else md == .rdn

/-- Round an exact scaled integer, `szero` giving the sign of a zero result
(`round_scaled`). -/
def roundScaled (f : FpFormat) (md : RMode) (szero : Bool) (v : Int × Int) :
    UnpackedFloat × FFlags :=
  let (m, e) := v
  if m = 0 then (.zero (signOf szero), noFlags)
  else if 0 < m then roundExact f md false m.toNat e
  else roundExact f md true (-m).toNat e

/-! ## NaN pre-pass -/

/-- `nan_pass1`. -/
def nanPass1 (f : FpFormat) (a : Nat) : Option (Nat × FFlags) :=
  if fpIsNan f a then some (fpCanonicalNan f, if fpIsSnan f a then nvFlag else noFlags)
  else none

/-- `nan_pass2`. -/
def nanPass2 (f : FpFormat) (a b : Nat) : Option (Nat × FFlags) :=
  if fpIsNan f a || fpIsNan f b then
    some (fpCanonicalNan f, if fpIsSnan f a || fpIsSnan f b then nvFlag else noFlags)
  else none

/-- `nan_pass3`. -/
def nanPass3 (f : FpFormat) (a b c : Nat) : Option (Nat × FFlags) :=
  if fpIsNan f a || fpIsNan f b || fpIsNan f c then
    some (fpCanonicalNan f,
      if fpIsSnan f a || fpIsSnan f b || fpIsSnan f c then nvFlag else noFlags)
  else none

/-- `enc`. -/
def enc (f : FpFormat) (r : UnpackedFloat × FFlags) : Nat × FFlags := (fpEncode f r.1, r.2)

/-! ## Addition, subtraction, multiplication, division, square root -/

/-- `fp_add`. -/
def fpAdd (f : FpFormat) (md : RMode) (a b : Nat) : Nat × FFlags :=
  match nanPass2 f a b with
  | some r => r
  | none =>
    let x := fpDecode f a
    let y := fpDecode f b
    match x, y with
    | .infinity sa, .infinity sb =>
      if sa == sb then (fpEncode f (.infinity sa), noFlags)
      else (fpCanonicalNan f, nvFlag) -- inf - inf
    | .infinity sa, _ => (fpEncode f (.infinity sa), noFlags)
    | _, .infinity sb => (fpEncode f (.infinity sb), noFlags)
    | _, _ =>
      enc f (roundScaled f md (zeroSign md (sfSign x) (sfSign y))
        (scaledAdd (sfScaled x) (sfScaled y)))

/-- Subtraction is addition of the sign-flipped operand (`fp_sub`). -/
def fpSub (f : FpFormat) (md : RMode) (a b : Nat) : Nat × FFlags := fpAdd f md a (fpNeg f b)

/-- Sign of a product or quotient of two upstream signs. -/
def xorSign (s : Sign) (b : Bool) : Sign := signOf ((s == .negative) ^^ b)

/-- `fp_mul`. -/
def fpMul (f : FpFormat) (md : RMode) (a b : Nat) : Nat × FFlags :=
  match nanPass2 f a b with
  | some r => r
  | none =>
    match fpDecode f a, fpDecode f b with
    | .infinity _, .zero _ | .zero _, .infinity _ => (fpCanonicalNan f, nvFlag) -- 0 × inf
    | .infinity sa, y => (fpEncode f (.infinity (xorSign sa (sfSign y))), noFlags)
    | x, .infinity sb => (fpEncode f (.infinity (xorSign sb (sfSign x))), noFlags)
    | .zero sa, y => (fpEncode f (.zero (xorSign sa (sfSign y))), noFlags)
    | x, .zero sb => (fpEncode f (.zero (xorSign sb (sfSign x))), noFlags)
    | .finite sa ma ea _, .finite sb mb eb _ =>
      enc f (roundExact f md ((sa == .negative) ^^ (sb == .negative)) (ma * mb) (ea + eb))
    | _, _ => (fpCanonicalNan f, noFlags) -- unreachable: NaNs handled above

/-- `fp_div`. -/
def fpDiv (f : FpFormat) (md : RMode) (a b : Nat) : Nat × FFlags :=
  match nanPass2 f a b with
  | some r => r
  | none =>
    match fpDecode f a, fpDecode f b with
    | .infinity _, .infinity _ => (fpCanonicalNan f, nvFlag)
    | .zero _, .zero _ => (fpCanonicalNan f, nvFlag)
    | .infinity sa, y => (fpEncode f (.infinity (xorSign sa (sfSign y))), noFlags)
    | x, .infinity sb => (fpEncode f (.zero (xorSign sb (sfSign x))), noFlags)
    | .zero sa, y => (fpEncode f (.zero (xorSign sa (sfSign y))), noFlags)
    -- finite nonzero / zero: the only divide-by-zero there is
    | x, .zero sb => (fpEncode f (.infinity (xorSign sb (sfSign x))), dzFlag)
    | .finite sa ma ea _, .finite sb mb eb _ =>
      let (mz, ez, lz) := UnpackedFloat.divCore f ma ea mb eb
      enc f (roundAux f md ((sa == .negative) ^^ (sb == .negative)) mz ez lz)
    | _, _ => (fpCanonicalNan f, noFlags) -- unreachable

/-- `fp_sqrt`; `sqrt(-0) = -0`. -/
def fpSqrt (f : FpFormat) (md : RMode) (a : Nat) : Nat × FFlags :=
  match nanPass1 f a with
  | some r => r
  | none =>
    match fpDecode f a with
    | .zero s => (fpEncode f (.zero s), noFlags)
    | .infinity .positive => (fpEncode f (.infinity .positive), noFlags)
    | .infinity .negative => (fpCanonicalNan f, nvFlag)
    | .finite .negative .. => (fpCanonicalNan f, nvFlag)
    | .finite .positive m e _ =>
      let (mz, ez, lz) := UnpackedFloat.sqrtCore f m e
      enc f (roundAux f md false mz ez lz)
    | .notANumber => (fpCanonicalNan f, noFlags) -- unreachable

/-! ## Fused multiply-add (`fp_fma`)

The product is not rounded before the addend is applied: the exact product and the addend
are summed as scaled integers and rounded once. An invalid product (`0 × inf`) raises NV
even when the addend is a quiet NaN. -/

/-- `fp_fma`. -/
def fpFma (f : FpFormat) (md : RMode) (a b c : Nat) : Nat × FFlags :=
  let x := fpDecode f a
  let y := fpDecode f b
  let prodInvalid :=
    match x, y with
    | .infinity _, .zero _ | .zero _, .infinity _ => true
    | _, _ => false
  if prodInvalid && !(fpIsNan f a || fpIsNan f b) then (fpCanonicalNan f, nvFlag)
  else
  match nanPass3 f a b c with
  | some r => r
  | none =>
    let z := fpDecode f c
    let sp := sfSign x ^^ sfSign y
    match x, y with
    -- An infinite product: the addend can only make it invalid.
    | .infinity _, _ | _, .infinity _ =>
      match z with
      | .infinity sz =>
        if sp == (sz == .negative) then (fpEncode f (.infinity (signOf sp)), noFlags)
        else (fpCanonicalNan f, nvFlag)
      | _ => (fpEncode f (.infinity (signOf sp)), noFlags)
    | .finite _ ma ea _, .finite _ mb eb _ =>
      -- A finite product plus an infinite addend is that infinity.
      match z with
      | .infinity sz => (fpEncode f (.infinity sz), noFlags)
      | _ =>
        let prod : Int × Int := (if sp then -((ma * mb : Nat) : Int) else (ma * mb : Nat), ea + eb)
        enc f (roundScaled f md (zeroSign md sp (sfSign z)) (scaledAdd prod (sfScaled z)))
    -- A zero product: the sum is the addend, but the zero sign follows the product's sign
    -- when the addend is zero too.
    | _, _ =>
      match z with
      | .infinity sz => (fpEncode f (.infinity sz), noFlags)
      | _ => enc f (roundScaled f md (zeroSign md sp (sfSign z)) (sfScaled z))

/-! ## Comparisons, min/max, classification -/

/-- `none` is "unordered", i.e. a NaN operand (`fp_compare`). -/
def fpCompare (f : FpFormat) (a b : Nat) : Option Ordering :=
  (fpDecode f a).compare (fpDecode f b)

/-- feq is quiet: only a signalling NaN raises NV (`fp_eq`). -/
def fpEq (f : FpFormat) (a b : Nat) : Bool × FFlags :=
  (fpCompare f a b == some .eq, if fpIsSnan f a || fpIsSnan f b then nvFlag else noFlags)

/-- flt is signalling: any NaN raises NV (`fp_lt`). -/
def fpLt (f : FpFormat) (a b : Nat) : Bool × FFlags :=
  (fpCompare f a b == some .lt, if fpIsNan f a || fpIsNan f b then nvFlag else noFlags)

/-- fle is signalling (`fp_le`). -/
def fpLe (f : FpFormat) (a b : Nat) : Bool × FFlags :=
  (fpCompare f a b == some .lt || fpCompare f a b == some .eq,
    if fpIsNan f a || fpIsNan f b then nvFlag else noFlags)

/-- fmin/fmax (`fp_minmax`): one NaN operand yields the other operand, NV only for a
signalling NaN, and `-0 < +0`. -/
def fpMinMax (f : FpFormat) (isMax : Bool) (a b : Nat) : Nat × FFlags :=
  let fl := if fpIsSnan f a || fpIsSnan f b then nvFlag else noFlags
  if fpIsNan f a && fpIsNan f b then (fpCanonicalNan f, fl)
  else if fpIsNan f a then (b, fl)
  else if fpIsNan f b then (a, fl)
  else
    let aLtB :=
      match fpCompare f a b with
      | some .lt => true
      | some .eq => fpSignBit f a && !fpSignBit f b
      | _ => false
    (if isMax ^^ aLtB then a else b, fl)

/-- The fclass bit mask (`fp_class`): bit 0 -inf, 1 -normal, 2 -subnormal, 3 -0, 4 +0,
5 +subnormal, 6 +normal, 7 +inf, 8 sNaN, 9 qNaN. -/
def fpClass (f : FpFormat) (a : Nat) : Nat :=
  let s := fpSignBit f a
  let e := fpExpField f a
  let m := fpManField f a
  if e = 2 ^ f.ew - 1 then
    if m = 0 then (if s then 1 else 2 ^ 7)
    else if fpIsSnan f a then 2 ^ 8 else 2 ^ 9
  else if e = 0 then
    if m = 0 then (if s then 2 ^ 3 else 2 ^ 4)
    else if s then 2 ^ 2 else 2 ^ 5
  else if s then 2 ^ 1 else 2 ^ 6

/-! ## Conversions -/

/-- `int_lo`. -/
def intLo (signed : Bool) (bits : Nat) : Int := if signed then -(2 ^ (bits - 1) : Int) else 0
/-- `int_hi`. -/
def intHi (signed : Bool) (bits : Nat) : Int :=
  if signed then 2 ^ (bits - 1) - 1 else 2 ^ bits - 1
/-- Two's-complement image of `v` in `bits` bits (`int_wrap`, `Z.land v (Z.ones bits)`). -/
def intWrap (bits : Nat) (v : Int) : Nat := (v % 2 ^ bits).toNat

/-- float → integer, saturating (`fp_to_int`). The answer is the raw two's-complement value
in `bits` bits. A NaN gives the maximum in both signednesses; NV suppresses NX. -/
def fpToInt (f : FpFormat) (md : RMode) (signed : Bool) (bits : Nat) (a : Nat) :
    Nat × FFlags :=
  let sat (v : Int) : Nat × FFlags := (intWrap bits v, nvFlag)
  if fpIsNan f a then sat (intHi signed bits)
  else
    match fpDecode f a with
    | .infinity s => sat (if s == .negative then intLo signed bits else intHi signed bits)
    | .zero _ => (0, noFlags)
    | .notANumber => sat (intHi signed bits) -- unreachable
    | .finite sg m e _ =>
      let s := sg == .negative
      let (q, l) : Nat × Accuracy :=
        if 0 ≤ e then (m <<< e.toNat, .exact)
        else
          let d := 2 ^ (-e).toNat
          (m / d, UnpackedFloat.accuracyOfFraction (m % d) d)
      let q' := chooseMantissa md s q l
      let v : Int := if s then -(q' : Int) else q'
      if v < intLo signed bits || intHi signed bits < v then
        sat (if s then intLo signed bits else intHi signed bits)
      else (intWrap bits v, match l with | .exact => noFlags | .inexact _ => nxFlag)

/-- integer → float (`fp_of_int`); `v` is the raw `bits`-wide source value. -/
def fpOfInt (f : FpFormat) (md : RMode) (signed : Bool) (bits : Nat) (v : Nat) :
    Nat × FFlags :=
  let u := v % 2 ^ bits
  let n : Int := if signed && u.testBit (bits - 1) then (u : Int) - 2 ^ bits else u
  enc f (roundScaled f md false (n, 0))

/-- float → float (`fp_convert`): a NaN converts to the destination's canonical NaN, and a
signalling one raises NV. -/
def fpConvert (src dst : FpFormat) (md : RMode) (a : Nat) : Nat × FFlags :=
  if fpIsNan src a then (fpCanonicalNan dst, if fpIsSnan src a then nvFlag else noFlags)
  else
    match fpDecode src a with
    | .zero s => (fpEncode dst (.zero s), noFlags)
    | .infinity s => (fpEncode dst (.infinity s), noFlags)
    | .notANumber => (fpCanonicalNan dst, noFlags) -- unreachable
    | .finite s m e _ => enc dst (roundExact dst md (s == .negative) m e)

end Silmaril.RiscV.LPS
