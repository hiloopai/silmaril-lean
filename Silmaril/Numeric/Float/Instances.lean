module

public import Silmaril.Numeric.Float.Ops

/-!
# x86 SSE, RISC-V F/D and AArch64 profiles

Each profile is transcribed from an architecture manual; every field cites the
section it comes from. These are specifications from documents: nothing here has
been compared against hardware execution.

Sources:

* Intel 64 and IA-32 Architectures Software Developer's Manual (SDM), Vol. 1
  (§4.8 real numbers and NaNs, §4.9 floating-point exceptions, §10.2.3 MXCSR) and
  Vol. 2 (instruction pages).
* The RISC-V Instruction Set Manual, Volume I: Unprivileged ISA, version 20191213,
  Chapter 11 "F" (§11.2 FCSR, §11.3 NaN generation and propagation, §11.4
  subnormal arithmetic, §11.6 computational instructions, §11.7 conversions,
  §11.8 comparisons) and Chapter 12 "D". Later manual versions renumber these
  sections without changing the rules cited here.
* Arm Architecture Reference Manual for A-profile (DDI 0487), shared pseudocode
  functions `FPUnpackBase`, `FPRoundBase`, `FPProcessNaN`, `FPProcessNaNs`,
  `FPProcessNaNs3`, `FPDefaultNaN`, `FPMulAdd`, `FPMin`, `FPMinNum`, `FPToFixed`,
  `FPCompare`, with FPCR.AH = 0 and FPCR.FIZ = 0 (the reset behaviour without
  FEAT_AFP). Half-precision controls (FPCR.FZ16) are out of scope.

Exception traps are outside the model: every profile describes masked (x86) or
non-trapping (RISC-V, AArch64 with trap enables clear) behaviour, which is what
the flag outcomes report.
-/

@[expose] public section

namespace Silmaril.Numeric.Float

open Silmaril.Numeric.Ieee754

/-- The underflow and inexact flags. -/
def underflowInexact : Flags := { underflow := true, inexact := true }

/-- The underflow flag alone. -/
def underflowOnly : Flags := { underflow := true }

/-! ## x86 SSE -/

/-- The MXCSR control fields that affect results (SDM Vol. 1 §10.2.3, Figure 10-3).
`Profile.x86SSE` reads DAZ and FZ; `rounding` is the dynamic direction, which the
instruction layer passes to each operation. -/
structure MXCSRControl where
  /-- MXCSR.DAZ, bit 6 (SDM Vol. 1 §10.2.3.4). -/
  denormalsAreZeros : Bool := false
  /-- MXCSR.FZ, bit 15 (SDM Vol. 1 §10.2.3.3). -/
  flushToZero : Bool := false
  /-- MXCSR.RC, bits 13–14 (SDM Vol. 1 §10.2.3.2). -/
  rounding : RoundingMode := .nearestTiesToEven
  deriving DecidableEq, Repr

/-- The RC field encoding (SDM Vol. 1 §4.8.4, Table 4-8): 00 nearest (even),
01 down (toward −∞), 10 up (toward +∞), 11 toward zero. -/
def x86RoundingControl (rc : BitVec 2) : RoundingMode :=
  if rc = 0#2 then .nearestTiesToEven
  else if rc = 1#2 then .towardNegative
  else if rc = 2#2 then .towardPositive
  else .towardZero

/-- Decode the result-affecting MXCSR fields. Flush-to-zero applies only while the
underflow exception is masked (SDM Vol. 1 §10.2.3.3), so `flushToZero` is FZ
(bit 15) and UM (bit 11) together; with UM clear the SDM ignores FZ and raises the
underflow exception instead. The profiles describe masked exceptions only, so the
unmasked case is left to the instruction layer (x86: `Silmaril.X86.Float`). -/
def MXCSRControl.ofBits (mxcsr : BitVec 32) : MXCSRControl where
  denormalsAreZeros := mxcsr.getLsbD 6
  flushToZero := mxcsr.getLsbD 15 && mxcsr.getLsbD 11
  rounding := x86RoundingControl (mxcsr.extractLsb' 13 2)

/-- x86 SSE/SSE2 scalar floating point (MINSS/MAXSS family, CVT* family, `UCOMIS`/
`COMIS`, `CMPSS`/`CMPSD`), for a given MXCSR configuration with exceptions masked.

With DAZ set, every operation sees the flushed operand. This reads SDM Vol. 1
§10.2.3.4 ("Denormals-Are-Zeros"), which speaks of denormal source operands in
general, as applying to every instruction; it is not confirmed on hardware.
Consequences: `MINSS` with a subnormal operand returns a zero; `CVT(T)SS2SI`/
`CVT(T)SD2SI` convert a subnormal operand to 0 without signaling precision; and
`ROUNDSS`/`ROUNDSD` return a zero without precision for a subnormal operand even
when rounding toward an infinity (`Tests.lean` records `ROUNDSS` of `2^-149`
toward +∞). The FMA3 NaN rules are not transcribed here: no
x86 `FmaNaNRule` is provided, and `Profile.fmaWith` takes the rule from the
instruction layer. -/
def Profile.x86SSE (c : MXCSRControl := {}) : Profile where
  -- SDM Vol. 1 §4.8.3.5 and Table 4-7: with one NaN source it is returned
  -- (an SNaN converted to a QNaN); with two NaN sources the first source operand.
  propagation := .firstNaN
  -- SDM Vol. 1 §4.8.3.7: the "QNaN floating-point indefinite" has sign 1 and only
  -- the quiet bit set (FFC00000H, FFF8000000000000H).
  defaultNaNNegative := true
  -- SDM Vol. 1 §10.2.3.4: DAZ converts denormal source operands to zeros of the
  -- same sign.
  flushInputs := c.denormalsAreZeros
  -- SDM Vol. 1 §10.2.3.3: FZ returns a zero with the sign of the true result on
  -- underflow and sets the precision and underflow flags. This model reads the
  -- "underflow condition" of §4.9.1.5 as a tiny result, so exact tiny results are
  -- flushed as well.
  flushResults := c.flushToZero
  flushFlags := underflowInexact
  -- SDM Vol. 1 §4.9.1.5: underflow is detected from "the result of rounding with
  -- unbounded exponent", that is, tininess after rounding.
  tininess := .afterRounding
  minMax := .x86
  -- SDM Vol. 2, `CVTSD2SI`/`CVTTSD2SI`: invalid, and the integer indefinite value.
  intOverflow := .indefinite
  -- SDM Vol. 2, `CVTSS2SI`/`CVTTSS2SI`/`CVTSD2SI`/`CVTTSD2SI`, "SIMD Floating-Point
  -- Exceptions: Invalid, Precision": an inexact in-range conversion sets PE.
  toIntSignalsInexact := true

/-- The comparison predicates of `CMPSS`/`CMPSD` and their VEX forms, indexed by
imm8 (SDM Vol. 2A, `CMPPD`, Table 3-1). Predicates 0–7 are the SSE encodings;
16–31 repeat 0–15 with the opposite signaling behaviour. -/
def x86ComparePredicate (imm : Fin 32) : Predicate :=
  let base : Nat → Predicate := fun
    | 0 => ⟨false, true, false, false, false⟩   -- EQ_OQ
    | 1 => ⟨true, false, false, false, true⟩    -- LT_OS
    | 2 => ⟨true, true, false, false, true⟩     -- LE_OS
    | 3 => ⟨false, false, false, true, false⟩   -- UNORD_Q
    | 4 => ⟨true, false, true, true, false⟩     -- NEQ_UQ
    | 5 => ⟨false, true, true, true, true⟩      -- NLT_US
    | 6 => ⟨false, false, true, true, true⟩     -- NLE_US
    | 7 => ⟨true, true, true, false, false⟩     -- ORD_Q
    | 8 => ⟨false, true, false, true, false⟩    -- EQ_UQ
    | 9 => ⟨true, false, false, true, true⟩     -- NGE_US
    | 10 => ⟨true, true, false, true, true⟩     -- NGT_US
    | 11 => ⟨false, false, false, false, false⟩ -- FALSE_OQ
    | 12 => ⟨true, false, true, false, false⟩   -- NEQ_OQ
    | 13 => ⟨false, true, true, false, true⟩    -- GE_OS
    | 14 => ⟨false, false, true, false, true⟩   -- GT_OS
    | _ => ⟨true, true, true, true, false⟩      -- 15: TRUE_UQ
  let P := base (imm.val % 16)
  if imm.val < 16 then P else { P with signaling := !P.signaling }

/-- EFLAGS (ZF, PF, CF) written by `COMIS*`/`UCOMIS*` (SDM Vol. 2A, `COMISS`):
unordered 111, greater 000, less 001, equal 100; OF, SF and AF are cleared.
`UCOMIS*` is a quiet comparison and `COMIS*` a signaling one (invalid also for
QNaN operands), i.e. `Profile.compare` with `signaling := false`/`true`. -/
def x86ComisFlags : Option Ordering → Bool × Bool × Bool
  | none => (true, true, true)
  | some .gt => (false, false, false)
  | some .lt => (false, false, true)
  | some .eq => (true, false, false)

/-- x86 `MINSS`/`MINSD`/`MAXSS`/`MAXSD` (SDM Vol. 2B instruction pages). -/
def x86MinMaxRule : MinMaxRule := .x86

/-! ## RISC-V F and D -/

/-- The `frm`/`rm` encoding (Unprivileged ISA §11.2, Table 11.1): 000 RNE, 001 RTZ,
010 RDN, 011 RUP, 100 RMM. 101 and 110 are reserved and 111 selects the dynamic
mode in an instruction's `rm` field; those yield `none`. -/
def riscvRoundingMode? (rm : BitVec 3) : Option RoundingMode :=
  if rm = 0#3 then some .nearestTiesToEven
  else if rm = 1#3 then some .towardZero
  else if rm = 2#3 then some .towardNegative
  else if rm = 3#3 then some .towardPositive
  else if rm = 4#3 then some .nearestTiesToAway
  else none

/-- The rounding selection of an instruction's `rm` field (§11.2, Table 11.1):
a static direction for 000–100, the dynamic `frm` for 111, and `none` for the
reserved values 101 and 110. -/
def riscvRoundingSelect? (rm : BitVec 3) : Option RoundingSelect :=
  if rm = 7#3 then some .dynamic else (riscvRoundingMode? rm).map .static

/-- RISC-V F/D. The rounding direction is not part of the profile: an instruction
whose `rm` field decodes to `riscvRoundingSelect? rm = some s` rounds in
`s.resolve frm`. -/
def Profile.riscvFD : Profile where
  -- §11.3: "if the result of a floating-point operation is NaN, it is the
  -- canonical NaN"; NaN payloads are not propagated.
  propagation := .defaultNaN
  -- §11.3: the canonical NaN has a positive sign (7FC00000H; D: 7FF8000000000000H).
  defaultNaNNegative := false
  -- §11.4: subnormals are handled per IEEE 754; there is no flush mode.
  flushInputs := false
  flushResults := false
  flushFlags := Flags.empty
  -- §11.4: "tininess is detected after rounding".
  tininess := .afterRounding
  -- §11.6: FMIN/FMAX are minimumNumber/maximumNumber (F version 2.2).
  minMax := .minimumNumber
  -- §11.7, the table "Domains of float-to-integer conversions and behavior for
  -- invalid inputs": out of range saturates, NaN converts to the maximum.
  intOverflow := .saturateNaNToMax
  -- §11.7: conversions set NX when the rounded result differs from the operand
  -- and NV is not set.
  toIntSignalsInexact := true

/-- RISC-V `FMIN`/`FMAX` (§11.6). -/
def riscvMinMaxRule : MinMaxRule := .minimumNumber

/-- RISC-V fused multiply-add NaN rule (§11.6): results are canonical NaNs, and
"the fused multiply-add instructions must set the invalid operation exception flag
when the multiplicands are ∞ and zero, even when the addend is a quiet NaN". -/
def riscvFmaNaNRule : FmaNaNRule where
  priority := [.multiplicand1, .multiplicand2, .addend]
  infZeroQuietNaNIsDefault := true
  infZeroQuietNaNInvalid := true

/-- `FEQ` is quiet; `FLT`/`FLE` are signaling (§11.8). -/
def riscvFeq : Predicate := Predicate.eqQuiet
def riscvFlt : Predicate := Predicate.ltSignaling
def riscvFle : Predicate := Predicate.leSignaling

/-! ## AArch64 -/

/-- The FPCR control fields that affect results. `Profile.aarch64` reads DN and FZ;
`rounding` is the dynamic direction, which the instruction layer passes to each
operation. -/
structure FPCRControl where
  /-- FPCR.DN, bit 25: default NaN mode. -/
  defaultNaN : Bool := false
  /-- FPCR.FZ, bit 24: flush-to-zero for single and double precision. -/
  flushToZero : Bool := false
  /-- FPCR.RMode, bits 23:22. -/
  rounding : RoundingMode := .nearestTiesToEven
  deriving DecidableEq, Repr

/-- FPCR.RMode encoding: 00 RN, 01 RP (toward +∞), 10 RM (toward −∞), 11 RZ. -/
def aarch64RoundingMode (rmode : BitVec 2) : RoundingMode :=
  if rmode = 0#2 then .nearestTiesToEven
  else if rmode = 1#2 then .towardPositive
  else if rmode = 2#2 then .towardNegative
  else .towardZero

/-- Decode the result-affecting FPCR fields (FPCR.AH and FPCR.FIZ are assumed 0). -/
def FPCRControl.ofBits (fpcr : BitVec 64) : FPCRControl where
  defaultNaN := fpcr.getLsbD 25
  flushToZero := fpcr.getLsbD 24
  rounding := aarch64RoundingMode (fpcr.extractLsb' 22 2)

/-- AArch64 scalar single/double precision for a given FPCR configuration. -/
def Profile.aarch64 (c : FPCRControl := {}) : Profile where
  -- `FPProcessNaNs`: op1 SNaN, op2 SNaN, op1 QNaN, op2 QNaN, each quieted by
  -- `FPProcessNaN`; with FPCR.DN = 1 `FPProcessNaN` returns `FPDefaultNaN`.
  propagation := if c.defaultNaN then .defaultNaN else .signalingFirst
  -- `FPDefaultNaN`: sign 0 (with FPCR.AH = 0), quiet bit only.
  defaultNaNNegative := false
  -- `FPUnpackBase`: with FPCR.FZ = 1 a denormal input is treated as a zero of the
  -- same sign (raising Input Denormal).
  flushInputs := c.flushToZero
  -- `FPRoundBase`: with FPCR.FZ = 1 and `exponent < minimum_exp` the result is
  -- `FPZero(sign)` and only Underflow is raised.
  flushResults := c.flushToZero
  flushFlags := underflowOnly
  -- `FPRoundBase`: "Underflow occurs if exponent is too small before rounding"
  -- (FPCR.AH = 0), and flushing tests the unrounded exponent.
  tininess := .beforeRounding
  -- `FMIN`/`FMAX` (`FPMin`/`FPMax`).
  minMax := .minimum
  -- `FPToFixed`: NaN yields 0, out-of-range saturates; both raise InvalidOp.
  intOverflow := .saturateNaNToZero
  -- `FPToFixed`: a nonzero rounding error raises Inexact.
  toIntSignalsInexact := true

/-- AArch64 `FMIN`/`FMAX` (`FPMin`/`FPMax`). -/
def aarch64FMinRule : MinMaxRule := .minimum

/-- AArch64 `FMINNM`/`FMAXNM` (`FPMinNum`/`FPMaxNum`). -/
def aarch64FMinNMRule : MinMaxRule := .minNum

/-- AArch64 `FMADD` NaN rule (`FPMulAdd`): `FPProcessNaNs3(typeA, type1, type2)`
examines the addend first; `(±∞ × ±0) + qNaN` yields the default NaN and raises
InvalidOp. -/
def aarch64FmaNaNRule : FmaNaNRule where
  priority := [.addend, .multiplicand1, .multiplicand2]
  infZeroQuietNaNIsDefault := true
  infZeroQuietNaNInvalid := true

/-- `FCMP` is quiet and `FCMPE` signaling; `FPCompare` writes NZCV as
0011 unordered, 0110 equal, 1000 less, 0010 greater. -/
def aarch64CompareNZCV : Option Ordering → BitVec 4
  | none => 0b0011#4
  | some .eq => 0b0110#4
  | some .lt => 0b1000#4
  | some .gt => 0b0010#4

end Silmaril.Numeric.Float
