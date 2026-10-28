module

public import Silmaril.X86.Float.State
public import Silmaril.X86.Float.Encoding
public import Silmaril.Process.Memory

/-!
# Semantics of the scalar SSE subset

A handwritten local model of the instructions of `Silmaril.X86.Float.Instr`,
written from the Intel SDM (Vol. 1, Chapters 10 and 11; Vol. 2, the instruction
pages). It is a specification from documents; nothing here is derived from, or
proved to correspond with, the Sail, ACL2 or any hardware description.

## Arithmetic comes from the shared profile

Every floating-point value, IEEE flag and subnormal-operand indication is an
operation of `Silmaril.Numeric.Float.Profile` applied to `MXCSR.profile`, which
is `Profile.x86SSE` for the MXCSR's DAZ, FZ and RC fields:

| Instruction | Profile operation |
| --- | --- |
| ADD/SUB/MUL/DIV SS/SD | `binary` |
| MIN/MAX SS/SD | `minMaxBase` (the x86 rule) |
| SQRTSS/SD | `sqrt` |
| CVTSI2SS/SD | `ofInt` |
| CVTTSS2SI/CVTTSD2SI | `toInt` toward zero |
| CVTSS2SI/CVTSD2SI | `toInt` in the MXCSR.RC direction |
| CVTSS2SD/CVTSD2SS | `convert` |
| UCOMIS/COMIS | `compare` (quiet / signaling) |
| CMPSS/CMPSD | `comparePredicate` with `x86ComparePredicate` |
| ROUNDSS/SD | `roundToIntegral`, with imm8[3] suppressing inexact |

The first source of a two-operand instruction is the destination's low lane,
as in the SDM operation sections (`DEST[31:0] ← DEST[31:0] + SRC[31:0]`).

## Destination merging

* Scalar arithmetic, SQRT, CVTSI2Sx, CVTSS2SD/CVTSD2SS, ROUNDSx, CMPSx and
  register-to-register MOVSS/MOVSD write the low lane and keep the rest of the
  destination (`setLane`).
* MOVSS/MOVSD loads zero bits 127:32 or 127:64 (`zeroLane`).
* MOVD/MOVQ into an XMM register zero bits 127:32 or 127:64 (SDM Vol. 2B,
  MOVD/MOVQ).
* MOVD/MOVQ, CVT(T)SS2SI and CVT(T)SD2SI with a 32-bit general-purpose
  destination zero bits 63:32 of that register (SDM Vol. 1, §3.4.1.1).
* ANDPS/ANDNPS/ORPS/XORPS (and the PD forms) and MOVAPS/MOVAPD act on all 128
  bits. Their memory forms require a 16-byte-aligned operand; a misaligned one
  raises #GP(0) (SDM Vol. 2A, ANDPS, "Exceptions": legacy SSE alignment).

## SIMD floating-point exceptions

`detect` turns a profile outcome into the six MXCSR conditions, split into
*pre-computation* exceptions (invalid, denormal operand, divide-by-zero) and
*post-computation* exceptions (overflow, underflow, precision) as in SDM Vol. 1,
§11.5.1 ("SIMD Floating-Point Exceptions") and the procedure of §11.5.3
("Generating SIMD Floating-Point Exceptions"). `signal` then applies the
handling rules of §11.5.3.1 ("Handling Masked Exceptions"), §11.5.3.2
("Handling Unmasked Exceptions") and §11.5.3.3 ("Handling Combinations of Masked
and Unmasked Exceptions"), with §4.9.2 ("Floating-Point Exception Priority"):
if a detected pre-computation exception is unmasked, the pre-computation flags
are recorded and #XM is raised without the post-computation step; otherwise, if
a post-computation exception is unmasked, all detected flags are recorded and #XM
is raised; otherwise the flags are OR-ed into MXCSR and the instruction commits.
Sections are cited by title as well as number because the titles are stable
across SDM revisions; the numbers were written from the SDM's Chapter 11 layout
and have not been checked against a pinned SDM revision (no copy of the manual
was available when this was written). A faulting instruction writes no
register, memory or RFLAGS; the fault carries the MXCSR with the recorded
flags, which is what the handler observes. The model assumes CR4.OSXMMEXCPT = 1;
with it clear the processor raises #UD instead (SDM Vol. 3A, §2.5).

The denormal-operand condition (DE) is not an IEEE flag, so it is derived here
from the profile's `subnormalOperand` through the shared precedence rule
`Outcome.denormalAfterPriority` (`Silmaril.Numeric.Float.Exceptions`), per this
reading of the SDM:

* only instructions whose SDM page lists "Denormal" check it (arithmetic, MIN/MAX,
  SQRT, CVTSS2SD/CVTSD2SS, COMIS/UCOMIS, CMP); ROUNDSx, CVT*2SI and CVTSI2Sx do
  not;
* with DAZ set, DE is never signaled (Vol. 1, §10.2.3.4 "Denormals-Are-Zeros":
  denormal sources are converted to zero and the denormal-operand exception is
  not reported). The profile applies DAZ to every instruction, so it also
  changes the results and the precision flag of CVT(T)S*2SI and ROUNDSx on a
  subnormal operand (both give a zero without PE); this is a reading of
  §10.2.3.4, which speaks of denormal source operands in general, and is not
  confirmed on hardware;
* it has lower priority than a NaN operand, an invalid operation and
  divide-by-zero (Vol. 1, §4.9.2), and a higher-priority masked exception
  replaces it, so DE is reported only when no operand is a NaN and neither
  invalid nor divide-by-zero is detected.

The underflow condition depends on UM (Vol. 1, §4.9.1.5 and §10.2.3.3). Masked,
it is the IEEE underflow flag (tiny and inexact) returned by the profile, with
FZ applied. Unmasked, it is tininess alone (after rounding), so an exact tiny
result also faults; FZ then has no effect (`MXCSR.control`). This is the shared
`Profile.underflowCondition` with the trap enabled exactly when UM is clear
(`detect_underflow`).

## Faults

`Result.fault` reports a data-memory fault (`Fault.memory`: the span is not
permitted or not backed), a misaligned 128-bit operand (`Fault.alignment`,
#GP(0)), an attempt to load reserved MXCSR bits (`Fault.reservedMxcsr`, #GP(0),
SDM Vol. 2A, LDMXCSR) or #XM (`Fault.simd`). Memory operands are read before any
computation, so a memory fault takes precedence over #XM.

Not modeled: canonical-address and segment checks, alignment checking with
CR0.AM/EFLAGS.AC, AVX state (the upper YMM/ZMM bits, which legacy SSE
instructions preserve), CR4.OSFXSR/OSXMMEXCPT and #NM/#UD, the RFLAGS bits
other than the six status flags, and memory ordering.
-/

@[expose] public section

namespace Silmaril.X86.Float

open Silmaril.Process (Memory)
open Silmaril.Numeric.Float (Bits Profile x86ComisFlags x86ComparePredicate x86RoundingControl)
open Silmaril.Numeric.Ieee754 (RoundingMode)
open Silmaril.Numeric.Ieee754.FlagSpec (sqrtOutcome convertOutcome ofIntOutcome)

/-! ## Results -/

/-- Why an instruction did not commit. -/
inductive Fault where
  /-- A data access was not permitted or a byte had no backing. -/
  | memory
  /-- #GP(0): a 128-bit legacy SSE memory operand is not 16-byte aligned. -/
  | alignment
  /-- #GP(0): LDMXCSR with a nonzero reserved bit. -/
  | reservedMxcsr
  /-- #XM: an unmasked SIMD floating-point exception. `mxcsr` is MXCSR with the
  detected flags recorded; no other state changes. -/
  | simd (mxcsr : MXCSR)
  deriving DecidableEq, Repr

/-- The outcome of one instruction. -/
inductive Result where
  /-- The instruction retired: the successor state (with RIP advanced) and memory. -/
  | commit (state : State) (memory : Memory)
  | fault (fault : Fault)

/-! ## Operands -/

/-- The effective address of a memory operand, as a natural number. -/
def _root_.Silmaril.X86.Mem.addr (m : Mem) (s : State) : Nat :=
  (m.effectiveAddress s.core.read).toNat

/-- The general-purpose integer format of a conversion or MOVD/MOVQ. -/
def IntWidth.target : IntWidth → Numeric.IntFormat
  | .w32 => .i32
  | .w64 => .i64

/-- The width in bytes of an `r/m32` or `r/m64` memory operand. -/
def IntWidth.bytes : IntWidth → Nat
  | .w32 => 4
  | .w64 => 8

/-- The low `w` bits of a general-purpose register. -/
def IntWidth.truncate : (w : IntWidth) → Word → BitVec w.target.width
  | .w32, v => v.setWidth 32
  | .w64, v => v

/-- A `w`-bit value written to a general-purpose register: a 32-bit write zeroes
bits 63:32 (SDM Vol. 1, §3.4.1.1). -/
def IntWidth.toGpr : (w : IntWidth) → BitVec w.target.width → Word
  | .w32, v => (v : BitVec 32).setWidth 64
  | .w64, v => v

/-- The value of exactly `w.bytes` little-endian bytes. -/
def IntWidth.ofBytes? : (w : IntWidth) → List Byte → Option (BitVec w.target.width)
  | .w32, bytes => ofLe32? bytes
  | .w64, bytes => ofLe64? bytes

/-- Load a scalar lane. -/
def loadLane (p : Precision) (memory : Memory) (address : Nat) : Option (Bits p.fmt) :=
  (memory.readBytes address p.bytes).bind (decodeLane? p)

/-- Load a `w`-bit integer. -/
def loadInt (w : IntWidth) (memory : Memory) (address : Nat) : Option (BitVec w.target.width) :=
  (memory.readBytes address w.bytes).bind w.ofBytes?

/-- Load a 32-bit value. -/
def load32 (memory : Memory) (address : Nat) : Option (BitVec 32) :=
  (memory.readBytes address 4).bind ofLe32?

/-- Load a 128-bit value. -/
def load128 (memory : Memory) (address : Nat) : Option (BitVec 128) :=
  (memory.readBytes address 16).bind ofLe128?

/-- An `xmm/m32` or `xmm/m64` source: the low lane of a register, or a scalar
load (no alignment requirement). -/
def readLane (p : Precision) (s : State) (memory : Memory) : XRM → Option (Bits p.fmt)
  | .reg r => some (lane p (s.readX r))
  | .mem m => loadLane p memory (m.addr s)

/-- An `r/m32` or `r/m64` source. -/
def readInt (w : IntWidth) (s : State) (memory : Memory) : GRM → Option (BitVec w.target.width)
  | .reg r => some (w.truncate (s.core.read r))
  | .mem m => loadInt w memory (m.addr s)

/-- An `xmm/m128` source of a legacy SSE packed instruction, which must be
16-byte aligned. -/
def readPacked (s : State) (memory : Memory) : XRM → Except Fault (BitVec 128)
  | .reg r => .ok (s.readX r)
  | .mem m =>
    if m.addr s % 16 = 0 then
      match load128 memory (m.addr s) with
      | some v => .ok v
      | none => .error .memory
    else .error .alignment

/-! ## Instruction helpers -/

/-- Addition to subtraction via the profile's binary operations; minimum and
maximum via its min/max rule (`true` is maximum). -/
def ArithOp.kind : ArithOp → Numeric.Float.ArithOp ⊕ Bool
  | .add => .inl .add
  | .sub => .inl .sub
  | .mul => .inl .mul
  | .div => .inl .div
  | .min => .inr false
  | .max => .inr true

/-- The 128-bit bitwise operation; ANDN complements the destination. -/
def LogicOp.eval : LogicOp → BitVec 128 → BitVec 128 → BitVec 128
  | .and, d, v => d &&& v
  | .andn, d, v => ~~~d &&& v
  | .or, d, v => d ||| v
  | .xor, d, v => d ^^^ v

/-- The CMPSS/CMPSD result lane: all ones for true, all zeros for false (SDM
Vol. 2A, CMPSS). -/
def cmpMask : (p : Precision) → Bool → Bits p.fmt
  | .single, b => if b then BitVec.allOnes 32 else 0#32
  | .double, b => if b then BitVec.allOnes 64 else 0#64

/-- The CMPSS/CMPSD immediate (0-7) as an index of `x86ComparePredicate`. -/
def CmpPred.index (p : CmpPred) : Fin 32 := ⟨p.toBitVec.toNat, by
  have := p.toBitVec.isLt; simp only [Nat.reducePow] at this; omega⟩

/-- MOVD/MOVQ into an XMM register: zero-extend the low `w` bits. -/
def IntWidth.toXmm : IntWidth → Word → BitVec 128
  | .w32, v => (v.setWidth 32).setWidth 128
  | .w64, v => v.setWidth 128

/-- MOVD/MOVQ out of an XMM register: the low `w` bits, zero-extended to 64. -/
def IntWidth.ofXmm : IntWidth → BitVec 128 → Word
  | .w32, v => (v.setWidth 32).setWidth 64
  | .w64, v => v.setWidth 64

/-- The status flags written by COMIS/UCOMIS: ZF, PF and CF from the comparison
(SDM Vol. 2A, COMISS: unordered 111, greater 000, less 001, equal 100) and OF,
SF and AF cleared. Every flag is defined. -/
def comisFlags (c : Option Ordering) : X86.Flags :=
  let (zf, pf, cf) := x86ComisFlags c
  { carry := some cf, parity := some pf, adjust := some false, zero := some zf,
    sign := some false, overflow := some false }

/-! ## Exception detection and signaling -/

/-- The exceptions detected by one instruction, split into pre-computation
(invalid, denormal, divide-by-zero) and post-computation (overflow, underflow,
precision) conditions (SDM Vol. 1, §11.5.1 and §11.5.3). -/
structure Detected where
  pre : Exceptions := {}
  post : Exceptions := {}
  deriving DecidableEq, Repr

/-- All detected conditions. -/
def Detected.all (d : Detected) : Exceptions := d.pre.union d.post

/-- The MXCSR conditions of a profile outcome.

* `checksDenormal`: the instruction's SDM page lists the denormal-operand
  exception;
* `nanOperand`: some floating-point source is a NaN (a quiet NaN operand takes
  precedence over the denormal-operand condition, SDM Vol. 1, §4.9.2);
* `tiny`: the exact result is tiny, the underflow condition when UM is clear. -/
def detect {α : Type} (m : MXCSR) (checksDenormal nanOperand tiny : Bool)
    (o : Numeric.Float.Outcome α) : Detected where
  pre :=
    { invalid := o.flags.invalidOperation
      divideByZero := o.flags.divisionByZero
      denormal := checksDenormal && !m.daz && o.denormalAfterPriority nanOperand }
  post :=
    { overflow := o.flags.overflow
      underflow := o.flags.underflow || (!m.um && tiny)
      precision := o.flags.inexact }

/-- The SDM rules for masked, unmasked and combined exceptions (Vol. 1,
§11.5.3.1–§11.5.3.3): `error` is #XM with the MXCSR that the handler observes,
`ok` the committed MXCSR. -/
def signal (m : MXCSR) (d : Detected) : Except MXCSR MXCSR :=
  if m.unmasked d.pre then .error (m.record d.pre)
  else if m.unmasked d.post then .error (m.record d.all)
  else .ok (m.record d.all)

/-- The underflow condition of `detect`, with `tiny` computed by the shared
`Profile.tinyOutcome`, is the shared `Profile.underflowCondition` with the trap
enabled exactly when UM is clear. -/
theorem detect_underflow {α : Type} (m : MXCSR) (checksDenormal nanOperand : Bool)
    (fmt : _root_.Float.Model.Format) (mode : RoundingMode)
    (spec : Numeric.Ieee754.FlagSpec.Outcome) (o : Numeric.Float.Outcome α) :
    (detect m checksDenormal nanOperand (m.profile.tinyOutcome fmt mode spec) o).post.underflow =
      m.profile.underflowCondition (!m.um) fmt mode spec o.flags := rfl

/-- Advance RIP past the instruction. -/
def advance (i : Instr) (s : State) : State :=
  { s with core := { s.core with rip := s.core.rip + BitVec.ofNat 64 (encode i).length } }

/-- Commit a floating-point instruction's register update, or raise #XM. -/
def finish (i : Instr) (s : State) (memory : Memory) (d : Detected) (update : State → State) :
    Result :=
  match signal s.mxcsr d with
  | .error m => .fault (.simd m)
  | .ok m => .commit (advance i { update s with mxcsr := m }) memory

/-! ## Scalar operations of an MXCSR configuration

Each operation is the profile operation of `MXCSR.profile` in the rounding
direction the instruction uses, paired with the MXCSR conditions it detects. -/

namespace Scalar

variable (m : MXCSR) (p : Precision)

/-- ADD/SUB/MUL/DIV SS/SD. -/
def binary (a : Numeric.Float.ArithOp) (x y : Bits p.fmt) : Numeric.Float.Outcome (Bits p.fmt) :=
  m.profile.binary p.fmt a m.rounding x y

def binaryDetected (a : Numeric.Float.ArithOp) (x y : Bits p.fmt) : Detected :=
  detect m true (x.isNaN || y.isNaN)
    (m.profile.tinyOutcome p.fmt m.rounding
      (a.outcome (m.profile.flushInput x).datum (m.profile.flushInput y).datum))
    (binary m p a x y)

/-- MIN/MAX SS/SD (`isMax` selects MAX). -/
def minMax (isMax : Bool) (x y : Bits p.fmt) : Numeric.Float.Outcome (Bits p.fmt) :=
  m.profile.minMaxBase isMax x y

def minMaxDetected (isMax : Bool) (x y : Bits p.fmt) : Detected :=
  detect m true (x.isNaN || y.isNaN) false (minMax m p isMax x y)

/-- SQRTSS/SQRTSD. -/
def sqrt (y : Bits p.fmt) : Numeric.Float.Outcome (Bits p.fmt) :=
  m.profile.sqrt p.fmt m.rounding y

def sqrtDetected (y : Bits p.fmt) : Detected :=
  detect m true y.isNaN
    (m.profile.tinyOutcome p.fmt m.rounding (sqrtOutcome (m.profile.flushInput y).datum))
    (sqrt m p y)

/-- CVTSI2SS/CVTSI2SD of a signed `w`-bit integer. -/
def ofInt (w : IntWidth) (v : BitVec w.target.width) : Numeric.Float.Outcome (Bits p.fmt) :=
  m.profile.ofInt p.fmt m.rounding v.toInt

def ofIntDetected (w : IntWidth) (v : BitVec w.target.width) : Detected :=
  detect m false false (m.profile.tinyOutcome p.fmt m.rounding (ofIntOutcome v.toInt))
    (ofInt m p w v)

/-- CVT(T)SS2SI/CVT(T)SD2SI to a signed `w`-bit integer in direction `mode`. -/
def toInt (w : IntWidth) (mode : RoundingMode) (y : Bits p.fmt) :
    Numeric.Float.Outcome (BitVec w.target.width) :=
  m.profile.toInt p.fmt w.target mode y

def toIntDetected (w : IntWidth) (mode : RoundingMode) (y : Bits p.fmt) : Detected :=
  detect m false y.isNaN false (toInt m p w mode y)

/-- CVTSS2SD (`p = single`) or CVTSD2SS (`p = double`). -/
def convert (y : Bits p.fmt) : Numeric.Float.Outcome (Bits p.other.fmt) :=
  m.profile.convert p.fmt p.other.fmt m.rounding y

def convertDetected (y : Bits p.fmt) : Detected :=
  detect m true y.isNaN
    (m.profile.tinyOutcome p.other.fmt m.rounding (convertOutcome (m.profile.flushInput y).datum))
    (convert m p y)

/-- UCOMIS (`signaling = false`) or COMIS (`signaling = true`). -/
def compare (signaling : Bool) (x y : Bits p.fmt) : Numeric.Float.Outcome (Option Ordering) :=
  m.profile.compare signaling x y

def compareDetected (signaling : Bool) (x y : Bits p.fmt) : Detected :=
  detect m true (x.isNaN || y.isNaN) false (compare m p signaling x y)

/-- The ROUNDSS/ROUNDSD direction: MXCSR.RC when imm8[2] is set, otherwise
imm8[1:0] (SDM Vol. 2B, ROUNDSS, and the ROUNDPD immediate table). -/
def roundMode (ctrl : RoundImm) : RoundingMode :=
  if ctrl.useMxcsr then m.rounding else x86RoundingControl ctrl.rc

/-- ROUNDSS/ROUNDSD; imm8[3] set suppresses the precision exception. -/
def round (ctrl : RoundImm) (y : Bits p.fmt) : Numeric.Float.Outcome (Bits p.fmt) :=
  m.profile.roundToIntegral p.fmt (roundMode m ctrl) (!ctrl.suppressInexact) y

def roundDetected (ctrl : RoundImm) (y : Bits p.fmt) : Detected :=
  detect m false y.isNaN false (round m p ctrl y)

/-- CMPSS/CMPSD with predicate `pred`. -/
def cmp (pred : CmpPred) (x y : Bits p.fmt) : Numeric.Float.Outcome Bool :=
  m.profile.comparePredicate (x86ComparePredicate pred.index) x y

def cmpDetected (pred : CmpPred) (x y : Bits p.fmt) : Detected :=
  detect m true (x.isNaN || y.isNaN) false (cmp m p pred x y)

end Scalar

/-! ## Execution -/

/-- Execute one instruction, including its RIP update. -/
def Instr.exec (i : Instr) (s : State) (memory : Memory) : Result :=
  match i with
  | .movs p dst src =>
    .commit (advance i (s.writeX dst (setLane p (s.readX dst) (lane p (s.readX src))))) memory
  | .load p dst m =>
    match loadLane p memory (m.addr s) with
    | none => .fault .memory
    | some x => .commit (advance i (s.writeX dst (zeroLane p x))) memory
  | .store p m src =>
    match memory.writeBytes (m.addr s) (encodeLane p (lane p (s.readX src))) with
    | none => .fault .memory
    | some after => .commit (advance i s) after
  | .movToX w dst src => .commit (advance i (s.writeX dst (w.toXmm (s.core.read src)))) memory
  | .movFromX w dst src => .commit (advance i (s.writeGpr dst (w.ofXmm (s.readX src)))) memory
  | .movap _ dst src => .commit (advance i (s.writeX dst (s.readX src))) memory
  | .arith op p dst src =>
    match readLane p s memory src with
    | none => .fault .memory
    | some y =>
      match op.kind with
      | .inl a =>
        finish i s memory (Scalar.binaryDetected s.mxcsr p a (lane p (s.readX dst)) y)
          fun u => u.writeX dst (setLane p (u.readX dst)
            (Scalar.binary s.mxcsr p a (lane p (s.readX dst)) y).value)
      | .inr isMax =>
        finish i s memory (Scalar.minMaxDetected s.mxcsr p isMax (lane p (s.readX dst)) y)
          fun u => u.writeX dst (setLane p (u.readX dst)
            (Scalar.minMax s.mxcsr p isMax (lane p (s.readX dst)) y).value)
  | .sqrt p dst src =>
    match readLane p s memory src with
    | none => .fault .memory
    | some y =>
      finish i s memory (Scalar.sqrtDetected s.mxcsr p y)
        fun u => u.writeX dst (setLane p (u.readX dst) (Scalar.sqrt s.mxcsr p y).value)
  | .cvtFromInt p w dst src =>
    match readInt w s memory src with
    | none => .fault .memory
    | some v =>
      finish i s memory (Scalar.ofIntDetected s.mxcsr p w v)
        fun u => u.writeX dst (setLane p (u.readX dst) (Scalar.ofInt s.mxcsr p w v).value)
  | .cvtToIntTrunc p w dst src =>
    match readLane p s memory src with
    | none => .fault .memory
    | some y =>
      finish i s memory (Scalar.toIntDetected s.mxcsr p w .towardZero y)
        fun u => u.writeGpr dst (w.toGpr (Scalar.toInt s.mxcsr p w .towardZero y).value)
  | .cvtToInt p w dst src =>
    match readLane p s memory src with
    | none => .fault .memory
    | some y =>
      finish i s memory (Scalar.toIntDetected s.mxcsr p w s.mxcsr.rounding y)
        fun u => u.writeGpr dst (w.toGpr (Scalar.toInt s.mxcsr p w s.mxcsr.rounding y).value)
  | .cvtPrec p dst src =>
    match readLane p s memory src with
    | none => .fault .memory
    | some y =>
      finish i s memory (Scalar.convertDetected s.mxcsr p y)
        fun u => u.writeX dst (setLane p.other (u.readX dst) (Scalar.convert s.mxcsr p y).value)
  | .ucomi p a b =>
    match readLane p s memory b with
    | none => .fault .memory
    | some y =>
      finish i s memory (Scalar.compareDetected s.mxcsr p false (lane p (s.readX a)) y)
        fun u => { u with core := { u.core with
          flags := comisFlags (Scalar.compare s.mxcsr p false (lane p (s.readX a)) y).value } }
  | .comi p a b =>
    match readLane p s memory b with
    | none => .fault .memory
    | some y =>
      finish i s memory (Scalar.compareDetected s.mxcsr p true (lane p (s.readX a)) y)
        fun u => { u with core := { u.core with
          flags := comisFlags (Scalar.compare s.mxcsr p true (lane p (s.readX a)) y).value } }
  | .logic op _ dst src =>
    match readPacked s memory src with
    | .error f => .fault f
    | .ok v => .commit (advance i (s.writeX dst (op.eval (s.readX dst) v))) memory
  | .round p dst src ctrl =>
    match readLane p s memory src with
    | none => .fault .memory
    | some y =>
      finish i s memory (Scalar.roundDetected s.mxcsr p ctrl y)
        fun u => u.writeX dst (setLane p (u.readX dst) (Scalar.round s.mxcsr p ctrl y).value)
  | .cmp p pred dst src =>
    match readLane p s memory src with
    | none => .fault .memory
    | some y =>
      finish i s memory (Scalar.cmpDetected s.mxcsr p pred (lane p (s.readX dst)) y)
        fun u => u.writeX dst (setLane p (u.readX dst)
          (cmpMask p (Scalar.cmp s.mxcsr p pred (lane p (s.readX dst)) y).value))
  | .ldmxcsr m =>
    match load32 memory (m.addr s) with
    | none => .fault .memory
    | some v =>
      if (⟨v⟩ : MXCSR).WellFormed then .commit (advance i { s with mxcsr := ⟨v⟩ }) memory
      else .fault .reservedMxcsr
  | .stmxcsr m =>
    match memory.writeBytes (m.addr s) (le32 s.mxcsr.bits) with
    | none => .fault .memory
    | some after => .commit (advance i s) after

/-! ## Signaling -/

theorem signal_eq_ok_iff {m m' : MXCSR} {d : Detected} :
    signal m d = .ok m' ↔
      m.unmasked d.pre = false ∧ m.unmasked d.post = false ∧ m' = m.record d.all := by
  unfold signal
  cases h1 : m.unmasked d.pre <;> cases h2 : m.unmasked d.post <;>
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Except.ok.injEq, true_and,
      false_and, and_false]
  all_goals exact eq_comm

/-- #XM is raised exactly when a detected exception is unmasked. -/
theorem signal_eq_error_iff {m m' : MXCSR} {d : Detected} :
    signal m d = .error m' ↔
      (m.unmasked d.pre = true ∨ m.unmasked d.post = true) ∧
        m' = (if m.unmasked d.pre then m.record d.pre else m.record d.all) := by
  unfold signal
  cases h1 : m.unmasked d.pre <;> cases h2 : m.unmasked d.post <;>
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Except.error.injEq, true_and,
      false_and, or_self, or_true, true_or]
  all_goals exact eq_comm

theorem signal_of_allMasked {m : MXCSR} (h : m.AllMasked) (d : Detected) :
    signal m d = .ok (m.record d.all) := by
  simp [signal, MXCSR.unmasked_eq_false_of_allMasked h]

/-- `finish` commits exactly when no detected exception is unmasked; the
committed state is the update with the detected flags OR-ed into MXCSR and RIP
advanced. -/
theorem finish_eq_commit_iff_unmasked {i : Instr} {s t : State} {memory after : Memory}
    {d : Detected} {update : State → State} :
    finish i s memory d update = .commit t after ↔
      s.mxcsr.unmasked d.pre = false ∧ s.mxcsr.unmasked d.post = false ∧
        t = advance i { update s with mxcsr := s.mxcsr.record d.all } ∧ after = memory := by
  unfold finish
  split
  · rename_i h; simp only [signal_eq_error_iff] at h
    simp only [reduceCtorEq, false_iff, not_and]
    intro h1 h2; rcases h.1 with h' | h' <;> simp_all
  · rename_i m h
    rw [signal_eq_ok_iff] at h
    obtain ⟨h1, h2, rfl⟩ := h
    simp only [Result.commit.injEq, h1, h2, true_and]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

/-- `finish` faults exactly when a detected exception is unmasked, and the fault
is #XM carrying the recorded MXCSR. -/
theorem finish_eq_fault_iff_unmasked {i : Instr} {s : State} {memory : Memory} {d : Detected}
    {update : State → State} {f : Fault} :
    finish i s memory d update = .fault f ↔
      (s.mxcsr.unmasked d.pre = true ∨ s.mxcsr.unmasked d.post = true) ∧
        f = .simd (if s.mxcsr.unmasked d.pre then s.mxcsr.record d.pre
          else s.mxcsr.record d.all) := by
  unfold finish
  split
  · rename_i m h
    rw [signal_eq_error_iff] at h
    obtain ⟨h1, rfl⟩ := h
    simp only [Result.fault.injEq, h1, true_and]
    constructor <;> (rintro rfl; rfl)
  · rename_i m h
    rw [signal_eq_ok_iff] at h
    simp [h.1, h.2.1]

/-- Whether the detected exceptions raise #XM under this MXCSR: some detected
exception is unmasked. -/
def _root_.Silmaril.X86.Float.MXCSR.faults (m : MXCSR) (d : Detected) : Bool :=
  m.unmasked d.pre || m.unmasked d.post

/-- The MXCSR that a #XM handler observes: only the pre-computation flags when
a pre-computation exception is unmasked, otherwise all detected flags. -/
def _root_.Silmaril.X86.Float.MXCSR.faultRecord (m : MXCSR) (d : Detected) : MXCSR :=
  if m.unmasked d.pre then m.record d.pre else m.record d.all

theorem finish_eq_commit_iff {i : Instr} {s t : State} {memory after : Memory} {d : Detected}
    {update : State → State} :
    finish i s memory d update = .commit t after ↔
      s.mxcsr.faults d = false ∧
        t = advance i { update s with mxcsr := s.mxcsr.record d.all } ∧ after = memory := by
  rw [finish_eq_commit_iff_unmasked, MXCSR.faults, Bool.or_eq_false_iff, and_assoc]

theorem finish_eq_fault_iff {i : Instr} {s : State} {memory : Memory} {d : Detected}
    {update : State → State} {f : Fault} :
    finish i s memory d update = .fault f ↔
      s.mxcsr.faults d = true ∧ f = .simd (s.mxcsr.faultRecord d) := by
  rw [finish_eq_fault_iff_unmasked, MXCSR.faults, Bool.or_eq_true, MXCSR.faultRecord]

theorem finish_of_allMasked {i : Instr} {s : State} (memory : Memory) (d : Detected)
    (update : State → State) (h : s.mxcsr.AllMasked) :
    finish i s memory d update =
      .commit (advance i { update s with mxcsr := s.mxcsr.record d.all }) memory := by
  simp [finish, signal_of_allMasked h]

/-! ## No #XM when every exception is masked -/

theorem readPacked_ne_simd (s : State) (memory : Memory) (src : XRM) (m : MXCSR) :
    readPacked s memory src ≠ .error (.simd m) := by
  unfold readPacked
  split
  · simp
  · split
    · split <;> simp
    · simp

/-- With every exception masked, no instruction raises #XM. -/
theorem exec_ne_simd_of_allMasked (i : Instr) (s : State) (memory : Memory) (m : MXCSR)
    (h : s.mxcsr.AllMasked) : i.exec s memory ≠ .fault (.simd m) := by
  intro e
  unfold Instr.exec at e
  split at e <;> (repeat' split at e) <;>
    simp_all [finish_of_allMasked, readPacked_ne_simd]

/-- Under the reset MXCSR (`1F80H`: every exception masked, round to nearest,
DAZ = FZ = 0) no instruction raises #XM. -/
theorem exec_ne_simd_of_reset (i : Instr) (s : State) (memory : Memory) (m : MXCSR)
    (h : s.mxcsr = MXCSR.reset) : i.exec s memory ≠ .fault (.simd m) :=
  exec_ne_simd_of_allMasked i s memory m (h ▸ MXCSR.reset_allMasked)

/-! ## RIP advance -/

@[simp] theorem advance_xmm (i : Instr) (s : State) : (advance i s).xmm = s.xmm := rfl
@[simp] theorem advance_mxcsr (i : Instr) (s : State) : (advance i s).mxcsr = s.mxcsr := rfl
@[simp] theorem advance_readX (i : Instr) (s : State) (r : XReg) :
    (advance i s).readX r = s.readX r := rfl
@[simp] theorem advance_read (i : Instr) (s : State) (r : Reg) :
    (advance i s).core.read r = s.core.read r := rfl
@[simp] theorem advance_regs (i : Instr) (s : State) : (advance i s).core.regs = s.core.regs :=
  rfl
@[simp] theorem advance_flags (i : Instr) (s : State) : (advance i s).core.flags = s.core.flags :=
  rfl
@[simp] theorem advance_rip (i : Instr) (s : State) :
    (advance i s).core.rip = s.core.rip + BitVec.ofNat 64 (encode i).length := rfl

/-! ## Frames

Which parts of the state an instruction may change when it commits. -/

/-- The XMM register an instruction writes, if any. -/
def Instr.xmmDest? : Instr → Option XReg
  | .movs _ d _ | .load _ d _ | .movToX _ d _ | .movap _ d _ | .arith _ _ d _ | .sqrt _ d _
  | .cvtFromInt _ _ d _ | .cvtPrec _ d _ | .logic _ _ d _ | .round _ d _ _ | .cmp _ _ d _ => some d
  | .store .. | .movFromX .. | .cvtToIntTrunc .. | .cvtToInt .. | .ucomi .. | .comi ..
  | .ldmxcsr _ | .stmxcsr _ => none

/-- The general-purpose register an instruction writes, if any. -/
def Instr.gprDest? : Instr → Option Reg
  | .movFromX _ d _ | .cvtToIntTrunc _ _ d _ | .cvtToInt _ _ d _ => some d
  | _ => none

/-- Whether an instruction writes the RFLAGS status flags (COMIS/UCOMIS only). -/
def Instr.writesRflags : Instr → Bool
  | .ucomi .. | .comi .. => true
  | _ => false

/-- The memory span `(address, length)` an instruction stores to, if any. -/
def Instr.storeSpan (i : Instr) (s : State) : Option (Nat × Nat) :=
  match i with
  | .store p m _ => some (m.addr s, p.bytes)
  | .stmxcsr m => some (m.addr s, 4)
  | _ => none

section Frames

/-- Split a committed `exec` into the per-instruction state equations. -/
local macro "exec_cases " i:ident h:ident : tactic => `(tactic| (
  cases $i:ident <;> simp only [Instr.exec] at $h:ident <;> (repeat' split at $h:ident) <;>
  (try simp only [finish_eq_commit_iff_unmasked, Result.commit.injEq, reduceCtorEq] at $h:ident) <;>
  (first
    | (obtain ⟨h₁, h₂⟩ := $h:ident; subst h₁; subst h₂)
    | (obtain ⟨-, -, h₁, h₂⟩ := $h:ident; subst h₁; subst h₂)
    | skip)))

private theorem write_apply_of_ne {α β : Type} [DecidableEq α] (f : α → β) {d r : α}
    (v : β) (h : ¬ d = r) : Machine.RegisterFile.write f d v r = f r :=
  Machine.RegisterFile.write_other f d r v (Ne.symm h)

variable {i : Instr} {s t : State} {memory after : Memory}

/-- RIP advances by the encoded length. -/
theorem exec_commit_rip (h : i.exec s memory = .commit t after) :
    t.core.rip = s.core.rip + BitVec.ofNat 64 (encode i).length := by
  exec_cases i h <;> simp [State.writeGpr, State.writeX]

/-- XMM registers other than the destination are unchanged. -/
theorem exec_commit_readX (h : i.exec s memory = .commit t after) (r : XReg)
    (hr : i.xmmDest? ≠ some r) : t.readX r = s.readX r := by
  exec_cases i h <;> simp_all [Instr.xmmDest?, State.readX, State.writeX, State.writeGpr,
    write_apply_of_ne]

/-- General-purpose registers other than the destination are unchanged. -/
theorem exec_commit_read (h : i.exec s memory = .commit t after) (r : Reg)
    (hr : i.gprDest? ≠ some r) : t.core.read r = s.core.read r := by
  exec_cases i h <;> simp_all [Instr.gprDest?, State.writeGpr, State.writeX, X86.State.read,
    X86.State.write, write_apply_of_ne]

/-- RFLAGS is unchanged except by COMIS/UCOMIS. -/
theorem exec_commit_flags (h : i.exec s memory = .commit t after)
    (hr : i.writesRflags = false) : t.core.flags = s.core.flags := by
  exec_cases i h <;> simp_all [Instr.writesRflags, State.writeGpr, State.writeX]

/-- Memory is unchanged except for the stored span, and no mapping changes. -/
theorem exec_commit_memory (h : i.exec s memory = .commit t after) :
    match i.storeSpan s with
    | none => after = memory
    | some (address, length) => Memory.WritesOnly memory after address length := by
  exec_cases i h <;> simp only [Instr.storeSpan]
  · rename_i hw
    simpa using Memory.writeBytes_writesOnly hw
  · rename_i hw
    simpa using Memory.writeBytes_writesOnly hw

/-- Apart from LDMXCSR, a committed instruction only sets MXCSR flags: the
result is the incoming MXCSR with some exception set recorded, so the masks,
RC, DAZ and FZ are unchanged. -/
theorem exec_commit_mxcsr (h : i.exec s memory = .commit t after)
    (hi : ∀ m, i ≠ .ldmxcsr m) : ∃ e, t.mxcsr = s.mxcsr.record e := by
  exec_cases i h <;> first
    | exact absurd rfl (hi _)
    | exact ⟨_, rfl⟩
    | exact ⟨{}, by simp [State.writeX, State.writeGpr]⟩

/-- A committed instruction keeps MXCSR well formed. -/
theorem exec_commit_wellFormed (h : i.exec s memory = .commit t after)
    (hw : s.mxcsr.WellFormed) : t.mxcsr.WellFormed := by
  by_cases hl : ∃ m, i = .ldmxcsr m
  · obtain ⟨m, rfl⟩ := hl
    simp only [Instr.exec] at h
    repeat' split at h
    all_goals simp only [Result.commit.injEq, reduceCtorEq] at h
    obtain ⟨rfl, -⟩ := h
    assumption
  · obtain ⟨e, he⟩ := exec_commit_mxcsr h (fun m hm => hl ⟨m, hm⟩)
    rw [he]
    exact MXCSR.record_wellFormed _ _ hw

/-- The MXCSR carried by a #XM fault is the incoming MXCSR with some exception
set recorded: its masks and controls are unchanged. -/
theorem exec_simd_record {m : MXCSR} (h : i.exec s memory = .fault (.simd m)) :
    ∃ e, m = s.mxcsr.record e := by
  cases i <;> simp only [Instr.exec] at h <;> (repeat' split at h) <;>
    first
    | (rw [finish_eq_fault_iff_unmasked] at h; obtain ⟨-, h⟩ := h;
        simp only [Fault.simd.injEq] at h; split at h <;> exact ⟨_, h⟩)
    | simp_all [readPacked_ne_simd]

end Frames

/-! ## Per-instruction behaviour

For each floating-point instruction whose operands can be read: an unfolding
lemma stating the instruction as `finish` of a `Scalar` profile operation, the
exact fault condition (`MXCSR.faults`, carrying `MXCSR.faultRecord`), and the
committed result. The frame lemmas above give the unchanged state. -/

section Commit

variable {i : Instr} {s t : State} {memory after : Memory} {d : Detected}

/-- A committed scalar result: the low lane of `dst` holds `v`, the bits above
the lane keep their old values, and MXCSR accumulates the detected flags. -/
theorem finish_setLane_commit {q : Precision} {dst : XReg} {v : Bits q.fmt}
    (h : finish i s memory d (fun u => u.writeX dst (setLane q (u.readX dst) v)) =
      .commit t after) :
    lane q (t.readX dst) = v ∧
      (∀ j, q.width ≤ j → (t.readX dst).getLsbD j = (s.readX dst).getLsbD j) ∧
      t.mxcsr = s.mxcsr.record d.all ∧ after = memory := by
  rw [finish_eq_commit_iff] at h
  obtain ⟨-, rfl, rfl⟩ := h
  refine ⟨by simp [State.readX, State.writeX], fun j hj => ?_, rfl, rfl⟩
  have : ({ s.writeX dst (setLane q (s.readX dst) v) with mxcsr := s.mxcsr.record d.all }.readX
      dst) = setLane q (s.readX dst) v := by simp [State.readX, State.writeX]
  rw [advance_readX, this]
  exact getLsbD_setLane_upper q _ v hj

/-- A committed general-purpose result. -/
theorem finish_writeGpr_commit {dst : Reg} {v : Word}
    (h : finish i s memory d (fun u => u.writeGpr dst v) = .commit t after) :
    t.core.read dst = v ∧ t.mxcsr = s.mxcsr.record d.all ∧ after = memory := by
  rw [finish_eq_commit_iff] at h
  obtain ⟨-, rfl, rfl⟩ := h
  exact ⟨by simp [State.writeGpr, X86.State.read, X86.State.write], rfl, rfl⟩

/-- A committed RFLAGS result. -/
theorem finish_flags_commit {F : X86.Flags}
    (h : finish i s memory d (fun u => { u with core := { u.core with flags := F } }) =
      .commit t after) :
    t.core.flags = F ∧ t.mxcsr = s.mxcsr.record d.all ∧ after = memory := by
  rw [finish_eq_commit_iff] at h
  obtain ⟨-, rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

end Commit

section PerInstruction

variable {s t : State} {memory after : Memory}


/-- ADD/SUB/MUL/DIV SS/SD as `finish` of its profile operation. -/
theorem exec_arith_binary {op : ArithOp} {a : Numeric.Float.ArithOp} {p : Precision} {dst : XReg}
    {src : XRM} {y : Bits p.fmt} (hop : op.kind = .inl a) (hy : readLane p s memory src = some y) :
    (Instr.arith op p dst src).exec s memory =
      finish (Instr.arith op p dst src) s memory
        (Scalar.binaryDetected s.mxcsr p a (lane p (s.readX dst)) y)
        (fun u => u.writeX dst
          (setLane p (u.readX dst)
            ((Scalar.binary s.mxcsr p a (lane p (s.readX dst)) y).value))) := by
  simp only [Instr.exec, hy, hop]

/-- ADD/SUB/MUL/DIV SS/SD raises a fault exactly when a detected exception is unmasked; the
fault is #XM with the recorded MXCSR. -/
theorem exec_arith_binary_eq_fault_iff {op : ArithOp} {a : Numeric.Float.ArithOp} {p : Precision}
    {dst : XReg} {src : XRM} {y : Bits p.fmt} (hop : op.kind = .inl a)
    (hy : readLane p s memory src = some y) {f : Fault} :
    (Instr.arith op p dst src).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.binaryDetected s.mxcsr p a (lane p (s.readX dst)) y) = true ∧
        f = .simd
          (s.mxcsr.faultRecord (Scalar.binaryDetected s.mxcsr p a (lane p (s.readX dst)) y)) := by
  rw [exec_arith_binary hop hy, finish_eq_fault_iff]

/-- ADD/SUB/MUL/DIV SS/SD on commit: the low lane of the destination is the profile result, the bits
above it are unchanged and MXCSR accumulates the detected flags. -/
theorem exec_arith_binary_commit {op : ArithOp} {a : Numeric.Float.ArithOp} {p : Precision}
    {dst : XReg} {src : XRM} {y : Bits p.fmt} (hop : op.kind = .inl a)
    (hy : readLane p s memory src = some y)
    (h : (Instr.arith op p dst src).exec s memory = .commit t after) :
    lane p (t.readX dst) = (Scalar.binary s.mxcsr p a (lane p (s.readX dst)) y).value ∧
      (∀ j, p.width ≤ j → (t.readX dst).getLsbD j = (s.readX dst).getLsbD j) ∧
      t.mxcsr = s.mxcsr.record (Scalar.binaryDetected s.mxcsr p a (lane p (s.readX dst)) y).all ∧
        after = memory :=
  finish_setLane_commit (by rwa [exec_arith_binary hop hy] at h)


/-- MIN/MAX SS/SD as `finish` of its profile operation. -/
theorem exec_arith_minMax {op : ArithOp} {isMax : Bool} {p : Precision} {dst : XReg} {src : XRM}
    {y : Bits p.fmt} (hop : op.kind = .inr isMax) (hy : readLane p s memory src = some y) :
    (Instr.arith op p dst src).exec s memory =
      finish (Instr.arith op p dst src) s memory
        (Scalar.minMaxDetected s.mxcsr p isMax (lane p (s.readX dst)) y)
        (fun u => u.writeX dst
          (setLane p (u.readX dst)
            ((Scalar.minMax s.mxcsr p isMax (lane p (s.readX dst)) y).value))) := by
  simp only [Instr.exec, hy, hop]

/-- MIN/MAX SS/SD raises a fault exactly when a detected exception is unmasked; the
fault is #XM with the recorded MXCSR. -/
theorem exec_arith_minMax_eq_fault_iff {op : ArithOp} {isMax : Bool} {p : Precision} {dst : XReg}
    {src : XRM} {y : Bits p.fmt} (hop : op.kind = .inr isMax)
    (hy : readLane p s memory src = some y) {f : Fault} :
    (Instr.arith op p dst src).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.minMaxDetected s.mxcsr p isMax (lane p (s.readX dst)) y) = true ∧
        f = .simd
          (s.mxcsr.faultRecord
            (Scalar.minMaxDetected s.mxcsr p isMax (lane p (s.readX dst)) y)) := by
  rw [exec_arith_minMax hop hy, finish_eq_fault_iff]

/-- MIN/MAX SS/SD on commit: the low lane of the destination is the profile result, the bits above
it are unchanged and MXCSR accumulates the detected flags. -/
theorem exec_arith_minMax_commit {op : ArithOp} {isMax : Bool} {p : Precision} {dst : XReg}
    {src : XRM} {y : Bits p.fmt} (hop : op.kind = .inr isMax)
    (hy : readLane p s memory src = some y)
    (h : (Instr.arith op p dst src).exec s memory = .commit t after) :
    lane p (t.readX dst) = (Scalar.minMax s.mxcsr p isMax (lane p (s.readX dst)) y).value ∧
      (∀ j, p.width ≤ j → (t.readX dst).getLsbD j = (s.readX dst).getLsbD j) ∧
      t.mxcsr = s.mxcsr.record
        (Scalar.minMaxDetected s.mxcsr p isMax (lane p (s.readX dst)) y).all ∧ after = memory :=
  finish_setLane_commit (by rwa [exec_arith_minMax hop hy] at h)


/-- SQRTSS/SQRTSD as `finish` of its profile operation. -/
theorem exec_sqrt {p : Precision} {dst : XReg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y) :
    (Instr.sqrt p dst src).exec s memory =
      finish (Instr.sqrt p dst src) s memory (Scalar.sqrtDetected s.mxcsr p y)
        (fun u => u.writeX dst (setLane p (u.readX dst) ((Scalar.sqrt s.mxcsr p y).value))) := by
  simp only [Instr.exec, hy]

/-- SQRTSS/SQRTSD raises a fault exactly when a detected exception is unmasked; the
fault is #XM with the recorded MXCSR. -/
theorem exec_sqrt_eq_fault_iff {p : Precision} {dst : XReg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y) {f : Fault} :
    (Instr.sqrt p dst src).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.sqrtDetected s.mxcsr p y) = true ∧
        f = .simd (s.mxcsr.faultRecord (Scalar.sqrtDetected s.mxcsr p y)) := by
  rw [exec_sqrt hy, finish_eq_fault_iff]

/-- SQRTSS/SQRTSD on commit: the low lane of the destination is the profile result, the bits above
it are unchanged and MXCSR accumulates the detected flags. -/
theorem exec_sqrt_commit {p : Precision} {dst : XReg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y)
    (h : (Instr.sqrt p dst src).exec s memory = .commit t after) :
    lane p (t.readX dst) = (Scalar.sqrt s.mxcsr p y).value ∧
      (∀ j, p.width ≤ j → (t.readX dst).getLsbD j = (s.readX dst).getLsbD j) ∧
      t.mxcsr = s.mxcsr.record (Scalar.sqrtDetected s.mxcsr p y).all ∧ after = memory :=
  finish_setLane_commit (by rwa [exec_sqrt hy] at h)


/-- CVTSI2SS/CVTSI2SD as `finish` of its profile operation. -/
theorem exec_cvtFromInt {p : Precision} {w : IntWidth} {dst : XReg} {src : GRM}
    {v : BitVec w.target.width} (hv : readInt w s memory src = some v) :
    (Instr.cvtFromInt p w dst src).exec s memory =
      finish (Instr.cvtFromInt p w dst src) s memory (Scalar.ofIntDetected s.mxcsr p w v)
        (fun u => u.writeX dst (setLane p (u.readX dst) ((Scalar.ofInt s.mxcsr p w v).value))) := by
  simp only [Instr.exec, hv]

/-- CVTSI2SS/CVTSI2SD raises a fault exactly when a detected exception is unmasked; the
fault is #XM with the recorded MXCSR. -/
theorem exec_cvtFromInt_eq_fault_iff {p : Precision} {w : IntWidth} {dst : XReg} {src : GRM}
    {v : BitVec w.target.width} (hv : readInt w s memory src = some v) {f : Fault} :
    (Instr.cvtFromInt p w dst src).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.ofIntDetected s.mxcsr p w v) = true ∧
        f = .simd (s.mxcsr.faultRecord (Scalar.ofIntDetected s.mxcsr p w v)) := by
  rw [exec_cvtFromInt hv, finish_eq_fault_iff]

/-- CVTSI2SS/CVTSI2SD on commit: the low lane of the destination is the profile result, the bits
above it are unchanged and MXCSR accumulates the detected flags. -/
theorem exec_cvtFromInt_commit {p : Precision} {w : IntWidth} {dst : XReg} {src : GRM}
    {v : BitVec w.target.width} (hv : readInt w s memory src = some v)
    (h : (Instr.cvtFromInt p w dst src).exec s memory = .commit t after) :
    lane p (t.readX dst) = (Scalar.ofInt s.mxcsr p w v).value ∧
      (∀ j, p.width ≤ j → (t.readX dst).getLsbD j = (s.readX dst).getLsbD j) ∧
      t.mxcsr = s.mxcsr.record (Scalar.ofIntDetected s.mxcsr p w v).all ∧ after = memory :=
  finish_setLane_commit (by rwa [exec_cvtFromInt hv] at h)


/-- CVTSS2SD/CVTSD2SS as `finish` of its profile operation. -/
theorem exec_cvtPrec {p : Precision} {dst : XReg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y) :
    (Instr.cvtPrec p dst src).exec s memory =
      finish (Instr.cvtPrec p dst src) s memory (Scalar.convertDetected s.mxcsr p y)
        (fun u => u.writeX dst
          (setLane p.other (u.readX dst) ((Scalar.convert s.mxcsr p y).value))) := by
  simp only [Instr.exec, hy]

/-- CVTSS2SD/CVTSD2SS raises a fault exactly when a detected exception is unmasked; the
fault is #XM with the recorded MXCSR. -/
theorem exec_cvtPrec_eq_fault_iff {p : Precision} {dst : XReg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y) {f : Fault} :
    (Instr.cvtPrec p dst src).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.convertDetected s.mxcsr p y) = true ∧
        f = .simd (s.mxcsr.faultRecord (Scalar.convertDetected s.mxcsr p y)) := by
  rw [exec_cvtPrec hy, finish_eq_fault_iff]

/-- CVTSS2SD/CVTSD2SS on commit: the low lane of the destination is the profile result, the bits
above it are unchanged and MXCSR accumulates the detected flags. -/
theorem exec_cvtPrec_commit {p : Precision} {dst : XReg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y)
    (h : (Instr.cvtPrec p dst src).exec s memory = .commit t after) :
    lane p.other (t.readX dst) = (Scalar.convert s.mxcsr p y).value ∧
      (∀ j, p.other.width ≤ j → (t.readX dst).getLsbD j = (s.readX dst).getLsbD j) ∧
      t.mxcsr = s.mxcsr.record (Scalar.convertDetected s.mxcsr p y).all ∧ after = memory :=
  finish_setLane_commit (by rwa [exec_cvtPrec hy] at h)


/-- ROUNDSS/ROUNDSD as `finish` of its profile operation. -/
theorem exec_round {p : Precision} {dst : XReg} {src : XRM} {ctrl : RoundImm} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y) :
    (Instr.round p dst src ctrl).exec s memory =
      finish (Instr.round p dst src ctrl) s memory (Scalar.roundDetected s.mxcsr p ctrl y)
        (fun u => u.writeX dst
          (setLane p (u.readX dst) ((Scalar.round s.mxcsr p ctrl y).value))) := by
  simp only [Instr.exec, hy]

/-- ROUNDSS/ROUNDSD raises a fault exactly when a detected exception is unmasked; the
fault is #XM with the recorded MXCSR. -/
theorem exec_round_eq_fault_iff {p : Precision} {dst : XReg} {src : XRM} {ctrl : RoundImm}
    {y : Bits p.fmt} (hy : readLane p s memory src = some y) {f : Fault} :
    (Instr.round p dst src ctrl).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.roundDetected s.mxcsr p ctrl y) = true ∧
        f = .simd (s.mxcsr.faultRecord (Scalar.roundDetected s.mxcsr p ctrl y)) := by
  rw [exec_round hy, finish_eq_fault_iff]

/-- ROUNDSS/ROUNDSD on commit: the low lane of the destination is the profile result, the bits above
it are unchanged and MXCSR accumulates the detected flags. -/
theorem exec_round_commit {p : Precision} {dst : XReg} {src : XRM} {ctrl : RoundImm}
    {y : Bits p.fmt} (hy : readLane p s memory src = some y)
    (h : (Instr.round p dst src ctrl).exec s memory = .commit t after) :
    lane p (t.readX dst) = (Scalar.round s.mxcsr p ctrl y).value ∧
      (∀ j, p.width ≤ j → (t.readX dst).getLsbD j = (s.readX dst).getLsbD j) ∧
      t.mxcsr = s.mxcsr.record (Scalar.roundDetected s.mxcsr p ctrl y).all ∧ after = memory :=
  finish_setLane_commit (by rwa [exec_round hy] at h)


/-- CMPSS/CMPSD as `finish` of its profile operation. -/
theorem exec_cmp {p : Precision} {pred : CmpPred} {dst : XReg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y) :
    (Instr.cmp p pred dst src).exec s memory =
      finish (Instr.cmp p pred dst src) s memory
        (Scalar.cmpDetected s.mxcsr p pred (lane p (s.readX dst)) y)
        (fun u => u.writeX dst
          (setLane p (u.readX dst)
            (cmpMask p (Scalar.cmp s.mxcsr p pred (lane p (s.readX dst)) y).value))) := by
  simp only [Instr.exec, hy]

/-- CMPSS/CMPSD raises a fault exactly when a detected exception is unmasked; the
fault is #XM with the recorded MXCSR. -/
theorem exec_cmp_eq_fault_iff {p : Precision} {pred : CmpPred} {dst : XReg} {src : XRM}
    {y : Bits p.fmt} (hy : readLane p s memory src = some y) {f : Fault} :
    (Instr.cmp p pred dst src).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.cmpDetected s.mxcsr p pred (lane p (s.readX dst)) y) = true ∧
        f = .simd
          (s.mxcsr.faultRecord (Scalar.cmpDetected s.mxcsr p pred (lane p (s.readX dst)) y)) := by
  rw [exec_cmp hy, finish_eq_fault_iff]

/-- CMPSS/CMPSD on commit: the low lane of the destination is the profile result, the bits above it
are unchanged and MXCSR accumulates the detected flags. -/
theorem exec_cmp_commit {p : Precision} {pred : CmpPred} {dst : XReg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y)
    (h : (Instr.cmp p pred dst src).exec s memory = .commit t after) :
    lane p (t.readX dst) = cmpMask p (Scalar.cmp s.mxcsr p pred (lane p (s.readX dst)) y).value ∧
      (∀ j, p.width ≤ j → (t.readX dst).getLsbD j = (s.readX dst).getLsbD j) ∧
      t.mxcsr = s.mxcsr.record (Scalar.cmpDetected s.mxcsr p pred (lane p (s.readX dst)) y).all ∧
        after = memory :=
  finish_setLane_commit (by rwa [exec_cmp hy] at h)


/-- CVTTSS2SI/CVTTSD2SI (truncating) as `finish` of its profile operation. -/
theorem exec_cvtToIntTrunc {p : Precision} {w : IntWidth} {dst : Reg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y) :
    (Instr.cvtToIntTrunc p w dst src).exec s memory =
      finish (Instr.cvtToIntTrunc p w dst src) s memory
        (Scalar.toIntDetected s.mxcsr p w .towardZero y)
        (fun u => u.writeGpr dst (w.toGpr (Scalar.toInt s.mxcsr p w .towardZero y).value)) := by
  simp only [Instr.exec, hy]

/-- CVTTSS2SI/CVTTSD2SI (truncating) raises a fault exactly when a detected exception is unmasked;
the fault is #XM with the recorded MXCSR. -/
theorem exec_cvtToIntTrunc_eq_fault_iff {p : Precision} {w : IntWidth} {dst : Reg} {src : XRM}
    {y : Bits p.fmt} (hy : readLane p s memory src = some y) {f : Fault} :
    (Instr.cvtToIntTrunc p w dst src).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.toIntDetected s.mxcsr p w .towardZero y) = true ∧
        f = .simd (s.mxcsr.faultRecord (Scalar.toIntDetected s.mxcsr p w .towardZero y)) := by
  rw [exec_cvtToIntTrunc hy, finish_eq_fault_iff]

/-- CVTTSS2SI/CVTTSD2SI (truncating) on commit: the destination register holds the profile result
(zero-extended from 32 bits for a 32-bit destination) and MXCSR accumulates the detected flags. -/
theorem exec_cvtToIntTrunc_commit {p : Precision} {w : IntWidth} {dst : Reg} {src : XRM}
    {y : Bits p.fmt} (hy : readLane p s memory src = some y)
    (h : (Instr.cvtToIntTrunc p w dst src).exec s memory = .commit t after) :
    t.core.read dst = w.toGpr (Scalar.toInt s.mxcsr p w .towardZero y).value ∧
      t.mxcsr = s.mxcsr.record (Scalar.toIntDetected s.mxcsr p w .towardZero y).all ∧ after =
        memory :=
  finish_writeGpr_commit (by rwa [exec_cvtToIntTrunc hy] at h)


/-- CVTSS2SI/CVTSD2SI (rounding by MXCSR.RC) as `finish` of its profile operation. -/
theorem exec_cvtToInt {p : Precision} {w : IntWidth} {dst : Reg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y) :
    (Instr.cvtToInt p w dst src).exec s memory =
      finish (Instr.cvtToInt p w dst src) s memory
        (Scalar.toIntDetected s.mxcsr p w s.mxcsr.rounding y)
        (fun u => u.writeGpr dst
          (w.toGpr (Scalar.toInt s.mxcsr p w s.mxcsr.rounding y).value)) := by
  simp only [Instr.exec, hy]

/-- CVTSS2SI/CVTSD2SI (rounding by MXCSR.RC) raises a fault exactly when a detected exception is
unmasked; the fault is #XM with the recorded MXCSR. -/
theorem exec_cvtToInt_eq_fault_iff {p : Precision} {w : IntWidth} {dst : Reg} {src : XRM}
    {y : Bits p.fmt} (hy : readLane p s memory src = some y) {f : Fault} :
    (Instr.cvtToInt p w dst src).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.toIntDetected s.mxcsr p w s.mxcsr.rounding y) = true ∧
        f = .simd (s.mxcsr.faultRecord (Scalar.toIntDetected s.mxcsr p w s.mxcsr.rounding y)) := by
  rw [exec_cvtToInt hy, finish_eq_fault_iff]

/-- CVTSS2SI/CVTSD2SI (rounding by MXCSR.RC) on commit: the destination register holds the profile
result (zero-extended from 32 bits for a 32-bit destination) and MXCSR accumulates the detected
flags. -/
theorem exec_cvtToInt_commit {p : Precision} {w : IntWidth} {dst : Reg} {src : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory src = some y)
    (h : (Instr.cvtToInt p w dst src).exec s memory = .commit t after) :
    t.core.read dst = w.toGpr (Scalar.toInt s.mxcsr p w s.mxcsr.rounding y).value ∧
      t.mxcsr = s.mxcsr.record (Scalar.toIntDetected s.mxcsr p w s.mxcsr.rounding y).all ∧ after =
        memory :=
  finish_writeGpr_commit (by rwa [exec_cvtToInt hy] at h)


/-- UCOMISS/UCOMISD as `finish` of its profile operation. -/
theorem exec_ucomi {p : Precision} {a : XReg} {b : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory b = some y) :
    (Instr.ucomi p a b).exec s memory =
      finish (Instr.ucomi p a b) s memory
        (Scalar.compareDetected s.mxcsr p false (lane p (s.readX a)) y)
        (fun u => { u with core := { u.core with
          flags :=
            comisFlags (Scalar.compare s.mxcsr p false (lane p (s.readX a)) y).value } }) := by
  simp only [Instr.exec, hy]

/-- UCOMISS/UCOMISD raises a fault exactly when a detected exception is unmasked; the
fault is #XM with the recorded MXCSR. -/
theorem exec_ucomi_eq_fault_iff {p : Precision} {a : XReg} {b : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory b = some y) {f : Fault} :
    (Instr.ucomi p a b).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.compareDetected s.mxcsr p false (lane p (s.readX a)) y) = true ∧
        f = .simd
          (s.mxcsr.faultRecord
            (Scalar.compareDetected s.mxcsr p false (lane p (s.readX a)) y)) := by
  rw [exec_ucomi hy, finish_eq_fault_iff]

/-- UCOMISS/UCOMISD on commit: the status flags are those of `comisFlags` for the profile comparison
and MXCSR accumulates the detected flags. -/
theorem exec_ucomi_commit {p : Precision} {a : XReg} {b : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory b = some y)
    (h : (Instr.ucomi p a b).exec s memory = .commit t after) :
    t.core.flags = comisFlags (Scalar.compare s.mxcsr p false (lane p (s.readX a)) y).value ∧
      t.mxcsr = s.mxcsr.record
        (Scalar.compareDetected s.mxcsr p false (lane p (s.readX a)) y).all ∧ after = memory :=
  finish_flags_commit (by rwa [exec_ucomi hy] at h)


/-- COMISS/COMISD as `finish` of its profile operation. -/
theorem exec_comi {p : Precision} {a : XReg} {b : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory b = some y) :
    (Instr.comi p a b).exec s memory =
      finish (Instr.comi p a b) s memory
        (Scalar.compareDetected s.mxcsr p true (lane p (s.readX a)) y)
        (fun u => { u with core := { u.core with
          flags :=
            comisFlags (Scalar.compare s.mxcsr p true (lane p (s.readX a)) y).value } }) := by
  simp only [Instr.exec, hy]

/-- COMISS/COMISD raises a fault exactly when a detected exception is unmasked; the
fault is #XM with the recorded MXCSR. -/
theorem exec_comi_eq_fault_iff {p : Precision} {a : XReg} {b : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory b = some y) {f : Fault} :
    (Instr.comi p a b).exec s memory = .fault f ↔
      s.mxcsr.faults (Scalar.compareDetected s.mxcsr p true (lane p (s.readX a)) y) = true ∧
        f = .simd
          (s.mxcsr.faultRecord (Scalar.compareDetected s.mxcsr p true (lane p (s.readX a)) y)) := by
  rw [exec_comi hy, finish_eq_fault_iff]

/-- COMISS/COMISD on commit: the status flags are those of `comisFlags` for the profile comparison
and MXCSR accumulates the detected flags. -/
theorem exec_comi_commit {p : Precision} {a : XReg} {b : XRM} {y : Bits p.fmt}
    (hy : readLane p s memory b = some y)
    (h : (Instr.comi p a b).exec s memory = .commit t after) :
    t.core.flags = comisFlags (Scalar.compare s.mxcsr p true (lane p (s.readX a)) y).value ∧
      t.mxcsr = s.mxcsr.record
        (Scalar.compareDetected s.mxcsr p true (lane p (s.readX a)) y).all ∧ after = memory :=
  finish_flags_commit (by rwa [exec_comi hy] at h)


end PerInstruction

/-! ## Profile facts at the instruction level -/

namespace Scalar

variable (m : MXCSR) (p : Precision)

/-- UCOMIS compares the operands after DAZ with the IEEE comparison. -/
theorem compare_value (signaling : Bool) (x y : Bits p.fmt) :
    (compare m p signaling x y).value =
      (m.profile.flushInput x).value.compare (m.profile.flushInput y).value := rfl

/-- UCOMISS/UCOMISD signal invalid only for signaling NaN operands. -/
theorem compare_flags_quiet (x y : Bits p.fmt) :
    (compare m p false x y).flags =
      if x.isSignalingNaN || y.isSignalingNaN then Numeric.Ieee754.FlagSpec.invalid
      else Numeric.Ieee754.Flags.empty :=
  Numeric.Float.x86_ucomis_flags m.control x y

/-- COMISS/COMISD signal invalid for every NaN operand. -/
theorem compare_flags_signaling (x y : Bits p.fmt) :
    (compare m p true x y).flags =
      if x.isNaN || y.isNaN then Numeric.Ieee754.FlagSpec.invalid
      else Numeric.Ieee754.Flags.empty :=
  Numeric.Float.x86_comis_flags m.control x y

/-- MINSS/MAXSS signal invalid for every NaN operand. -/
theorem minMax_flags (isMax : Bool) (x y : Bits p.fmt) :
    (minMax m p isMax x y).flags =
      if x.isNaN || y.isNaN then Numeric.Ieee754.FlagSpec.invalid
      else Numeric.Ieee754.Flags.empty :=
  Numeric.Float.x86_minMax_flags m.control isMax x y

end Scalar

/-- The x86 "integer indefinite" value: the most negative signed integer
(SDM Vol. 2A, CVTSD2SI: `80000000H`, or `80000000_00000000H` with REX.W). -/
def IntWidth.indefinite : (w : IntWidth) → BitVec w.target.width
  | .w32 => 0x80000000#32
  | .w64 => 0x8000000000000000#64

/-- A float-to-integer conversion that signals invalid returns the integer
indefinite value. -/
theorem Scalar.toInt_value_of_invalid (m : MXCSR) (p : Precision) (w : IntWidth)
    (mode : RoundingMode) (y : Bits p.fmt)
    (h : (Scalar.toInt m p w mode y).flags.invalidOperation = true) :
    (Scalar.toInt m p w mode y).value = w.indefinite := by
  unfold Scalar.toInt MXCSR.profile at *
  rw [Numeric.Float.x86_toInt_of_invalid _ _ _ _ h]
  cases w <;> decide

/-- A 32-bit general-purpose destination is zero-extended. -/
@[simp] theorem IntWidth.toGpr_toNat (w : IntWidth) (x : BitVec w.target.width) :
    (w.toGpr x).toNat = x.toNat := by
  cases w
  · simp only [toGpr, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide))
  · rfl

/-! ## COMIS/UCOMIS status flags -/

/-- Every status flag written by COMIS/UCOMIS is defined: ZF, PF and CF follow
the comparison and OF, SF and AF are zero. -/
theorem comisFlags_eq (c : Option Ordering) :
    comisFlags c =
      { zero := some (decide (c = none ∨ c = some .eq)),
        parity := some (decide (c = none)),
        carry := some (decide (c = none ∨ c = some .lt)),
        overflow := some false, sign := some false, adjust := some false } := by
  rcases c with _ | _ | _ | _ <;> rfl

@[simp] theorem comisFlags_overflow (c : Option Ordering) : (comisFlags c).overflow = some false :=
  by rw [comisFlags_eq]
@[simp] theorem comisFlags_sign (c : Option Ordering) : (comisFlags c).sign = some false := by
  rw [comisFlags_eq]
@[simp] theorem comisFlags_adjust (c : Option Ordering) : (comisFlags c).adjust = some false := by
  rw [comisFlags_eq]

/-- `JA`/`JNBE` (CF = 0 and ZF = 0) after COMIS/UCOMIS: ordered and greater. -/
theorem comisFlags_above (c : Option Ordering) :
    ((comisFlags c).carry = some false ∧ (comisFlags c).zero = some false) ↔ c = some .gt := by
  rcases c with _ | _ | _ | _ <;> decide

/-- `JAE`/`JNB` (CF = 0): ordered and greater or equal. -/
theorem comisFlags_aboveEqual (c : Option Ordering) :
    (comisFlags c).carry = some false ↔ c = some .gt ∨ c = some .eq := by
  rcases c with _ | _ | _ | _ <;> decide

/-- `JB` (CF = 1): less, or unordered. -/
theorem comisFlags_below (c : Option Ordering) :
    (comisFlags c).carry = some true ↔ c = some .lt ∨ c = none := by
  rcases c with _ | _ | _ | _ <;> decide

/-- `JBE` (CF = 1 or ZF = 1): not ordered-and-greater. -/
theorem comisFlags_belowEqual (c : Option Ordering) :
    ((comisFlags c).carry = some true ∨ (comisFlags c).zero = some true) ↔ c ≠ some .gt := by
  rcases c with _ | _ | _ | _ <;> decide

/-- `JE`/`JZ` (ZF = 1): equal, or unordered. -/
theorem comisFlags_zero (c : Option Ordering) :
    (comisFlags c).zero = some true ↔ c = some .eq ∨ c = none := by
  rcases c with _ | _ | _ | _ <;> decide

/-- `JP` (PF = 1): unordered. -/
theorem comisFlags_parity (c : Option Ordering) :
    (comisFlags c).parity = some true ↔ c = none := by
  rcases c with _ | _ | _ | _ <;> decide

/-- ZF = 1 and PF = 0 (the ordered-equality test compilers emit): ordered and
equal. -/
theorem comisFlags_orderedEqual (c : Option Ordering) :
    ((comisFlags c).zero = some true ∧ (comisFlags c).parity = some false) ↔ c = some .eq := by
  rcases c with _ | _ | _ | _ <;> decide

/-! ## Data movement -/

section Moves

variable {s t : State} {memory after : Memory}

@[simp] theorem Mem.addr_advance (m : Mem) (i : Instr) (s : State) :
    m.addr (advance i s) = m.addr s := rfl

/-- MOVSS/MOVSD between registers merge into the destination. -/
theorem exec_movs (p : Precision) (dst src : XReg) :
    (Instr.movs p dst src).exec s memory =
      .commit (advance (.movs p dst src)
        (s.writeX dst (setLane p (s.readX dst) (lane p (s.readX src))))) memory := rfl

/-- MOVAPS/MOVAPD between registers copy all 128 bits. -/
theorem exec_movap (p : Precision) (dst src : XReg) :
    (Instr.movap p dst src).exec s memory =
      .commit (advance (.movap p dst src) (s.writeX dst (s.readX src))) memory := rfl

/-- MOVD/MOVQ into an XMM register. -/
theorem exec_movToX (w : IntWidth) (dst : XReg) (src : Reg) :
    (Instr.movToX w dst src).exec s memory =
      .commit (advance (.movToX w dst src) (s.writeX dst (w.toXmm (s.core.read src)))) memory :=
  rfl

/-- MOVD/MOVQ out of an XMM register. -/
theorem exec_movFromX (w : IntWidth) (dst : Reg) (src : XReg) :
    (Instr.movFromX w dst src).exec s memory =
      .commit (advance (.movFromX w dst src) (s.writeGpr dst (w.ofXmm (s.readX src)))) memory :=
  rfl

/-- The operand width in bits of MOVD (32) and MOVQ (64). -/
def IntWidth.width : IntWidth → Nat
  | .w32 => 32
  | .w64 => 64

/-- MOVD/MOVQ into XMM keep the low `w` bits of the source and zero the rest. -/
theorem IntWidth.getLsbD_toXmm (w : IntWidth) (v : Word) (j : Nat) :
    (w.toXmm v).getLsbD j = (decide (j < w.width) && v.getLsbD j) := by
  cases w
  · simp only [toXmm, width, BitVec.getLsbD_setWidth]
    by_cases h : j < 32
    · simp [h, show j < 128 by omega]
    · simp [h]
  · simp only [toXmm, width, BitVec.getLsbD_setWidth]
    by_cases h : j < 64
    · simp [h, show j < 128 by omega]
    · simp [h, BitVec.getLsbD_of_ge v j (by omega)]

/-- MOVD/MOVQ out of XMM keep the low `w` bits and zero the rest of the
general-purpose register. -/
theorem IntWidth.getLsbD_ofXmm (w : IntWidth) (v : BitVec 128) (j : Nat) :
    (w.ofXmm v).getLsbD j = (decide (j < w.width) && v.getLsbD j) := by
  cases w
  · simp only [ofXmm, width, BitVec.getLsbD_setWidth]
    by_cases h : j < 32
    · simp [h, show j < 64 by omega]
    · simp [h]
  · exact BitVec.getLsbD_setWidth 64 v j

/-- Permissions depend only on the mappings. -/
theorem permitted_of_regions {a b : Memory} (h : b.regions = a.regions) {access : Process.Access}
    {address length : Nat} (hp : a.Permitted access address length) :
    b.Permitted access address length := by
  unfold Memory.Permitted Memory.checkSpan Memory.permits at *
  rw [h]
  exact hp

theorem loadLane_eq_none_iff {p : Precision} {address : Nat} :
    loadLane p memory address = none ↔ memory.readBytes address p.bytes = none := by
  unfold loadLane
  cases h : memory.readBytes address p.bytes with
  | none => simp
  | some bytes =>
    obtain ⟨x, hx⟩ := decodeLane?_isSome p (Memory.readWith_length h)
    simp [hx]

/-- A MOVSS/MOVSD load that succeeds zeroes the destination above the lane. -/
theorem exec_load {p : Precision} {dst : XReg} {m : Mem} {x : Bits p.fmt}
    (hx : loadLane p memory (m.addr s) = some x) :
    (Instr.load p dst m).exec s memory =
      .commit (advance (.load p dst m) (s.writeX dst (zeroLane p x))) memory := by
  simp only [Instr.exec, hx]

/-- A MOVSS/MOVSD load faults exactly when its 4- or 8-byte span is not
readable (not permitted for reading, beyond `2^64`, or not backed). -/
theorem exec_load_eq_fault_iff {p : Precision} {dst : XReg} {m : Mem} {f : Fault} :
    (Instr.load p dst m).exec s memory = .fault f ↔
      memory.readBytes (m.addr s) p.bytes = none ∧ f = .memory := by
  cases hx : loadLane p memory (m.addr s) with
  | none =>
    have hr := loadLane_eq_none_iff.mp hx
    simp only [Instr.exec, hx, Result.fault.injEq, hr, true_and]
    exact eq_comm
  | some x =>
    have hr : memory.readBytes (m.addr s) p.bytes ≠ none := fun e => by
      rw [← loadLane_eq_none_iff, hx] at e; cases e
    simp only [Instr.exec, hx, reduceCtorEq, hr, false_and]

/-- A MOVSS/MOVSD store faults exactly when its span is not writable. -/
theorem exec_store_eq_fault_iff {p : Precision} {dst : Mem} {src : XReg} {f : Fault} :
    (Instr.store p dst src).exec s memory = .fault f ↔
      ¬ memory.Permitted .write (dst.addr s) p.bytes ∧ f = .memory := by
  cases hw : memory.writeBytes (dst.addr s) (encodeLane p (lane p (s.readX src))) with
  | none =>
    have hp : ¬ memory.Permitted .write (dst.addr s) p.bytes := by
      intro hp
      have hc : memory.checkSpan .write (dst.addr s) p.bytes = true := hp
      simp [Memory.writeBytes, length_encodeLane, hc] at hw
    simp only [Instr.exec, hw, Result.fault.injEq, hp, not_false_eq_true, true_and]
    exact eq_comm
  | some after =>
    have hp := Memory.writeBytes_permitted hw
    rw [length_encodeLane] at hp
    simp only [Instr.exec, hw, reduceCtorEq, hp, not_true_eq_false, false_and]

/-- A committed MOVSS/MOVSD store writes exactly the lane's bytes at the
effective address and changes nothing else. -/
theorem exec_store_commit {p : Precision} {dst : Mem} {src : XReg}
    (h : (Instr.store p dst src).exec s memory = .commit t after) :
    t = advance (.store p dst src) s ∧
      memory.writeBytes (dst.addr s) (encodeLane p (lane p (s.readX src))) = some after := by
  simp only [Instr.exec] at h
  split at h
  · cases h
  · rename_i after' hw
    simp only [Result.commit.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hw⟩

/-- Store then load: after a committed MOVSS/MOVSD store, the stored lane can be
loaded back from the same address, provided that span is readable. -/
theorem exec_store_loadLane {p : Precision} {dst : Mem} {src : XReg}
    (h : (Instr.store p dst src).exec s memory = .commit t after)
    (readable : memory.Permitted .read (dst.addr s) p.bytes) :
    loadLane p after (dst.addr s) = some (lane p (s.readX src)) := by
  obtain ⟨-, hw⟩ := exec_store_commit h
  have frame := Memory.writeBytes_writesOnly hw
  have read := Memory.readWith_eq after .read (dst.addr s)
    (encodeLane p (lane p (s.readX src)))
    (by rw [length_encodeLane]; exact permitted_of_regions frame.1 readable)
    (fun index bound => Memory.writeBytes_get hw index bound)
  rw [length_encodeLane] at read
  simp [loadLane, Memory.readBytes, read]

/-- ANDPS etc. with a register source. -/
theorem exec_logic_reg (op : LogicOp) (p : Precision) (dst r : XReg) :
    (Instr.logic op p dst (.reg r)).exec s memory =
      .commit (advance (.logic op p dst (.reg r))
        (s.writeX dst (op.eval (s.readX dst) (s.readX r)))) memory := rfl

/-- ANDPS etc. with a memory source: #GP(0) if the address is not 16-byte
aligned, a memory fault if the 16-byte span is not readable, and otherwise the
128-bit operation. -/
theorem exec_logic_mem (op : LogicOp) (p : Precision) (dst : XReg) (m : Mem) :
    (Instr.logic op p dst (.mem m)).exec s memory =
      if m.addr s % 16 = 0 then
        match load128 memory (m.addr s) with
        | some v => .commit (advance (.logic op p dst (.mem m))
            (s.writeX dst (op.eval (s.readX dst) v))) memory
        | none => .fault .memory
      else .fault .alignment := by
  by_cases h : m.addr s % 16 = 0
  · cases hl : load128 memory (m.addr s) <;> simp [Instr.exec, readPacked, h, hl]
  · simp [Instr.exec, readPacked, h]

/-- LDMXCSR: #GP(0) if a reserved bit is set, otherwise the loaded value
replaces MXCSR, flags included. -/
theorem exec_ldmxcsr {m : Mem} {v : BitVec 32} (hv : load32 memory (m.addr s) = some v) :
    (Instr.ldmxcsr m).exec s memory =
      if (⟨v⟩ : MXCSR).WellFormed then
        .commit (advance (.ldmxcsr m) { s with mxcsr := ⟨v⟩ }) memory
      else .fault .reservedMxcsr := by
  simp only [Instr.exec, hv]

/-- STMXCSR then load: the four stored bytes read back as MXCSR. -/
theorem exec_stmxcsr_load32 {m : Mem} (h : (Instr.stmxcsr m).exec s memory = .commit t after)
    (readable : memory.Permitted .read (m.addr s) 4) :
    t = advance (.stmxcsr m) s ∧ load32 after (m.addr s) = some s.mxcsr.bits := by
  simp only [Instr.exec] at h
  split at h
  · cases h
  · rename_i after' hw
    simp only [Result.commit.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    have frame := Memory.writeBytes_writesOnly hw
    have read := Memory.readWith_eq after' .read (m.addr s) (le32 s.mxcsr.bits)
      (permitted_of_regions frame.1 readable)
      (fun index bound => Memory.writeBytes_get hw index bound)
    simp only [length_le32] at read
    simp [load32, Memory.readBytes, read]

end Moves

/-! ## The reset MXCSR -/

/-- Under the reset MXCSR a scalar ADD/SUB/MUL/DIV never faults: it commits the
default x86 profile's round-to-nearest-even result, and MXCSR accumulates the
detected flags. -/
theorem exec_arith_binary_reset {op : ArithOp} {a : Numeric.Float.ArithOp} {p : Precision}
    {dst : XReg} {src : XRM} {s : State} {memory : Memory} {y : Bits p.fmt}
    (hs : s.mxcsr = MXCSR.reset) (hop : op.kind = .inl a)
    (hy : readLane p s memory src = some y) :
    (Instr.arith op p dst src).exec s memory =
      .commit (advance (.arith op p dst src)
        { (s.writeX dst (setLane p (s.readX dst)
            ((Profile.x86SSE {}).binary p.fmt a .nearestTiesToEven (lane p (s.readX dst)) y).value))
          with mxcsr := (MXCSR.reset.record
            (Scalar.binaryDetected MXCSR.reset p a (lane p (s.readX dst)) y).all) }) memory := by
  rw [exec_arith_binary hop hy, finish_of_allMasked _ _ _ (hs ▸ MXCSR.reset_allMasked)]
  simp only [hs, Scalar.binary, MXCSR.reset_profile, MXCSR.reset_rounding]

end Silmaril.X86.Float
