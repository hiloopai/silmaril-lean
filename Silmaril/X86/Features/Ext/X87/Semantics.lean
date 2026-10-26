module

public import Silmaril.X86.Features.Extension
public import Silmaril.X86.Features.Ext.X87.Arith
public import Silmaril.X86.Features.Ext.X87.Encoding
public import Silmaril.X86.Ext.Semantics

/-!
# x87 semantics

`exec` gives each `Fpu.Instr` its effect on the extended state `State` (the
`x87` component, and for FNSTSW AX, FCOMI and FCMOVcc the integer registers and
flags) and on memory, written from the SDM (Vol. 1, Chapter 8; Vol. 2, the
instruction pages) and checked against an Intel Core i7-8700
(`scripts/x86-features/gen_x87_vectors.py`).

## The register stack

ST(i) is physical register `TOP + i` (`X87.st`). Each physical register has a
two-bit tag: `00` valid, `01` zero, `10` special (NaN, infinity, denormal,
unsupported), `11` empty (SDM Vol. 1, §8.1.7). Writes set the tag from the
value (`tagOf`), as the processor does, so the full tag word is always the one
FNSTENV/FNSAVE would store. A push decrements TOP and writes the new ST(0); a
pop marks ST(0) empty and increments TOP, leaving the register contents.

## Exceptions

Every computation reports its conditions (`Exc`); `commit` applies the
masking rules of SDM Vol. 1, §8.5 and §8.6:

* stack overflow (push onto a non-empty register) and underflow (an empty
  source) are invalid-operation stack faults: IE and SF, with C1 = 1 for
  overflow and 0 for underflow; masked, the result is the real indefinite;
* if an unmasked invalid, denormal-operand or divide-by-zero condition is
  detected, the destination and TOP are unchanged and only the exception flags,
  ES and B are set (the pre-computation response, §8.6);
* an unmasked overflow or underflow on a register destination delivers a
  result with a biased exponent (§8.5.5, §8.5.6); this is not modelled and the
  instruction is `unmodeled`. With a memory destination (FST) nothing is stored
  and only the status changes;
* otherwise the result is delivered, the flags are OR-ed in and C1 is set when
  the result was rounded up; if an unmasked precision exception was detected
  ES and B are set as well.

An unmasked exception is reported when the *next* waiting x87 instruction
starts: every instruction except FNINIT, FNCLEX, FNSTSW, FNSTCW, FNSTENV and
FNSAVE first checks the status word's ES bit and raises #MF
(`Fault.x87Exception`) with the unchanged status word.

## Not modelled (`unmodeled`)

F2XM1, FYL2X, FYL2XP1, FPTAN, FPATAN, FSIN, FCOS and FSINCOS (whose results are
implementation-specific approximations), FBLD and FBSTP, FNSTENV and FNSAVE
(which store the last-instruction and last-operand pointers, absent from the
state), precision control `01` (reserved), and the biased results of unmasked
overflow and underflow on register destinations. FCMOVcc whose condition reads
an undefined integer flag is `unmodeled` too.

The condition codes the SDM leaves undefined (for example C0, C2, C3 after an
arithmetic instruction) keep their previous values, which is what the
reference processor does on every vector. Where the processor differs from
the SDM's wording or fills an undefined code, the model follows the processor
(each was found by the vectors): a held instruction clears C1, except FCOMI;
FCOM-style and FCOMI-style compares set their codes or flags even when held;
FCOMI (except on underflow) and a non-underflowing FCMOVcc leave C1 unchanged;
FFREE clears C1; FLD ST(i) of an empty register onto a full stack reports
underflow (C1 = 0).
-/

@[expose] public section

namespace Silmaril.X86.Features.Fpu

open Silmaril.X86 (Byte Word)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Mem)

/-! ## Status-word and tag helpers -/

/-- Set bit `i` of a 16-bit word to `b`. -/
def setBit16 (w : BitVec 16) (i : Nat) (b : Bool) : BitVec 16 :=
  if b then w ||| (1#16 <<< i) else w &&& ~~~(1#16 <<< i)

/-- The tag of a value written to a register. -/
def tagOf (v : BitVec 80) : BitVec 2 :=
  match classify v with
  | .zero _ => 1
  | .fin _ _ _ => if isDenormal80 v then 2 else 0
  | _ => 2

namespace X87Ops

open Silmaril.X86.Features (X87)

def physTag (x : X87) (p : Fin 8) : BitVec 2 := x.tag.extractLsb' (2 * p.val) 2

def setPhysTag (x : X87) (p : Fin 8) (t : BitVec 2) : X87 :=
  { x with tag := (x.tag &&& ~~~(3#16 <<< (2 * p.val))) ||| (t.setWidth 16 <<< (2 * p.val)) }

/-- ST(i) is empty. -/
def empty (x : X87) (i : Fin 8) : Bool := physTag x (x.phys i) == 3

/-- Write ST(i), with the tag of the value. -/
def writeSt (x : X87) (i : Fin 8) (v : BitVec 80) : X87 :=
  let p := x.phys i
  setPhysTag { x with regs := fun q => if q = p then v else x.regs q } p (tagOf v)

/-- Push a value. -/
def push (x : X87) (v : BitVec 80) : X87 := writeSt (x.setTop (x.top - 1)) 0 v

/-- Pop: ST(0) becomes empty and TOP is incremented. -/
def pop (x : X87) : X87 := (setPhysTag x (x.phys 0) 3).setTop (x.top + 1)

def setStatus (x : X87) (sw : BitVec 16) : X87 := { x with status := sw }

/-- Set a condition code: C0 is bit 8, C1 bit 9, C2 bit 10, C3 bit 14. -/
def setC (x : X87) (bit : Nat) (b : Bool) : X87 := setStatus x (setBit16 x.status bit b)

def setC1 (x : X87) (b : Bool) : X87 := setC x 9 b

/-- OR in exception flags and set ES and B when one of them is unmasked. -/
def raise (x : X87) (e : Exc) : X87 :=
  let sw := x.status ||| e.bits
  let pending := (sw &&& ~~~x.control &&& 0x3F) != 0
  setStatus x (if pending then sw ||| 0x8080 else sw)

/-- An unmasked pending exception: the status word's ES bit. -/
def pendingMF (x : X87) : Bool := x.status.getLsbD 7

def precision (x : X87) : Option Nat :=
  match x.precisionControl.toNat with
  | 0 => some 24
  | 2 => some 53
  | 3 => some 64
  | _ => none

def rc (x : X87) : RC := RC.ofBits x.roundingControl

def masked (x : X87) (bit : Nat) : Bool := x.control.getLsbD bit

end X87Ops

open X87Ops

/-! ## Disposition of detected conditions -/

/-- What happens to a result after its conditions are detected. -/
inductive Disp where
  /-- Deliver the result. -/
  | deliver
  /-- An unmasked pre-computation condition, or an unmasked overflow/underflow
  with a memory destination: only the status word changes. -/
  | hold
  /-- An unmasked overflow or underflow with a register destination. -/
  | unmodeled

/-- The effective conditions: unmasked underflow is signalled on tininess
alone (SDM Vol. 1, §4.9.1.5). -/
def effective (x : Features.X87) (e : Exc) (tiny : Bool) : Exc :=
  if masked x 4 then e else { e with ue := tiny }

def dispose (x : Features.X87) (e : Exc) (memDest : Bool) : Disp :=
  if (e.ie && !masked x 0) || (e.de && !masked x 1) || (e.ze && !masked x 2) then .hold
  else if (e.oe && !masked x 3) || (e.ue && !masked x 4) then
    if memDest then .hold else .unmodeled
  else .deliver

/-- The exception flags, ES and B after a held instruction: the conditions that
were detected (pre-computation only when one of those is unmasked; for an
unmasked overflow or underflow on a memory destination, without precision,
as observed on hardware). -/
def holdFlags (x : Features.X87) (e : Exc) : Features.X87 :=
  let pre := (e.ie && !masked x 0) || (e.de && !masked x 1) || (e.ze && !masked x 2)
  raise x (if pre then e.pre else { e with pe := false })

/-- The status after a held instruction: `holdFlags` with C1 cleared (observed
on hardware for the held arithmetic, store, FPREM and FCOM forms; FCOMI keeps
C1, see `comiRegs`). -/
def holdStatus (x : Features.X87) (e : Exc) : Features.X87 :=
  setC1 (holdFlags x e) false

/-! ## Results -/

/-- Retire with a new x87 state (and RIP advanced). -/
def retireX (s : State) (length : Nat) (m : Memory) (x : Features.X87) : Result :=
  .retired ((s.setX87 x).advance length) m

/-- The address of a memory operand. -/
def addr (s : State) (length : Nat) (m : Ext.Mem) : Nat :=
  (m.addr s.core (s.rip + BitVec.ofNat 64 length)).toNat

/-- Little-endian bytes to a natural number. -/
def ofLe (bytes : List Byte) : Nat := bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- A natural number as `n` little-endian bytes. -/
def toLe (n : Nat) (v : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (v >>> (8 * i))

def load (s : State) (length : Nat) (mem : Memory) (m : Ext.Mem) (n : Nat) : Option Nat :=
  (mem.readBytes (addr s length m) n).map ofLe

def store (s : State) (length : Nat) (mem : Memory) (m : Ext.Mem) (n : Nat) (v : Nat) :
    Option Memory :=
  mem.writeBytes (addr s length m) (toLe n v)

/-! ## Operand formats -/

def SFmt.bytes : SFmt → Nat | .f32 => 4 | .f64 => 8
def SFmt.p : SFmt → Nat | .f32 => 24 | .f64 => 53
def SFmt.w : SFmt → Nat | .f32 => 8 | .f64 => 11
def SFmt.fmt : SFmt → Fmt | .f32 => .single | .f64 => .double
def SFmt.toF : SFmt → FFmt | .f32 => .f32 | .f64 => .f64
def FFmt.bytes : FFmt → Nat | .f32 => 4 | .f64 => 8 | .f80 => 10
def IFmt.bits : IFmt → Nat | .i16 => 16 | .i32 => 32 | .i64 => 64
def WFmt.toI : WFmt → IFmt | .i16 => .i16 | .i32 => .i32

/-- A memory floating-point operand as a register value, with the
denormal-operand condition of the source format. -/
def ofMem (f : FFmt) (v : Nat) : BitVec 80 × Bool :=
  match f with
  | .f32 => (ofIeee 24 8 v, ieeeDenormal 24 8 v)
  | .f64 => (ofIeee 53 11 v, ieeeDenormal 53 11 v)
  | .f80 => (BitVec.ofNat 80 v, false)

/-! ## Arithmetic -/

def Arith.eval (op : Arith) (p : Nat) (rc : RC) (dst src : BitVec 80) (xde : Bool) : Out :=
  match op with
  | .add => addVals p rc dst src false xde
  | .sub => addVals p rc dst src true xde
  | .subr => addVals p rc src dst true xde
  | .mul => mulVals p rc dst src xde
  | .div => divVals p rc dst src xde
  | .divr => divVals p rc src dst xde

/-- Deliver or hold a register result `o` for ST(`dst`), popping afterwards if
`pop`. -/
def finishReg (s : State) (length : Nat) (mem : Memory) (x : Features.X87) (dst : Fin 8)
    (o : Out) (pop : Bool) : Result :=
  let e := effective x o.exc o.tiny
  match dispose x e false with
  | .hold => retireX s length mem (holdStatus x e)
  | .unmodeled => .unmodeled
  | .deliver =>
    let x := setC1 (raise (writeSt x dst o.value) e) o.c1
    retireX s length mem (if pop then X87Ops.pop x else x)

/-- The stack-underflow response with a register destination. -/
def underflowOut : Out := ⟨indefinite, { ie := true, sf := true }, false, false⟩

/-- A two-operand arithmetic instruction on registers: ST(dst) ← ST(dst) op ST(src). -/
def arithRegs (s : State) (length : Nat) (mem : Memory) (op : Arith) (dst src : Fin 8)
    (pop : Bool) : Result :=
  let x := s.x87
  match precision x with
  | none => .unmodeled
  | some p =>
    let o := if empty x dst || empty x src then underflowOut
      else op.eval p (rc x) (x.st dst) (x.st src) false
    finishReg s length mem x dst o pop

/-- ST(0) ← ST(0) op (memory operand `v`, with denormal-operand condition `vde`). -/
def arithValue (s : State) (length : Nat) (mem : Memory) (op : Arith) (v : BitVec 80)
    (vde : Bool) : Result :=
  let x := s.x87
  match precision x with
  | none => .unmodeled
  | some p =>
    let o := if empty x 0 then underflowOut else op.eval p (rc x) (x.st 0) v vde
    finishReg s length mem x 0 o false

/-- A one-operand instruction on ST(0) with result `f`. -/
def unaryOp (s : State) (length : Nat) (mem : Memory) (f : BitVec 80 → Out) : Result :=
  let x := s.x87
  let o := if empty x 0 then underflowOut else f (x.st 0)
  finishReg s length mem x 0 o false

/-! ## Pushes and loads -/

/-- Push a value with its conditions (`e`, detected on the source). Stack
overflow (ST(7) not empty) is detected first. -/
def pushValue (s : State) (length : Nat) (mem : Memory) (v : BitVec 80) (e : Exc)
    (deHolds : Bool := true) : Result :=
  let x := s.x87
  if !empty x 7 then
    -- a source that already underflowed (FLD ST(i) of an empty register)
    -- reports underflow, C1 = 0, rather than overflow (observed on hardware)
    let c1 := !e.sf
    let e : Exc := { ie := true, sf := true }
    match dispose x e false with
    | .deliver => retireX s length mem (setC1 (raise (push x indefinite) e) c1)
    | _ => retireX s length mem (setC1 (holdStatus x e) c1)
  else
    match dispose x (if deHolds then e else { e with de := false }) false with
    | .deliver => retireX s length mem (setC1 (raise (push x v) e) false)
    | .hold => retireX s length mem (holdStatus x e)
    | .unmodeled => .unmodeled

/-! ## Comparisons -/

/-- Set C3, C2, C0 from a comparison (`none` is unordered) and clear C1. The
codes are set even when an unmasked exception holds the instruction. -/
def setCompare (x : Features.X87) (c : Option Ordering) : X87 :=
  let (c3, c2, c0) : Bool × Bool × Bool := match c with
    | some .gt => (false, false, false)
    | some .lt => (false, false, true)
    | some .eq => (true, false, false)
    | none => (true, true, true)
  setC1 (setC (setC (setC x 14 c3) 10 c2) 8 c0) false

/-- FCOM, FUCOM, FTST, FICOM and their popping forms: compare ST(0) with a
value; `pops` pops 0, 1 or 2 times. -/
def compareWith (s : State) (length : Nat) (mem : Memory) (signaling : Bool) (b : Option (BitVec 80))
    (bde : Bool) (pops : Nat) : Result :=
  let x := s.x87
  let (c, e) : Option Ordering × Exc :=
    match b with
    | none => (none, { ie := true, sf := true })
    | some v => if empty x 0 then (none, { ie := true, sf := true })
      else compareVals signaling (x.st 0) v bde
  match dispose x e false with
  | .deliver =>
    let x := raise (setCompare x c) e
    retireX s length mem (Nat.repeat X87Ops.pop pops x)
  | _ => retireX s length mem (setCompare (holdStatus x e) c)

/-- FCOMI/FUCOMI: compare ST(0) with ST(i) into ZF, PF, CF (OF, SF and AF
cleared), also when an unmasked exception holds the instruction. C1 is
cleared on stack underflow and otherwise left unchanged, delivered or held
(the SDM says "set to 0"; the i7-8700 keeps it). -/
def comiRegs (s : State) (length : Nat) (mem : Memory) (unordered pop : Bool) (i : Fin 8) :
    Result :=
  let x := s.x87
  let (c, e) : Option Ordering × Exc :=
    if empty x 0 || empty x i then (none, { ie := true, sf := true })
    else compareVals (!unordered) (x.st 0) (x.st i)
  let (zf, pf, cf) : Bool × Bool × Bool := match c with
    | some .gt => (false, false, false)
    | some .lt => (false, false, true)
    | some .eq => (true, false, false)
    | none => (true, true, true)
  let flags : X86.Flags := ⟨some cf, some pf, some false, some zf, some false, some false⟩
  let s := s.setCore { s.core with flags }
  let c1 : Features.X87 → Features.X87 := fun x => if e.sf then setC1 x false else x
  match dispose x e false with
  | .deliver =>
    let x := c1 (raise x e)
    retireX s length mem (if pop then X87Ops.pop x else x)
  | _ => retireX s length mem (c1 (holdFlags x e))

/-! ## Stores -/

/-- Store ST(0) to memory as an IEEE single or double, or as an 80-bit value. -/
def storeFloat (s : State) (length : Nat) (mem : Memory) (f : FFmt) (m : Ext.Mem) (pop : Bool) :
    Result :=
  let x := s.x87
  let r : IOut :=
    if empty x 0 then
      match f with
      | .f32 => ⟨ieeeIndefinite 24 8, { ie := true, sf := true }, false, false⟩
      | .f64 => ⟨ieeeIndefinite 53 11, { ie := true, sf := true }, false, false⟩
      | .f80 => ⟨indefinite.toNat, { ie := true, sf := true }, false, false⟩
    else
      match f with
      | .f32 => toIeee .single 8 (rc x) (x.st 0)
      | .f64 => toIeee .double 11 (rc x) (x.st 0)
      | .f80 => ⟨(x.st 0).toNat, {}, false, false⟩
  let e := effective x r.exc r.tiny
  match dispose x e true with
  | .deliver =>
    match store s length mem m f.bytes r.bits with
    | some mem' =>
      let x := setC1 (raise x e) r.c1
      retireX s length mem' (if pop then X87Ops.pop x else x)
    | none => .fault .dataFault
  | _ => retireX s length mem (holdStatus x e)

/-- Store ST(0) as an `n`-bit integer, rounding in direction `rc`. -/
def storeInt (s : State) (length : Nat) (mem : Memory) (f : IFmt) (rcv : RC) (m : Ext.Mem)
    (pop : Bool) : Result :=
  let x := s.x87
  let (v, e, c1) : Nat × Exc × Bool :=
    if empty x 0 then (2 ^ (f.bits - 1), { ie := true, sf := true }, false)
    else toInt f.bits rcv (x.st 0)
  match dispose x e true with
  | .deliver =>
    match store s length mem m (f.bits / 8) v with
    | some mem' =>
      let x := setC1 (raise x e) c1
      retireX s length mem' (if pop then X87Ops.pop x else x)
    | none => .fault .dataFault
  | _ => retireX s length mem (holdStatus x e)

/-! ## Environment -/

/-- The control word as stored: bit 6 reads as 1 and bits 15:13 as 0. -/
def normControl (v : Nat) : BitVec 16 := (BitVec.ofNat 16 v &&& 0x1F3F) ||| 0x40

/-- Load control, status and tag words (FLDENV/FRSTOR): only the empty/non-empty
part of each tag is kept, the rest follows the register contents. -/
def loadEnv (x : Features.X87) (cw sw tw : Nat) : Features.X87 :=
  let x := { x with control := normControl cw, status := BitVec.ofNat 16 sw }
  let twb := BitVec.ofNat 16 tw
  { x with tag := (List.range 8).foldl (fun acc p =>
      let t : BitVec 2 :=
        if twb.extractLsb' (2 * p) 2 = 3 then 3 else tagOf (x.regs ⟨p % 8, Nat.mod_lt _ (by decide)⟩)
      (acc &&& ~~~(3#16 <<< (2 * p))) ||| (t.setWidth 16 <<< (2 * p))) 0 }

/-! ## Execution -/

/-- The flag a condition reads, if defined. -/
def Cond.eval (c : Cond) (f : X86.Flags) : Option Bool :=
  match c with
  | .b => f.carry
  | .e => f.zero
  | .be => do let c ← f.carry; let z ← f.zero; pure (c || z)
  | .u => f.parity
  | .nb => f.carry.map (!·)
  | .ne => f.zero.map (!·)
  | .nbe => do let c ← f.carry; let z ← f.zero; pure (!(c || z))
  | .nu => f.parity.map (!·)

/-- Whether an instruction first checks for a pending unmasked exception. -/
def Instr.waits : Instr → Bool
  | .fnstcw _ | .fnstsw _ | .fnstenv _ | .fnsave _ => false
  | .nullary .fnclex | .nullary .fninit | .nullary .fnstswAx => false
  | _ => true

/-- The semantics of one instruction, after the pending-exception check. -/
def execBody (i : Instr) (length : Nat) (s : State) (mem : Memory) : Result :=
  let x := s.x87
  match i with
  | .fld f m =>
    match load s length mem m f.bytes with
    | none => .fault .dataFault
    | some v =>
      let (r, de) := ofMem f v
      let e : Exc := if f = .f80 then {} else { ie := isSNaN80 r, de := de && !isNaN80 r }
      -- an unmasked denormal operand does not hold FLD m32fp/m64fp: the value is
      -- pushed and DE, ES and B are set (observed on hardware)
      pushValue s length mem (if f = .f80 then r else quiet80OfSNaN r) e (deHolds := false)
  | .fst f m => storeFloat s length mem f.toF m false
  | .fstp f m => storeFloat s length mem f m true
  | .fild f m =>
    match load s length mem m (f.bits / 8) with
    | none => .fault .dataFault
    | some v => pushValue s length mem (ofInt f.bits v) {}
  | .fist f m => storeInt s length mem f.toI (rc x) m false
  | .fistp f m => storeInt s length mem f (rc x) m true
  | .fisttp f m => storeInt s length mem f .zero m true
  | .arithMem op f m =>
    match load s length mem m f.bytes with
    | none => .fault .dataFault
    | some v =>
      let (r, de) := ofMem f.toF v
      arithValue s length mem op r de
  | .arithInt op f m =>
    match load s length mem m (f.toI.bits / 8) with
    | none => .fault .dataFault
    | some v => arithValue s length mem op (ofInt f.toI.bits v) false
  | .comMem f pop m =>
    match load s length mem m f.bytes with
    | none => .fault .dataFault
    | some v =>
      let (r, de) := ofMem f.toF v
      compareWith s length mem true (some r) de (if pop then 1 else 0)
  | .comInt f pop m =>
    match load s length mem m (f.toI.bits / 8) with
    | none => .fault .dataFault
    | some v => compareWith s length mem true (some (ofInt f.toI.bits v)) false (if pop then 1 else 0)
  | .arithSt0 op i => arithRegs s length mem op 0 i false
  | .arithSti op i pop => arithRegs s length mem op i 0 pop
  | .fldSt i =>
    if empty x i then pushValue s length mem indefinite { ie := true, sf := true }
    else pushValue s length mem (x.st i) {}
  | .fstSt i pop =>
    let o : Out := if empty x 0 then underflowOut else ⟨x.st 0, {}, false, false⟩
    finishReg s length mem x i o pop
  | .fxch i =>
    let e : Exc := if empty x 0 || empty x i then { ie := true, sf := true } else {}
    match dispose x e false with
    | .deliver =>
      let a := if empty x 0 then indefinite else x.st 0
      let b := if empty x i then indefinite else x.st i
      retireX s length mem (setC1 (raise (writeSt (writeSt x 0 b) i a) e) false)
    | _ => retireX s length mem (holdStatus x e)
  | .ffree i => retireX s length mem (setC1 (setPhysTag x (x.phys i) 3) false)
  | .fcom i pop =>
    compareWith s length mem true (if empty x i then none else some (x.st i)) false
      (if pop then 1 else 0)
  | .fucom i pop =>
    compareWith s length mem false (if empty x i then none else some (x.st i)) false
      (if pop then 1 else 0)
  | .fcomi u pop i => comiRegs s length mem u pop i
  | .fcmov c i =>
    match c.eval s.core.flags with
    | none => .unmodeled
    | some cond =>
      if empty x 0 || empty x i then
        finishReg s length mem x 0 underflowOut false
      -- C1 is left unchanged when nothing underflows (observed on hardware)
      else if cond then retireX s length mem (writeSt x 0 (x.st i))
      else retireX s length mem x
  | .fldcw m =>
    match load s length mem m 2 with
    | none => .fault .dataFault
    | some v => retireX s length mem (raise { x with control := normControl v } {})
  | .fnstcw m =>
    match store s length mem m 2 x.control.toNat with
    | none => .fault .dataFault
    | some mem' => retireX s length mem' x
  | .fnstsw m =>
    match store s length mem m 2 x.status.toNat with
    | none => .fault .dataFault
    | some mem' => retireX s length mem' x
  | .fldenv m =>
    match load s length mem m 28 with
    | none => .fault .dataFault
    | some v =>
      retireX s length mem (loadEnv x (v % 2 ^ 16) ((v >>> 32) % 2 ^ 16) ((v >>> 64) % 2 ^ 16))
  | .frstor m =>
    match load s length mem m 108 with
    | none => .fault .dataFault
    | some v =>
      let sw := (v >>> 32) % 2 ^ 16
      let top := (sw >>> 11) % 8
      let regs : Fin 8 → BitVec 80 := fun p =>
        BitVec.ofNat 80 (v >>> (224 + 80 * ((p.val + 8 - top) % 8)))
      retireX s length mem (loadEnv { x with regs } (v % 2 ^ 16) sw ((v >>> 64) % 2 ^ 16))
  | .fnstenv _ | .fnsave _ | .fbld _ | .fbstp _ => .unmodeled
  | .nullary op =>
    match op with
    | .fnop | .fwait => retireX s length mem x
    | .fchs => unaryOp s length mem fun v => ⟨v ^^^ (1#80 <<< 79), {}, false, false⟩
    | .fabs => unaryOp s length mem fun v => ⟨v &&& ~~~(1#80 <<< 79), {}, false, false⟩
    | .ftst => compareWith s length mem true (some (zero80 false)) false 0
    | .fxam =>
      let v := x.st 0
      let (c3, c2, c0) : Bool × Bool × Bool :=
        if empty x 0 then (true, false, true)
        else match classify v with
          | .unsupported => (false, false, false)
          | .nan _ => (false, false, true)
          | .fin _ _ _ => if isDenormal80 v then (true, true, false) else (false, true, false)
          | .inf _ => (false, true, true)
          | .zero _ => (true, false, false)
      retireX s length mem (setC1 (setC (setC (setC x 14 c3) 10 c2) 8 c0) (sign80 v))
    | .fld1 => pushValue s length mem (constVal (rc x) 0) {}
    | .fldl2t => pushValue s length mem (constVal (rc x) 1) {}
    | .fldl2e => pushValue s length mem (constVal (rc x) 2) {}
    | .fldpi => pushValue s length mem (constVal (rc x) 3) {}
    | .fldlg2 => pushValue s length mem (constVal (rc x) 4) {}
    | .fldln2 => pushValue s length mem (constVal (rc x) 5) {}
    | .fldz => pushValue s length mem (zero80 false) {}
    | .fsqrt =>
      match precision x with
      | none => .unmodeled
      | some p => unaryOp s length mem (sqrtVal p (rc x))
    | .frndint => unaryOp s length mem (roundIntVal (rc x))
    | .fscale =>
      let o := if empty x 0 || empty x 1 then underflowOut else FSCALE (rc x) (x.st 0) (x.st 1)
      finishReg s length mem x 0 o false
    | .fxtract =>
      if empty x 0 then
        -- ST(0) becomes the indefinite, then the indefinite is pushed
        let e : Exc := { ie := true, sf := true }
        match dispose x e false with
        | .deliver => retireX s length mem (setC1 (raise (push (writeSt x 0 indefinite) indefinite) e) false)
        | _ => retireX s length mem (holdStatus x e)
      else if !empty x 7 then
        let e : Exc := { ie := true, sf := true }
        match dispose x e false with
        | .deliver => retireX s length mem (setC1 (raise (push (writeSt x 0 indefinite) indefinite) e) true)
        | _ => retireX s length mem (setC1 (holdStatus x e) true)
      else
        let (ex, sg, e) := xtractVal (x.st 0)
        match dispose x e false with
        | .deliver => retireX s length mem (setC1 (raise (push (writeSt x 0 ex) sg) e) false)
        | .hold => retireX s length mem (holdStatus x e)
        | .unmodeled => .unmodeled
    | .fprem | .fprem1 =>
      let r : PremOut := if empty x 0 || empty x 1 then
          ⟨indefinite, { ie := true, sf := true }, none, some false, some false, none⟩
        else premVal (op == .fprem1) (x.st 0) (x.st 1)
      -- the remainder is exact, so only an unmasked underflow sees a denormal
      -- remainder (then the result is biased: unmodeled)
      let e := effective x r.exc (isDenormal80 r.value)
      match dispose x e false with
      | .deliver =>
        let upd : Features.X87 → Nat → Option Bool → Features.X87 := fun x b c =>
          match c with | some v => setC x b v | none => x
        let x := raise (writeSt x 0 r.value) e
        retireX s length mem (upd (upd (upd (upd x 8 r.c0) 9 r.c1) 10 r.c2) 14 r.c3)
      -- held, FPREM also clears C2 (observed on hardware)
      | .hold => retireX s length mem (setC (holdStatus x e) 10 false)
      | .unmodeled => .unmodeled
    | .fdecstp => retireX s length mem (setC1 (x.setTop (x.top - 1)) false)
    | .fincstp => retireX s length mem (setC1 (x.setTop (x.top + 1)) false)
    | .fcompp =>
      compareWith s length mem true (if empty x 1 then none else some (x.st 1)) false 2
    | .fucompp =>
      compareWith s length mem false (if empty x 1 then none else some (x.st 1)) false 2
    | .fnclex => retireX s length mem (setStatus x (x.status &&& 0x7F00))
    | .fninit => retireX s length mem x.init
    | .fnstswAx =>
      let rax := s.core.read .rax
      let s := s.setCore (s.core.write .rax ((rax &&& ~~~0xFFFF#64) ||| x.status.setWidth 64))
      retireX s length mem x
    | .f2xm1 | .fyl2x | .fptan | .fpatan | .fyl2xp1 | .fsincos | .fsin | .fcos => .unmodeled
where
  quiet80OfSNaN (r : BitVec 80) : BitVec 80 := if isSNaN80 r then quiet80 r else r

/-- The semantics of an x87 instruction of `length` bytes. -/
def exec (i : Instr) (length : Nat) (s : State) (mem : Memory) : Result :=
  if i.waits && pendingMF s.x87 then .fault (.x87Exception s.x87.status)
  else execBody i length s mem

end Silmaril.X86.Features.Fpu
