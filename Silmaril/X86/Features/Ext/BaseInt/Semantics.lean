module

public import Silmaril.X86.Features.Ext.BaseInt.Encoding
public import Silmaril.X86.Features.Extension
public import Silmaril.X86.Ext.Semantics

/-!
# Baseline integer forms: semantics

`exec i length s memory` runs one instruction of the lane on the extended
state, following the Intel SDM instruction pages. Register and memory access
reuse `X86.Ext`: at 32 and 64 bits `Width.readRM`/`writeRM` are `Ext.readRM` and
`Ext.writeRM` (a 32-bit register write zero-extends), at 16 bits
`Ext.readNarrow .w` and `Ext.writeNarrow .w` (bits 63:16 kept). Memory accesses
are little-endian through `Process.Memory`; a failed access is
`Fault.dataFault` with no effect. ADD/OR/AND/SUB/XOR/CMP at 16 bits use
`Ext.AluOp.resultN`/`flagsN`, the formulas of the integer machine.

## Flags

Flags are exact, with the SDM's undefined flags recorded as undefined
(`none`), never fixed to a value; completing them is the flag-oracle
convention's job (`X86FlagChoices.completeFlags`), downstream.

* ADC/SBB: all six flags from the full sum `x + y + CF` (difference
  `x - (y + CF)`): CF is the unsigned carry (borrow), OF the signed overflow,
  AF the carry out of bit 3, and SF, ZF, PF follow the result.
* SHLD/SHRD by a nonzero masked count `c`: CF is the last bit shifted out of
  the destination, SF, ZF and PF follow the result, OF is defined only for
  `c = 1` (a sign change), and AF is undefined. A masked count of zero changes
  no flag.
* BT/BTS/BTR/BTC: CF is the selected bit, ZF is unchanged, and OF, SF, AF and
  PF are undefined.

## What is `unmodeled` (chaos)

The 32/64-bit forms this lane shares with the int-ext lane (`IntExt`) make the
same choices, so that the two lanes agree exactly on their overlap
(`IntMerged/Agree.lean`).

* ADC and SBB read CF. When CF is undefined (`none`) the result depends on an
  undefined flag, and the instruction is `Result.unmodeled`: any continuation
  is allowed, so no choice is made for the flag. With an `r/m` destination CF
  is checked before the destination is read.
* SHLD/SHRD at 16 bits with a masked count above 16: the SDM leaves the
  result and the flags undefined.
* SHLD/SHRD with a masked count of zero and a memory destination: whether the
  processor accesses the operand is not specified.
* BTx with a memory operand and a register bit offset whose access is refused:
  a processor may access less than the operand-size unit.

## Choices where the SDM leaves room

* SHLD/SHRD whose masked count is zero still write their unchanged register
  destination, as `X86.Ext`'s shifts do (a 32-bit register destination is
  zero-extended; measured on an i7-8700 by the int-ext lane).
* BTx with a memory operand and a register bit offset address the operand-size
  unit at `ea + (offset div size) * bytes` (floor division of the signed
  offset), and access that unit only.
* `repz ret` (`F3 C3`) is RET: it pops the return address into RIP and
  retires. An extension cannot report the machine's `returned` outcome, so a
  `repz ret` that pops the designated exit address retires to that address
  instead of returning.
-/

@[expose] public section

namespace Silmaril.X86.Features.BaseInt

open Silmaril.X86 (Reg Word Flags)
open Silmaril.X86.Ext (Sz RM Mem)
open Silmaril.Process (Memory)

/-! ## Operand access -/

namespace Width

/-- The low `sz.bits` bits of a register. -/
def read : (sz : Width) → X86.State → Reg → BitVec sz.bits
  | .w, s, r => (s.read r).setWidth 16
  | .d, s, r => Sz.d.read s r
  | .q, s, r => Sz.q.read s r

/-- A register write at `sz`: 16-bit writes keep bits 63:16, 32-bit writes
zero-extend. -/
def write : (sz : Width) → X86.State → Reg → BitVec sz.bits → X86.State
  | .w, s, r, v => s.write r ((s.read r &&& ~~~(Ext.narrowMask .w)) ||| v.setWidth 64)
  | .d, s, r, v => Sz.d.write s r v
  | .q, s, r, v => Sz.q.write s r v

def readRM : (sz : Width) → RM → X86.State → Memory → Word → Option (BitVec sz.bits)
  | .w, op, s, memory, next => Ext.readNarrow .w op s memory next
  | .d, op, s, memory, next => Ext.readRM .d op s memory next
  | .q, op, s, memory, next => Ext.readRM .q op s memory next

def writeRM : (sz : Width) → RM → BitVec sz.bits → X86.State → Memory → Word →
    Option (X86.State × Memory)
  | .w, op, v, s, memory, next => Ext.writeNarrow .w op v s memory next
  | .d, op, v, s, memory, next => Ext.writeRM .d op v s memory next
  | .q, op, v, s, memory, next => Ext.writeRM .q op v s memory next

/-- Load an operand-size value at an address. -/
def loadAt (sz : Width) (memory : Memory) (address : Word) : Option (BitVec sz.bits) :=
  (Ext.loadN memory address sz.bytes).map fun v => v.setWidth sz.bits

/-- Store an operand-size value at an address. -/
def storeAt (sz : Width) (memory : Memory) (address : Word) (v : BitVec sz.bits) :
    Option Memory :=
  Ext.storeN memory address sz.bytes (v.setWidth 64)

/-- At 32 and 64 bits the accessors are `X86.Ext`'s. -/
theorem readRM_d : Width.d.readRM = Ext.readRM .d := rfl
theorem readRM_q : Width.q.readRM = Ext.readRM .q := rfl
theorem writeRM_d : Width.d.writeRM = Ext.writeRM .d := rfl
theorem writeRM_q : Width.q.writeRM = Ext.writeRM .q := rfl
theorem readRM_w : Width.w.readRM = Ext.readNarrow .w := rfl
theorem writeRM_w : Width.w.writeRM = Ext.writeNarrow .w := rfl

end Width

/-! ## Flags -/

section Flags

variable {n : Nat}

/-- ADC: the flags of `x + y + c`. -/
def adcFlags (x y : BitVec n) (c : Bool) : Flags :=
  let r := x + y + BitVec.ofNat n c.toNat
  { carry := some (decide (2 ^ n ≤ x.toNat + y.toNat + c.toNat))
    parity := some (Ext.parityN r)
    adjust := some ((x ^^^ y ^^^ r).getLsbD 4)
    zero := some (Ext.isZeroN r)
    sign := some r.msb
    overflow := some (decide (r.toInt ≠ x.toInt + y.toInt + (c.toNat : Int))) }

/-- SBB: the flags of `x - (y + c)`. -/
def sbbFlags (x y : BitVec n) (c : Bool) : Flags :=
  let r := x - y - BitVec.ofNat n c.toNat
  { carry := some (decide (x.toNat < y.toNat + c.toNat))
    parity := some (Ext.parityN r)
    adjust := some ((x ^^^ y ^^^ r).getLsbD 4)
    zero := some (Ext.isZeroN r)
    sign := some r.msb
    overflow := some (decide (r.toInt ≠ x.toInt - y.toInt - (c.toNat : Int))) }

/-- The integer machine's operation, for the six operations it has. -/
def Op.toAluOp? : Op → Option X86.AluOp
  | .add => some .add | .or => some .or | .and => some .and | .sub => some .sub
  | .xor => some .xor | .cmp => some .cmp | .adc | .sbb => none

/-- Result and flags of an operation, with the incoming CF. `none` when the
operation reads CF and CF is undefined. -/
def Op.eval (op : Op) (x y : BitVec n) (cf : Option Bool) : Option (BitVec n × Flags) :=
  match op.toAluOp? with
  | some a => some (Ext.AluOp.resultN a x y, Ext.AluOp.flagsN a x y)
  | none =>
    match op with
    | .adc => cf.map fun c => (x + y + BitVec.ofNat n c.toNat, adcFlags x y c)
    | .sbb => cf.map fun c => (x - y - BitVec.ofNat n c.toNat, sbbFlags x y c)
    | _ => none

/-- SHLD (`left`) or SHRD of `x` with fill bits from `y`, by `1 ≤ c ≤ n`. -/
def shdResult (left : Bool) (x y : BitVec n) (c : Nat) : BitVec n :=
  if left then (x <<< c) ||| (y >>> (n - c)) else (x >>> c) ||| (y <<< (n - c))

def shdFlags (left : Bool) (x r : BitVec n) (c : Nat) : Flags :=
  { carry := some (if left then x.getLsbD (n - c) else x.getLsbD (c - 1))
    parity := some (Ext.parityN r)
    adjust := none
    zero := some (Ext.isZeroN r)
    sign := some r.msb
    overflow := if c = 1 then some (r.msb != x.msb) else none }

/-- BTx: CF is the selected bit, ZF unchanged, the others undefined. -/
def btFlags (old : Flags) (b : Bool) : Flags :=
  { carry := some b, parity := none, adjust := none, zero := old.zero, sign := none,
    overflow := none }

/-- The written value of BTS/BTR/BTC; `none` for BT, which does not write. -/
def BtOp.modify (op : BtOp) (x : BitVec n) (k : Nat) : Option (BitVec n) :=
  match op with
  | .bt => none
  | .bts => some (x ||| BitVec.ofNat n (2 ^ k))
  | .btr => some (x &&& ~~~(BitVec.ofNat n (2 ^ k)))
  | .btc => some (x ^^^ BitVec.ofNat n (2 ^ k))

end Flags

/-! ## Execution -/

/-- The outcome on the integer state. -/
inductive Out where
  | ok (t : X86.State) (memory : Memory)
  | dataFault
  | unmodeled

/-- The outcome on the extended state: only the integer part changes. -/
def Out.result (s : State) : Out → Result
  | .ok t memory => .retired (s.setCore t) memory
  | .dataFault => .fault .dataFault
  | .unmodeled => .unmodeled

/-- Finish with RIP set to `next`, or a data fault. -/
def retire (next : Word) (f : Flags) : Option (X86.State × Memory) → Out
  | some (t, memory) => .ok { t with flags := f, rip := next } memory
  | none => .dataFault

/-- ADC and SBB read CF. -/
def Op.readsCarry : Op → Bool
  | .adc | .sbb => true
  | _ => false

/-- `op dst, y` with an `r/m` destination. An undefined CF is checked before
the destination is read, as in `IntExt.carryRM`. -/
def aluStep (sz : Width) (op : Op) (dst : RM) (y : BitVec sz.bits) (s : X86.State)
    (memory : Memory) (next : Word) : Out :=
  if op.readsCarry && s.flags.carry.isNone then .unmodeled else
  match sz.readRM dst s memory next with
  | none => .dataFault
  | some x =>
    match op.eval x y s.flags.carry with
    | none => .unmodeled
    | some (r, f) =>
      if op = .cmp then .ok { s with flags := f, rip := next } memory
      else retire next f (sz.writeRM dst r s memory next)

/-- `op dst, src` with a register destination and an `r/m` source. -/
def aluStepR (sz : Width) (op : Op) (dst : Reg) (src : RM) (s : X86.State) (memory : Memory)
    (next : Word) : Out :=
  match sz.readRM src s memory next with
  | none => .dataFault
  | some y =>
    match op.eval (sz.read s dst) y s.flags.carry with
    | none => .unmodeled
    | some (r, f) =>
      if op = .cmp then .ok { s with flags := f, rip := next } memory
      else .ok { sz.write s dst r with flags := f, rip := next } memory

/-- An ALU form at size `sz`; immediates are sign-extended. -/
def formStep (sz : Width) (op : Op) {k : Nat} (form : AluForm k) (s : X86.State)
    (memory : Memory) (next : Word) : Out :=
  match form with
  | .rm dst src => aluStep sz op dst (sz.read s src) s memory next
  | .r dst src => aluStepR sz op dst src s memory next
  | .i dst v => aluStep sz op dst (v.signExtend sz.bits) s memory next
  | .i8 dst v => aluStep sz op dst (v.signExtend sz.bits) s memory next
  | .a v => aluStep sz op (.reg .rax) (v.signExtend sz.bits) s memory next

/-- The unmasked count. -/
def ShdCount.raw (count : ShdCount) (s : X86.State) : BitVec 8 :=
  match count with
  | .cl => (s.read .rcx).setWidth 8
  | .imm n => n

/-- A memory operand. -/
def isMemOp : RM → Bool
  | .mem _ => true
  | .reg _ => false

/-- SHLD/SHRD. The count is masked to 5 bits (6 with REX.W). -/
def shdStep (sz : Width) (left : Bool) (dst : RM) (src : Reg) (count : ShdCount) (s : X86.State)
    (memory : Memory) (next : Word) : Out :=
  let c := (count.raw s).toNat % (if sz = .q then 64 else 32)
  -- A zero count to memory is chaos before any access (`IntExt` checks it first).
  if c = 0 ∧ isMemOp dst = true then .unmodeled else
  match sz.readRM dst s memory next with
  | none => .dataFault
  | some x =>
    if c = 0 then retire next s.flags (sz.writeRM dst x s memory next)
    else if sz.bits < c then .unmodeled
    else
      let r := shdResult left x (sz.read s src) c
      retire next (shdFlags left x r c) (sz.writeRM dst r s memory next)

/-- BT/BTS/BTR/BTC. -/
def bitStep (sz : Width) (op : BtOp) (dst : RM) (src : BtSrc) (s : X86.State) (memory : Memory)
    (next : Word) : Out :=
  match dst with
  | .reg r =>
    let k := (match src with
      | .reg q => (sz.read s q).toNat
      | .imm n => n.toNat) % sz.bits
    let x := sz.read s r
    let f := btFlags s.flags (x.getLsbD k)
    match op.modify x k with
    | none => .ok { s with flags := f, rip := next } memory
    | some v => .ok { sz.write s r v with flags := f, rip := next } memory
  | .mem m =>
    let ak : Word × Nat := match src with
      | .imm n => (m.addr s next, n.toNat % sz.bits)
      | .reg q =>
        let off := (sz.read s q).toInt
        (m.addr s next + BitVec.ofInt 64 (off / (sz.bits : Int) * (sz.bytes : Int)),
          (off % (sz.bits : Int)).toNat)
    -- A register offset may address beyond the operand, and a processor may
    -- access less than the operand-size unit: a refused access is chaos.
    let refused : Out := match src with
      | .imm _ => .dataFault
      | .reg _ => .unmodeled
    match sz.loadAt memory ak.1 with
    | none => refused
    | some x =>
      let f := btFlags s.flags (x.getLsbD ak.2)
      match op.modify x ak.2 with
      | none => .ok { s with flags := f, rip := next } memory
      | some v =>
        match sz.storeAt memory ak.1 v with
        | none => refused
        | some after => .ok { s with flags := f, rip := next } after

/-- Execute on the integer state, with the consumed length. -/
def execCore (i : Instr) (length : Nat) (s : X86.State) (memory : Memory) : Out :=
  let next := s.rip + BitVec.ofNat 64 length
  match i with
  | .carry sz op form => formStep (Width.ofSz sz) op.toOp form s memory next
  | .alu16 op form => formStep .w op form s memory next
  | .shd sz left dst src count => shdStep sz left dst src count s memory next
  | .bit sz op dst src => bitStep sz op dst src s memory next
  | .pushI v =>
    match X86.pushWord s memory (v.signExtend 64) with
    | none => .dataFault
    | some (t, after) => .ok { t with rip := next } after
  | .pushI8 v =>
    match X86.pushWord s memory (v.signExtend 64) with
    | none => .dataFault
    | some (t, after) => .ok { t with rip := next } after
  | .repRet =>
    match X86.popWord s memory with
    | none => .dataFault
    | some (target, t) => .ok { t with rip := target } memory

/-- Execute on the extended state: the vector, mask, MXCSR and x87 state are
unchanged. -/
def exec (i : Instr) (length : Nat) (s : State) (memory : Memory) : Result :=
  (execCore i length s.core memory).result s

end Silmaril.X86.Features.BaseInt
