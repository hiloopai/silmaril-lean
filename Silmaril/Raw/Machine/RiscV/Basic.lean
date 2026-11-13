module

public import Mathlib.Data.BitVec
public import Silmaril.Machine.RegisterFile

/-! # An RV64 integer arithmetic fragment

Adapted from sail-riscv revision 27224ccb2290f022e46213c05b3e72e8a9ea635e.
Upstream copyright notices and BSD-2-Clause terms are retained in
`NOTICES/sail-riscv/LICENCE`.

Proof-friendly, handwritten normalization of Sail's ITYPE, RTYPE, SHIFTIOP,
and UTYPE clauses. This is a decoded, straight-line retirement model: fetching,
traps, privilege, memory, and asynchronous events are outside its scope.
-/

@[expose] public section

namespace Silmaril.RiscV

abbrev Reg := BitVec 5
abbrev Word := BitVec 64

inductive ImmOp where
  | add | slt | sltu | and | or | xor
  deriving DecidableEq, Repr

inductive RegOp where
  | add | sub | slt | sltu | and | or | xor | sll | srl | sra
  deriving DecidableEq, Repr

inductive ShiftOp where
  | sll | srl | sra
  deriving DecidableEq, Repr

inductive UpperOp where
  | lui | auipc
  deriving DecidableEq, Repr

/-- Exactly 21 RV64 base integer operations, all with 32-bit encodings. -/
inductive Instr where
  | imm (op : ImmOp) (rd rs1 : Reg) (value : BitVec 12)
  | reg (op : RegOp) (rd rs1 rs2 : Reg)
  | shift (op : ShiftOp) (rd rs1 : Reg) (amount : BitVec 6)
  | upper (op : UpperOp) (rd : Reg) (value : BitVec 20)
  deriving DecidableEq, Repr

structure State where
  regs : Machine.RegisterFile Reg Word
  pc : Word

namespace State

/-- The backing slot for x0 is unobservable; every architectural read is zero. -/
def read (s : State) (r : Reg) : Word := if r = 0#5 then 0#64 else s.regs r

/-- Writes to x0 are discarded, including its unobservable backing slot. -/
def write (s : State) (r : Reg) (v : Word) : State :=
  if r = 0#5 then s else { s with regs := Machine.RegisterFile.write s.regs r v }

@[simp] theorem read_zero (s : State) : s.read 0#5 = 0#64 := by simp [read]

@[simp] theorem write_zero (s : State) (v : Word) : s.write 0#5 v = s := by simp [write]

@[simp] theorem write_pc (s : State) (r : Reg) (v : Word) :
    (s.write r v).pc = s.pc := by simp [write]; split <;> rfl

@[simp] theorem read_write_same (s : State) (r : Reg) (v : Word) (h : r ≠ 0#5) :
    (s.write r v).read r = v := by simp [write, read, h]

theorem read_write_other (s : State) (r q : Reg) (v : Word) (h : q ≠ r) :
    (s.write r v).read q = s.read q := by
  by_cases hz : r = 0#5 <;> simp [write, read, hz, Machine.RegisterFile.write, h]

end State

def boolWord (b : Bool) : Word := (BitVec.ofBool b).setWidth 64

def ImmOp.eval (op : ImmOp) (x : Word) (imm : BitVec 12) : Word :=
  let y := imm.signExtend 64
  match op with
  | .add => x + y
  | .slt => boolWord (x.slt y)
  | .sltu => boolWord (x.ult y)
  | .and => x &&& y
  | .or => x ||| y
  | .xor => x ^^^ y

def ShiftOp.eval (op : ShiftOp) (x : Word) (amount : BitVec 6) : Word :=
  match op with
  | .sll => x <<< amount.toNat
  | .srl => x >>> amount.toNat
  | .sra => x.sshiftRight amount.toNat

/-- Register shifts use only the low six bits, as required by RV64. -/
def RegOp.eval (op : RegOp) (x y : Word) : Word :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .slt => boolWord (x.slt y)
  | .sltu => boolWord (x.ult y)
  | .and => x &&& y
  | .or => x ||| y
  | .xor => x ^^^ y
  | .sll => ShiftOp.eval .sll x (y.setWidth 6)
  | .srl => ShiftOp.eval .srl x (y.setWidth 6)
  | .sra => ShiftOp.eval .sra x (y.setWidth 6)

/-- LUI sign-extends its 32-bit result even on RV64. -/
def UpperOp.eval (op : UpperOp) (pc : Word) (imm : BitVec 20) : Word :=
  let offset := (imm ++ (0#12)).signExtend 64
  match op with
  | .lui => offset
  | .auipc => pc + offset

def Instr.dest : Instr → Reg
  | .imm _ rd _ _ | .reg _ rd _ _ | .shift _ rd _ _ | .upper _ rd _ => rd

/-- Both operands and AUIPC's address are read from the incoming state. -/
def Instr.value (i : Instr) (s : State) : Word :=
  match i with
  | .imm op _ rs1 immediate => op.eval (s.read rs1) immediate
  | .reg op _ rs1 rs2 => op.eval (s.read rs1) (s.read rs2)
  | .shift op _ rs1 amount => op.eval (s.read rs1) amount
  | .upper op _ immediate => op.eval s.pc immediate

/-- Retirement of one already-decoded instruction with sequential next PC.
This wrapper models the selected Sail clause plus ordinary four-byte PC advance;
it does not assert that instruction fetch or retirement can never trap.
-/
def step (i : Instr) (s : State) : State :=
  { s.write i.dest (i.value s) with pc := s.pc + 4 }

@[simp] theorem step_pc (i : Instr) (s : State) : (step i s).pc = s.pc + 4 := rfl

@[simp] theorem step_read_zero (i : Instr) (s : State) : (step i s).read 0#5 = 0#64 := by
  simp

theorem step_read_dest (i : Instr) (s : State) (h : i.dest ≠ 0#5) :
    (step i s).read i.dest = i.value s := by
  change (s.write i.dest (i.value s)).read i.dest = i.value s
  exact s.read_write_same _ _ h

theorem step_read_other (i : Instr) (s : State) (r : Reg) (h : r ≠ i.dest) :
    (step i s).read r = s.read r := by
  change (s.write i.dest (i.value s)).read r = s.read r
  exact s.read_write_other _ _ _ h

end Silmaril.RiscV
