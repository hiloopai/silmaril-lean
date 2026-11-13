module

public import Silmaril.Machine.RiscV.Basic.Defs
/-! # An extended RV64 instruction language

A superset of the 21-instruction arithmetic fragment `RiscV.Instr`, written
from the RISC-V unprivileged specification (RV64I base, M extension) for use
as a code-generation target. It adds:

* the RV64I word forms `ADDIW`, `SLLIW`, `SRLIW`, `SRAIW`, `ADDW`, `SUBW`,
  `SLLW`, `SRLW`, `SRAW`, which operate on the low 32 bits and sign-extend
  the 32-bit result;
* the M extension: `MUL`, `MULH`, `MULHSU`, `MULHU`, `DIV`, `DIVU`, `REM`,
  `REMU`, `MULW`, `DIVW`, `DIVUW`, `REMW`, `REMUW`;
* loads `LB LH LW LD LBU LHU LWU` and stores `SB SH SW SD` with 12-bit offsets;
* conditional branches `BEQ BNE BLT BGE BLTU BGEU`, `JAL`, `JALR`;
* `EBREAK`, used as a stop instruction.

Register-only instructions are collected in `Compute`, whose semantics is a
total function of the register state and PC. Their meaning for the base
fragment is exactly `RiscV.step` (`Compute.step_base`). Memory, control flow,
alignment faults and `EBREAK` are given meaning by `Ext.MState.step` in
`Silmaril.RiscV.Ext.Machine`.

RISC-V division never traps. The M-extension results for a zero divisor and
for signed overflow (`-2^(XLEN-1) / -1`) are fixed by the specification and
are stated as theorems below (`divS_zero`, `divS_overflow`, and so on).

Branch and `JAL` offsets are always even, so the instruction stores only bits
`12:1` (respectively `20:1`) of the byte offset; `branchOffset` and
`jalOffset` recover the sign-extended byte offset. This keeps every
`Instr` value encodable, so the codec is an exact round trip.

This is a handwritten local model. It is not proved to correspond to the
generated Sail model except where the Sail correspondence module (not in this repository: it needs the `riscv-zkvm` package) says so.
-/

@[expose] public section

namespace Silmaril.RiscV.Ext

/-! ## Operation vocabularies -/

/-- The low 32 bits of a register value. -/
def low32 (x : Word) : BitVec 32 := x.setWidth 32

/-- Sign-extension of a 32-bit result, as written by every RV64 `*W` instruction. -/
def sext32 (v : BitVec 32) : Word := v.signExtend 64

@[simp] theorem low32_sext32 (v : BitVec 32) : low32 (sext32 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i < 64 := by omega
  simp only [low32, sext32, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, this]

/-- Register-register word operations, opcode `OP-32`. -/
inductive RegWOp where
  | add | sub | sll | srl | sra
  deriving DecidableEq, Repr

/-- Full-width M-extension operations, opcode `OP` with `funct7 = 1`. -/
inductive MulOp where
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  deriving DecidableEq, Repr

/-- Word-width M-extension operations, opcode `OP-32` with `funct7 = 1`. -/
inductive MulWOp where
  | mulw | divw | divuw | remw | remuw
  deriving DecidableEq, Repr

inductive LoadOp where
  | lb | lh | lw | ld | lbu | lhu | lwu
  deriving DecidableEq, Repr

inductive StoreOp where
  | sb | sh | sw | sd
  deriving DecidableEq, Repr

inductive BranchOp where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr

/-! ## Division and multiplication as specified by the M extension -/

section Division

variable {w : Nat}

/-- Signed division rounding toward zero. A zero divisor gives all ones (`-1`);
`intMin / -1` gives `intMin` (`divS_overflow`), as the specification requires. -/
def divS (a b : BitVec w) : BitVec w := if b = 0#w then BitVec.allOnes w else a.sdiv b

/-- Unsigned division. A zero divisor gives all ones (`2^w - 1`). -/
def divU (a b : BitVec w) : BitVec w := if b = 0#w then BitVec.allOnes w else a / b

/-- Signed remainder with the sign of the dividend. A zero divisor gives the
dividend; `intMin % -1` gives zero (`remS_overflow`). -/
def remS (a b : BitVec w) : BitVec w := if b = 0#w then a else a.srem b

/-- Unsigned remainder. A zero divisor gives the dividend. -/
def remU (a b : BitVec w) : BitVec w := if b = 0#w then a else a % b

@[simp] theorem divS_zero (a : BitVec w) : divS a 0#w = BitVec.allOnes w := by simp [divS]
@[simp] theorem divU_zero (a : BitVec w) : divU a 0#w = BitVec.allOnes w := by simp [divU]
@[simp] theorem remS_zero (a : BitVec w) : remS a 0#w = a := by simp [remS]
@[simp] theorem remU_zero (a : BitVec w) : remU a 0#w = a := by simp [remU]

theorem divS_of_ne_zero (a : BitVec w) {b : BitVec w} (h : b ≠ 0#w) : divS a b = a.sdiv b := by
  simp [divS, h]

theorem divU_of_ne_zero (a : BitVec w) {b : BitVec w} (h : b ≠ 0#w) : divU a b = a / b := by
  simp [divU, h]

theorem remS_of_ne_zero (a : BitVec w) {b : BitVec w} (h : b ≠ 0#w) : remS a b = a.srem b := by
  simp [remS, h]

theorem remU_of_ne_zero (a : BitVec w) {b : BitVec w} (h : b ≠ 0#w) : remU a b = a % b := by
  simp [remU, h]

/-- `remU` agrees with `%` for every divisor, because `BitVec` already returns
the dividend for a zero modulus. -/
theorem remU_eq_umod (a b : BitVec w) : remU a b = a % b := by
  by_cases h : b = 0#w
  · subst h; simp [remU]
  · exact remU_of_ne_zero a h

private theorem neg_one_ne_zero (hw : 0 < w) : (-1#w) ≠ 0#w := by
  rw [BitVec.neg_one_eq_allOnes]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.zero_mod] at this
  have : 2 ≤ 2 ^ w := Nat.pow_one 2 ▸ (Nat.pow_le_pow_iff_right (by omega)).2 (by omega)
  omega

/-- Signed overflow: `-2^(w-1) / -1` is `-2^(w-1)`. -/
theorem divS_overflow (hw : 0 < w) : divS (BitVec.intMin w) (-1#w) = BitVec.intMin w := by
  rw [divS_of_ne_zero _ (neg_one_ne_zero hw), BitVec.intMin_sdiv_neg_one]

/-- Signed overflow: `-2^(w-1) % -1` is zero. -/
theorem remS_overflow (hw : 0 < w) : remS (BitVec.intMin w) (-1#w) = 0#w := by
  rw [remS_of_ne_zero _ (neg_one_ne_zero hw)]
  apply BitVec.srem_zero_of_dvd
  rw [BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes, ite_eq_left hw]
  exact ⟨-(BitVec.intMin w).toInt, by rw [Int.neg_one_mul, Int.neg_neg]⟩

/-- Away from a zero divisor, the signed quotient is the truncated integer
quotient reduced to `w` bits (this includes the overflow case). -/
theorem toInt_divS (a : BitVec w) {b : BitVec w} (h : b ≠ 0#w) :
    (divS a b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ w) := by
  rw [divS_of_ne_zero a h, BitVec.toInt_sdiv]

end Division

/-- High 64 bits of the signed × signed 128-bit product. -/
def mulHigh (a b : Word) : Word := ((a.signExtend 128 * b.signExtend 128) >>> 64).setWidth 64

/-- High 64 bits of the signed × unsigned 128-bit product. -/
def mulHighSU (a b : Word) : Word := ((a.signExtend 128 * b.setWidth 128) >>> 64).setWidth 64

/-- High 64 bits of the unsigned × unsigned 128-bit product. -/
def mulHighU (a b : Word) : Word := ((a.setWidth 128 * b.setWidth 128) >>> 64).setWidth 64

/-! ## Evaluation of register operations -/

/-- Shifts by the low five bits of the amount on the low 32 bits, then sign-extends. -/
def evalShiftW (op : ShiftOp) (x : Word) (amount : BitVec 5) : Word :=
  match op with
  | .sll => sext32 (low32 x <<< amount.toNat)
  | .srl => sext32 (low32 x >>> amount.toNat)
  | .sra => sext32 ((low32 x).sshiftRight amount.toNat)

def RegWOp.eval (op : RegWOp) (x y : Word) : Word :=
  match op with
  | .add => sext32 (low32 x + low32 y)
  | .sub => sext32 (low32 x - low32 y)
  | .sll => evalShiftW .sll x (y.setWidth 5)
  | .srl => evalShiftW .srl x (y.setWidth 5)
  | .sra => evalShiftW .sra x (y.setWidth 5)

def MulOp.eval (op : MulOp) (x y : Word) : Word :=
  match op with
  | .mul => x * y
  | .mulh => mulHigh x y
  | .mulhsu => mulHighSU x y
  | .mulhu => mulHighU x y
  | .div => divS x y
  | .divu => divU x y
  | .rem => remS x y
  | .remu => remU x y

/-- Word forms operate on the low 32 bits and sign-extend the 32-bit result,
including `DIVUW` and `REMUW`. -/
def MulWOp.eval (op : MulWOp) (x y : Word) : Word :=
  match op with
  | .mulw => sext32 (low32 x * low32 y)
  | .divw => sext32 (divS (low32 x) (low32 y))
  | .divuw => sext32 (divU (low32 x) (low32 y))
  | .remw => sext32 (remS (low32 x) (low32 y))
  | .remuw => sext32 (remU (low32 x) (low32 y))

def BranchOp.eval (op : BranchOp) (x y : Word) : Bool :=
  match op with
  | .eq => x == y
  | .ne => x != y
  | .lt => x.slt y
  | .ge => !x.slt y
  | .ltu => x.ult y
  | .geu => !x.ult y

/-- Access width in bytes. -/
def LoadOp.width : LoadOp → Nat
  | .lb | .lbu => 1
  | .lh | .lhu => 2
  | .lw | .lwu => 4
  | .ld => 8

/-- Whether the loaded value is sign-extended. `LD` loads a full register. -/
def LoadOp.signed : LoadOp → Bool
  | .lb | .lh | .lw => true
  | .lbu | .lhu | .lwu | .ld => false

def StoreOp.width : StoreOp → Nat
  | .sb => 1
  | .sh => 2
  | .sw => 4
  | .sd => 8

/-- The sign-extended byte offset of a branch whose instruction stores bits `12:1`. -/
def branchOffset (half : BitVec 12) : Word := (half ++ 0#1).signExtend 64

/-- The sign-extended byte offset of a `JAL` whose instruction stores bits `20:1`. -/
def jalOffset (half : BitVec 20) : Word := (half ++ 0#1).signExtend 64

/-- An even 13-bit byte offset is represented by its bits `12:1`. -/
theorem branchOffset_of_even (offset : BitVec 13) (even : offset.getLsbD 0 = false) :
    branchOffset (offset.extractLsb' 1 12) = offset.signExtend 64 := by
  have : offset.extractLsb' 1 12 ++ 0#1 = offset := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_append]
    by_cases h0 : i < 1
    · have : i = 0 := by omega
      subst this; simpa using even
    · simp only [h0, ↓reduceIte, BitVec.getLsbD_extractLsb']
      have : i - 1 < 12 := by omega
      simp only [this, decide_true, Bool.true_and]
      congr 1; omega
  simp [branchOffset, this]

theorem jalOffset_of_even (offset : BitVec 21) (even : offset.getLsbD 0 = false) :
    jalOffset (offset.extractLsb' 1 20) = offset.signExtend 64 := by
  have : offset.extractLsb' 1 20 ++ 0#1 = offset := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_append]
    by_cases h0 : i < 1
    · have : i = 0 := by omega
      subst this; simpa using even
    · simp only [h0, ↓reduceIte, BitVec.getLsbD_extractLsb']
      have : i - 1 < 20 := by omega
      simp only [this, decide_true, Bool.true_and]
      congr 1; omega
  simp [jalOffset, this]

/-! ## Instructions -/

/-- Register-only instructions: a total function of registers and PC, with a
sequential four-byte PC advance. -/
inductive Compute where
  /-- The existing 21-instruction arithmetic fragment, unchanged. -/
  | base (instr : RiscV.Instr)
  | addiw (rd rs1 : Reg) (imm : BitVec 12)
  | shiftW (op : ShiftOp) (rd rs1 : Reg) (amount : BitVec 5)
  | regW (op : RegWOp) (rd rs1 rs2 : Reg)
  | mulDiv (op : MulOp) (rd rs1 rs2 : Reg)
  | mulDivW (op : MulWOp) (rd rs1 rs2 : Reg)
  deriving DecidableEq, Repr

inductive Instr where
  | compute (c : Compute)
  /-- `rd := extend(mem[rs1 + sext(offset)])`. -/
  | load (op : LoadOp) (rd rs1 : Reg) (offset : BitVec 12)
  /-- `mem[rs1 + sext(offset)] := low bytes of rs2`. -/
  | store (op : StoreOp) (rs1 rs2 : Reg) (offset : BitVec 12)
  /-- Conditional branch to `pc + branchOffset half`. -/
  | branch (op : BranchOp) (rs1 rs2 : Reg) (half : BitVec 12)
  /-- `rd := pc + 4; pc := pc + jalOffset half`. -/
  | jal (rd : Reg) (half : BitVec 20)
  /-- `rd := pc + 4; pc := (rs1 + sext(offset)) with bit 0 cleared`. -/
  | jalr (rd rs1 : Reg) (offset : BitVec 12)
  /-- A breakpoint, used by this model as a stop instruction. -/
  | ebreak
  deriving DecidableEq, Repr

/-- The embedding of the existing arithmetic fragment. -/
abbrev Instr.ofBase (instr : RiscV.Instr) : Instr := .compute (.base instr)

theorem Instr.ofBase_injective : Function.Injective Instr.ofBase := by
  intro a b h
  cases h
  rfl

namespace Compute

def dest : Compute → Reg
  | .base instr => instr.dest
  | .addiw rd _ _ | .shiftW _ rd _ _ | .regW _ rd _ _ | .mulDiv _ rd _ _
  | .mulDivW _ rd _ _ => rd

/-- The destination value; operands and the PC are read from the incoming state. -/
def value (c : Compute) (s : State) : Word :=
  match c with
  | .base instr => instr.value s
  | .addiw _ rs1 imm => sext32 (low32 (s.read rs1) + imm.signExtend 32)
  | .shiftW op _ rs1 amount => evalShiftW op (s.read rs1) amount
  | .regW op _ rs1 rs2 => op.eval (s.read rs1) (s.read rs2)
  | .mulDiv op _ rs1 rs2 => op.eval (s.read rs1) (s.read rs2)
  | .mulDivW op _ rs1 rs2 => op.eval (s.read rs1) (s.read rs2)

/-- Retirement with sequential next PC. -/
def step (c : Compute) (s : State) : State :=
  { s.write c.dest (c.value s) with pc := s.pc + 4 }

/-- On the base fragment, `step` is exactly `RiscV.step`. -/
@[simp] theorem step_base (instr : RiscV.Instr) : step (.base instr) = RiscV.step instr := rfl

@[simp] theorem step_pc (c : Compute) (s : State) : (step c s).pc = s.pc + 4 := rfl

theorem step_read_dest (c : Compute) (s : State) (h : c.dest ≠ 0#5) :
    (step c s).read c.dest = c.value s :=
  s.read_write_same _ _ h

theorem step_read_other (c : Compute) (s : State) (r : Reg) (h : r ≠ c.dest) :
    (step c s).read r = s.read r :=
  s.read_write_other _ _ _ h

@[simp] theorem step_read_zero (c : Compute) (s : State) : (step c s).read 0#5 = 0#64 := by
  simp [step]

end Compute

/-! ## Word-form results as 32-bit operations

A 32-bit value kept sign-extended in a register is recovered by `low32`. -/

theorem low32_addiw (x : Word) (imm : BitVec 12) :
    low32 (sext32 (low32 x + imm.signExtend 32)) = low32 x + imm.signExtend 32 := by simp

@[simp] theorem low32_regW_add (x y : Word) :
    low32 (RegWOp.eval .add x y) = low32 x + low32 y := by simp [RegWOp.eval]

@[simp] theorem low32_regW_sub (x y : Word) :
    low32 (RegWOp.eval .sub x y) = low32 x - low32 y := by simp [RegWOp.eval]

@[simp] theorem low32_mulw (x y : Word) :
    low32 (MulWOp.eval .mulw x y) = low32 x * low32 y := by simp [MulWOp.eval]

@[simp] theorem low32_divw (x y : Word) :
    low32 (MulWOp.eval .divw x y) = divS (low32 x) (low32 y) := by simp [MulWOp.eval]

@[simp] theorem low32_divuw (x y : Word) :
    low32 (MulWOp.eval .divuw x y) = divU (low32 x) (low32 y) := by simp [MulWOp.eval]

@[simp] theorem low32_remw (x y : Word) :
    low32 (MulWOp.eval .remw x y) = remS (low32 x) (low32 y) := by simp [MulWOp.eval]

@[simp] theorem low32_remuw (x y : Word) :
    low32 (MulWOp.eval .remuw x y) = remU (low32 x) (low32 y) := by simp [MulWOp.eval]

/-- Low-half products do not depend on the upper operand bits. -/
theorem low32_mul (x y : Word) : low32 (x * y) = low32 x * low32 y := by
  simp [low32, BitVec.setWidth_mul _ _ (show 32 ≤ 64 by decide)]

theorem low32_add (x y : Word) : low32 (x + y) = low32 x + low32 y := by
  simp [low32, BitVec.setWidth_add _ _ (show 32 ≤ 64 by decide)]

end Silmaril.RiscV.Ext
