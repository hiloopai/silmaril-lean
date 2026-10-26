module

public import Silmaril.X86.Basic
public import Silmaril.Machine.Block

/-!
# Semantics of a small x86-64 integer subset

A handwritten local model of the 64-bit operand-size, register-direct forms of
MOV, ADD, OR, AND, SUB, XOR, CMP, NEG and NOT, following the Intel SDM
instruction reference. It is not derived from, or proved to correspond with,
the Sail, ACL2 or any hardware description.

Immediates are 32 bits and sign-extended to 64 bits, as for the `REX.W 81 /digit
id` and `REX.W C7 /0 id` forms. Every operand is read from the incoming state,
so destinations may alias sources. Flag effects:

* ADD, SUB and CMP set all six status flags (`addFlags`, `subFlags`).
* AND, OR and XOR clear CF and OF, set SF, ZF and PF, and leave AF undefined
  (`logicFlags`).
* NEG sets CF exactly when its operand is nonzero and the others as for
  `0 - x` (`negFlags`).
* MOV and NOT leave the flags unchanged.
* CMP writes no general-purpose register.

`step` retires one already-decoded instruction and advances RIP by its encoded
length (`Instr.length`; `Encoding.lean` proves it is the length of `encode`).
Instruction fetch, decoding from memory, faults and interrupts are outside this
model.
-/

@[expose] public section

namespace Silmaril.X86

/-- The two-operand integer operations sharing the `/r` and `81 /digit` forms. -/
inductive AluOp where
  | add | or | and | sub | xor | cmp
  deriving DecidableEq, Repr

/-- The instructions of the subset, all with 64-bit operand size. -/
inductive Instr where
  /-- `mov dst, src` (`MOV r/m64, r64`). -/
  | movRR (dst src : Reg)
  /-- `mov dst, imm32` with the immediate sign-extended (`MOV r/m64, imm32`). -/
  | movRI (dst : Reg) (imm : BitVec 32)
  /-- `op dst, src` (`OP r/m64, r64`). -/
  | alu (op : AluOp) (dst src : Reg)
  /-- `op dst, imm32` with the immediate sign-extended (`OP r/m64, imm32`). -/
  | aluI (op : AluOp) (dst : Reg) (imm : BitVec 32)
  | neg (dst : Reg)
  | not (dst : Reg)
  deriving DecidableEq, Repr

namespace AluOp

/-- The computed value; for CMP this is the discarded difference. -/
def result : AluOp → Word → Word → Word
  | .add, x, y => x + y
  | .or, x, y => x ||| y
  | .and, x, y => x &&& y
  | .sub, x, y => x - y
  | .xor, x, y => x ^^^ y
  | .cmp, x, y => x - y

def flags : AluOp → Word → Word → Flags
  | .add, x, y => addFlags x y
  | .sub, x, y => subFlags x y
  | .cmp, x, y => subFlags x y
  | .or, x, y => logicFlags (x ||| y)
  | .and, x, y => logicFlags (x &&& y)
  | .xor, x, y => logicFlags (x ^^^ y)

end AluOp

/-- Encoded length in bytes. -/
def Instr.length : Instr → Nat
  | .movRR .. | .alu .. | .neg _ | .not _ => 3
  | .movRI .. | .aluI .. => 7

/-- The general-purpose register written, if any. -/
def Instr.dest? : Instr → Option Reg
  | .movRR dst _ | .movRI dst _ | .neg dst | .not dst => some dst
  | .alu op dst _ | .aluI op dst _ => if op = .cmp then none else some dst

/-- A two-operand operation with destination `dst` and second operand `y`. -/
def execAlu (op : AluOp) (dst : Reg) (y : Word) (s : State) : State :=
  let x := s.read dst
  let s' := if op = .cmp then s else s.write dst (op.result x y)
  { s' with flags := op.flags x y }

/-- Register and flag effects, excluding RIP. -/
def Instr.exec : Instr → State → State
  | .movRR dst src, s => s.write dst (s.read src)
  | .movRI dst imm, s => s.write dst (imm.signExtend 64)
  | .alu op dst src, s => execAlu op dst (s.read src) s
  | .aluI op dst imm, s => execAlu op dst (imm.signExtend 64) s
  | .neg dst, s => { s.write dst (0#64 - s.read dst) with flags := negFlags (s.read dst) }
  | .not dst, s => s.write dst (~~~(s.read dst))

/-- Retire one decoded instruction with sequential next RIP (modulo 2^64). -/
def step (i : Instr) (s : State) : State :=
  { i.exec s with rip := s.rip + BitVec.ofNat 64 i.length }

/-! ## RIP and register frame -/

@[simp] theorem step_rip (i : Instr) (s : State) :
    (step i s).rip = s.rip + BitVec.ofNat 64 i.length := rfl

theorem step_read (i : Instr) (s : State) (r : Reg) :
    (step i s).read r = (i.exec s).read r := rfl

/-- Registers other than the instruction's destination are unchanged. -/
theorem step_read_other (i : Instr) (s : State) (r : Reg) (h : i.dest? ≠ some r) :
    (step i s).read r = s.read r := by
  rw [step_read]
  cases i with
  | movRR dst src =>
    exact State.read_write_other _ _ _ _ (fun e => h (by simp [Instr.dest?, e]))
  | movRI dst imm =>
    exact State.read_write_other _ _ _ _ (fun e => h (by simp [Instr.dest?, e]))
  | alu op dst src =>
    simp only [Instr.exec, execAlu]
    by_cases hc : op = .cmp
    · simp [hc]
    · simp only [hc, ite_false]
      exact State.read_write_other _ _ _ _ (fun e => h (by simp [Instr.dest?, e, hc]))
  | aluI op dst imm =>
    simp only [Instr.exec, execAlu]
    by_cases hc : op = .cmp
    · simp [hc]
    · simp only [hc, ite_false]
      exact State.read_write_other _ _ _ _ (fun e => h (by simp [Instr.dest?, e, hc]))
  | neg dst =>
    exact State.read_write_other _ _ _ _ (fun e => h (by simp [Instr.dest?, e]))
  | not dst =>
    exact State.read_write_other _ _ _ _ (fun e => h (by simp [Instr.dest?, e]))

/-! ## Per-instruction destination values and flags -/

@[simp] theorem step_movRR_read_dst (dst src : Reg) (s : State) :
    (step (.movRR dst src) s).read dst = s.read src := by
  simp [step_read, Instr.exec]

@[simp] theorem step_movRR_flags (dst src : Reg) (s : State) :
    (step (.movRR dst src) s).flags = s.flags := rfl

@[simp] theorem step_movRI_read_dst (dst : Reg) (imm : BitVec 32) (s : State) :
    (step (.movRI dst imm) s).read dst = imm.signExtend 64 := by
  simp [step_read, Instr.exec]

@[simp] theorem step_movRI_flags (dst : Reg) (imm : BitVec 32) (s : State) :
    (step (.movRI dst imm) s).flags = s.flags := rfl

theorem step_alu_read_dst (op : AluOp) (dst src : Reg) (s : State) (h : op ≠ .cmp) :
    (step (.alu op dst src) s).read dst = op.result (s.read dst) (s.read src) := by
  rw [step_read]
  simp [Instr.exec, execAlu, h, State.read, State.write]

@[simp] theorem step_alu_flags (op : AluOp) (dst src : Reg) (s : State) :
    (step (.alu op dst src) s).flags = op.flags (s.read dst) (s.read src) := rfl

theorem step_aluI_read_dst (op : AluOp) (dst : Reg) (imm : BitVec 32) (s : State)
    (h : op ≠ .cmp) :
    (step (.aluI op dst imm) s).read dst = op.result (s.read dst) (imm.signExtend 64) := by
  rw [step_read]
  simp [Instr.exec, execAlu, h, State.read, State.write]

@[simp] theorem step_aluI_flags (op : AluOp) (dst : Reg) (imm : BitVec 32) (s : State) :
    (step (.aluI op dst imm) s).flags = op.flags (s.read dst) (imm.signExtend 64) := rfl

/-- CMP writes no general-purpose register. -/
@[simp] theorem step_alu_cmp_read (dst src r : Reg) (s : State) :
    (step (.alu .cmp dst src) s).read r = s.read r :=
  step_read_other _ _ _ (by simp [Instr.dest?])

@[simp] theorem step_aluI_cmp_read (dst r : Reg) (imm : BitVec 32) (s : State) :
    (step (.aluI .cmp dst imm) s).read r = s.read r :=
  step_read_other _ _ _ (by simp [Instr.dest?])

@[simp] theorem step_neg_read_dst (dst : Reg) (s : State) :
    (step (.neg dst) s).read dst = 0#64 - s.read dst := by
  rw [step_read]
  simp [Instr.exec, State.read, State.write]

@[simp] theorem step_neg_flags (dst : Reg) (s : State) :
    (step (.neg dst) s).flags = negFlags (s.read dst) := rfl

/-- NEG's CF is set exactly when its operand is nonzero. -/
theorem step_neg_carry (dst : Reg) (s : State) :
    (step (.neg dst) s).flags.carry = some (decide (s.read dst ≠ 0#64)) := by
  simp only [step_neg_flags, negFlags, bne, Option.some.injEq, decide_not]
  congr 1

@[simp] theorem step_not_read_dst (dst : Reg) (s : State) :
    (step (.not dst) s).read dst = ~~~(s.read dst) := by
  simp [step_read, Instr.exec]

@[simp] theorem step_not_flags (dst : Reg) (s : State) :
    (step (.not dst) s).flags = s.flags := rfl

/-! ## Straight-line blocks -/

/-- RIP advances by the total encoded length of the block, modulo 2^64. -/
theorem run_rip (code : List Instr) (s : State) :
    (Machine.Block.run step code s).rip =
      s.rip + BitVec.ofNat 64 (code.map Instr.length).sum := by
  induction code generalizing s with
  | nil => simp
  | cons i rest ih =>
    simp only [Machine.Block.run_cons, ih, step_rip, List.map_cons, List.sum_cons,
      BitVec.ofNat_add, BitVec.add_assoc]

/-- Registers outside a block's destination set retain their value. -/
theorem run_read_frame (code : List Instr) (s : State) (r : Reg)
    (h : ∀ i ∈ code, i.dest? ≠ some r) :
    (Machine.Block.run step code s).read r = s.read r := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [Machine.Block.run_cons, ih _ (fun j hj => h j (List.mem_cons_of_mem i hj))]
    exact step_read_other i s r (h i List.mem_cons_self)

/-! ## Arithmetic leaf: `mov rax, rdi; add rax, rsi` -/

/-- The six-byte body of a two-argument addition leaf (without its return). -/
def addLeaf : List Instr := [.movRR .rax .rdi, .alu .add .rax .rsi]

/-- For arbitrary inputs `a` in `rdi` and `b` in `rsi`, the leaf leaves
`a + b` (wrapping) in `rax`, preserves every other register, sets the flags of
the addition and advances RIP by six bytes. -/
theorem addLeaf_spec (s : State) (a b : Word) (ha : s.read .rdi = a) (hb : s.read .rsi = b) :
    let t := Machine.Block.run step addLeaf s
    t.read .rax = a + b ∧
      (t.read .rax).toNat = (a.toNat + b.toNat) % 2 ^ 64 ∧
      (∀ r, r ≠ .rax → t.read r = s.read r) ∧
      t.rip = s.rip + 6#64 ∧
      t.flags = addFlags a b := by
  have hrax : (Machine.Block.run step addLeaf s).read .rax = a + b := by
    simp only [addLeaf, Machine.Block.run_cons, Machine.Block.run_nil]
    rw [step_alu_read_dst _ _ _ _ (by decide), step_movRR_read_dst,
      step_read_other _ _ _ (by simp [Instr.dest?])]
    simp [AluOp.result, ha, hb]
  refine ⟨hrax, ?_, ?_, ?_, ?_⟩
  · rw [hrax, BitVec.toNat_add]
  · intro r hr
    exact run_read_frame _ _ _ (by
      intro i hi
      simp only [addLeaf, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> simp [Instr.dest?, Ne.symm hr])
  · rw [run_rip]; rfl
  · simp only [addLeaf, Machine.Block.run_cons, Machine.Block.run_nil, step_alu_flags,
      step_movRR_read_dst]
    rw [step_read_other _ _ _ (by simp [Instr.dest?]), ha, hb]
    rfl

end Silmaril.X86
