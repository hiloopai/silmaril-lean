module

public import Silmaril.X86.Ext.Semantics

/-!
# Instruction-level facts for code generation

Per-instruction statements of `Ext.exec` in the forms a code generator emits:
register-direct arithmetic at both sizes, loads and stores with an explicit
memory outcome, compares followed by SETcc/Jcc, CDQ/CQO followed by
DIV/IDIV, and the stack instructions. `next` below is always
`s.rip + BitVec.ofNat 64 i.length`, and `Instr.length i = (encode i).length`.

The division lemmas `divide_unsigned` and `divide_signed` give DIV and IDIV in
terms of `BitVec.udiv`/`umod` and `sdiv`/`srem` when the high half is set up
as a compiler does (zeroed for DIV, CDQ/CQO sign fill for IDIV), including
exactly when `#DE` is raised.

These are facts about the handwritten local model only.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (Reg Word State Flags AluOp Byte pushWord popWord)
open Silmaril.Process (Memory)

variable (s : State) (memory : Memory)

/-! ## Moves -/

theorem exec_mov_reg (sz : Sz) (dst src : Reg) :
    exec (.mov sz (.reg dst) src) s memory =
      .ok { sz.write s dst (sz.read s src) with
        rip := s.rip + BitVec.ofNat 64 (Instr.mov sz (.reg dst) src).length } memory := rfl

theorem exec_movI_reg (sz : Sz) (dst : Reg) (imm : BitVec 32) :
    exec (.movI sz (.reg dst) imm) s memory =
      .ok { sz.write s dst (imm.signExtend sz.bits) with
        rip := s.rip + BitVec.ofNat 64 (Instr.movI sz (.reg dst) imm).length } memory := rfl

theorem exec_movabs (dst : Reg) (imm : BitVec 64) :
    exec (.movabs dst imm) s memory =
      .ok { s.write dst imm with
        rip := s.rip + BitVec.ofNat 64 (Instr.movabs dst imm).length } memory := rfl

theorem exec_lea (dst : Reg) (m : Mem) :
    exec (.lea .q dst m) s memory =
      .ok { s.write dst (m.addr s (s.rip + BitVec.ofNat 64 (Instr.lea .q dst m).length)) with
        rip := s.rip + BitVec.ofNat 64 (Instr.lea .q dst m).length } memory := rfl

/-- `lea dst, [rip + disp]` materialises the address of the next instruction
plus the displacement: this is how a PC-relative `.rodata` reference is
compiled. -/
theorem exec_lea_rip (dst : Reg) (disp : BitVec 32) :
    exec (.lea .q dst (Mem.ofRip disp)) s memory =
      .ok { s.write dst (s.rip + BitVec.ofNat 64 (Instr.lea .q dst (Mem.ofRip disp)).length +
          disp.signExtend 64) with
        rip := s.rip + BitVec.ofNat 64 (Instr.lea .q dst (Mem.ofRip disp)).length } memory := by
  simp [exec, retire, Mem.addr, Mem.ofRip]

theorem exec_movsxd_reg (dst src : Reg) :
    exec (.movsxd dst (.reg src)) s memory =
      .ok { s.write dst ((Sz.d.read s src).signExtend 64) with
        rip := s.rip + BitVec.ofNat 64 (Instr.movsxd dst (.reg src)).length } memory := rfl

theorem exec_movx_reg (sx : Bool) (sz : Sz) (n : Narrow) (dst src : Reg) :
    exec (.movx sx sz n dst (.reg src)) s memory =
      .ok { sz.write s dst (if sx then ((s.read src).setWidth n.bits).signExtend sz.bits
          else ((s.read src).setWidth n.bits).setWidth sz.bits) with
        rip := s.rip + BitVec.ofNat 64 (Instr.movx sx sz n dst (.reg src)).length } memory := rfl

/-- CMOV reads the source before testing flags, and preserves flags and memory.
The false branch still performs the operand-size register write. -/
theorem exec_cmov_reg (sz : Sz) (c : Cond) (dst src : Reg) :
    exec (.cmov sz c dst (.reg src)) s memory =
      match c.eval s.flags with
      | none => .undefinedCondition c
      | some taken => .ok { sz.write s dst
          (if taken then sz.read s src else sz.read s dst) with
          rip := s.rip + BitVec.ofNat 64 (Instr.cmov sz c dst (.reg src)).length } memory := by
  simp only [exec, readRM]
  cases c.eval s.flags <;> rfl

/-! ## Loads and stores -/

/-- A load retires exactly when the bytes are readable. -/
theorem exec_load (sz : Sz) (dst : Reg) (m : Mem) :
    exec (.load sz dst m) s memory =
      match loadN memory (m.addr s (s.rip + BitVec.ofNat 64 (Instr.load sz dst m).length))
        sz.bytes with
      | some v => .ok { sz.write s dst (v.setWidth sz.bits) with
          rip := s.rip + BitVec.ofNat 64 (Instr.load sz dst m).length } memory
      | none => .dataFault := by
  simp only [exec, readRM]
  cases loadN memory (m.addr s (s.rip + BitVec.ofNat 64 (Instr.load sz dst m).length)) sz.bytes <;>
    rfl

/-- A 32- or 64-bit store retires exactly when the bytes are writable. -/
theorem exec_store (sz : Sz) (m : Mem) (src : Reg) :
    exec (.mov sz (.mem m) src) s memory =
      match storeN memory (m.addr s (s.rip + BitVec.ofNat 64 (Instr.mov sz (.mem m) src).length))
        sz.bytes ((sz.read s src).setWidth 64) with
      | some after => .ok { s with
          rip := s.rip + BitVec.ofNat 64 (Instr.mov sz (.mem m) src).length } after
      | none => .dataFault := by
  simp only [exec, writeRM]
  cases storeN memory (m.addr s (s.rip + BitVec.ofNat 64 (Instr.mov sz (.mem m) src).length))
    sz.bytes ((sz.read s src).setWidth 64) <;> rfl

/-- A narrow store to a memory destination retires exactly when the bytes are
writable. The statement names a `Mem` because that is the form a code
generator emits; `exec_storeNarrow_reg` covers the `mod = 11` case. -/
theorem exec_storeNarrow (n : Narrow) (m : Mem) (src : Reg) :
    exec (.store n (.mem m) src) s memory =
      match storeN memory (m.addr s (s.rip + BitVec.ofNat 64 (Instr.store n (.mem m) src).length))
        n.bytes (s.read src) with
      | some after => .ok { s with
          rip := s.rip + BitVec.ofNat 64 (Instr.store n (.mem m) src).length } after
      | none => .dataFault := by
  simp only [exec, writeNarrow, storeN_setWidth]
  cases storeN memory (m.addr s (s.rip + BitVec.ofNat 64 (Instr.store n (.mem m) src).length))
    n.bytes (s.read src) <;> rfl

/-- `88 /r` and `66 89 /r` with `mod = 11`: a register-to-register move at 8 or
16 bits, which keeps the bits above the ones written and never faults. -/
theorem exec_storeNarrow_reg (n : Narrow) (dst src : Reg) :
    exec (.store n (.reg dst) src) s memory =
      .ok { s.write dst ((s.read dst &&& ~~~(narrowMask n)) |||
          ((s.read src).setWidth n.bits).setWidth 64) with
        rip := s.rip + BitVec.ofNat 64 (Instr.store n (.reg dst) src).length } memory := rfl

/-- At 8 bits that is `writeByte`, the same register view SETcc and `8A /r`
use. -/
theorem exec_store8_reg (dst src : Reg) :
    exec (.store .b (.reg dst) src) s memory =
      .ok { writeByte s dst ((s.read src).setWidth 8) with
        rip := s.rip + BitVec.ofNat 64 (Instr.store .b (.reg dst) src).length } memory := rfl

/-- Spill and reload: a 64-bit store followed by a 64-bit load of the same
readable bytes returns the stored register. -/
theorem spill_reload {m : Mem} {src dst : Reg} {after : Memory} {stRip : Word}
    (stored : storeN memory (m.addr s stRip) 8 (s.read src) = some after)
    (readable : memory.Permitted .read (m.addr s stRip).toNat 8) (t : State)
    (sameAddress :
      m.addr t (t.rip + BitVec.ofNat 64 (Instr.load .q dst m).length) = m.addr s stRip) :
    exec (.load .q dst m) t after =
      .ok { t.write dst (s.read src) with
        rip := t.rip + BitVec.ofNat 64 (Instr.load .q dst m).length } after := by
  rw [exec_load, sameAddress, show Sz.q.bytes = 8 from rfl,
    loadN_storeN_eight stored readable]
  simp

/-! ## Arithmetic on registers -/

theorem exec_alu_reg (sz : Sz) (op : AluOp) (dst src : Reg) (h : op ≠ .cmp) :
    exec (.alu sz op (.reg dst) src) s memory =
      .ok { sz.write s dst (AluOp.resultN op (sz.read s dst) (sz.read s src)) with
        flags := AluOp.flagsN op (sz.read s dst) (sz.read s src)
        rip := s.rip + BitVec.ofNat 64 (Instr.alu sz op (.reg dst) src).length } memory := by
  simp [exec, retire, aluStep, readRM, writeRM, h]

theorem exec_cmp_reg (sz : Sz) (dst src : Reg) :
    exec (.alu sz .cmp (.reg dst) src) s memory =
      .ok { s with
        flags := subFlagsN (sz.read s dst) (sz.read s src)
        rip := s.rip + BitVec.ofNat 64 (Instr.alu sz .cmp (.reg dst) src).length } memory := by
  simp [exec, retire, aluStep, readRM, AluOp.flagsN]

theorem exec_aluI_reg (sz : Sz) (op : AluOp) (dst : Reg) (imm : BitVec 32) (h : op ≠ .cmp) :
    exec (.aluI sz op (.reg dst) imm) s memory =
      .ok { sz.write s dst (AluOp.resultN op (sz.read s dst) (imm.signExtend sz.bits)) with
        flags := AluOp.flagsN op (sz.read s dst) (imm.signExtend sz.bits)
        rip := s.rip + BitVec.ofNat 64 (Instr.aluI sz op (.reg dst) imm).length } memory := by
  simp [exec, retire, aluStep, readRM, writeRM, h]

theorem exec_cmpI_reg (sz : Sz) (dst : Reg) (imm : BitVec 32) :
    exec (.aluI sz .cmp (.reg dst) imm) s memory =
      .ok { s with
        flags := subFlagsN (sz.read s dst) (imm.signExtend sz.bits)
        rip := s.rip + BitVec.ofNat 64 (Instr.aluI sz .cmp (.reg dst) imm).length } memory := by
  simp [exec, retire, aluStep, readRM, AluOp.flagsN]

theorem exec_aluR_reg (sz : Sz) (op : AluOp) (dst src : Reg) (h : op ≠ .cmp) :
    exec (.aluR sz op dst (.reg src)) s memory =
      .ok { sz.write s dst (AluOp.resultN op (sz.read s dst) (sz.read s src)) with
        flags := AluOp.flagsN op (sz.read s dst) (sz.read s src)
        rip := s.rip + BitVec.ofNat 64 (Instr.aluR sz op dst (.reg src)).length } memory := by
  simp [exec, retire, aluStepR, readRM, h]

theorem exec_cmpR_reg (sz : Sz) (dst src : Reg) :
    exec (.aluR sz .cmp dst (.reg src)) s memory =
      .ok { s with
        flags := subFlagsN (sz.read s dst) (sz.read s src)
        rip := s.rip + BitVec.ofNat 64 (Instr.aluR sz .cmp dst (.reg src)).length } memory := by
  simp [exec, retire, aluStepR, readRM, AluOp.flagsN]

theorem exec_aluI8_reg (sz : Sz) (op : AluOp) (dst : Reg) (imm : BitVec 8) (h : op ≠ .cmp) :
    exec (.aluI8 sz op (.reg dst) imm) s memory =
      .ok { sz.write s dst (AluOp.resultN op (sz.read s dst) (imm.signExtend sz.bits)) with
        flags := AluOp.flagsN op (sz.read s dst) (imm.signExtend sz.bits)
        rip := s.rip + BitVec.ofNat 64 (Instr.aluI8 sz op (.reg dst) imm).length } memory := by
  simp [exec, retire, aluStep, readRM, writeRM, h]

/-- `cmp reg, [mem]` (`3B /r` with a memory source): the comparison a `-O0`
loop head emits when the bound is a spilled variable rather than a literal.
Flags only, and it faults exactly when the load does. -/
theorem exec_cmpR_mem (sz : Sz) (dst : Reg) (m : Mem) :
    exec (.aluR sz .cmp dst (.mem m)) s memory =
      match loadN memory
        (m.addr s (s.rip + BitVec.ofNat 64 (Instr.aluR sz .cmp dst (.mem m)).length))
        sz.bytes with
      | some v => .ok { s with
          flags := subFlagsN (sz.read s dst) (v.setWidth sz.bits)
          rip := s.rip + BitVec.ofNat 64 (Instr.aluR sz .cmp dst (.mem m)).length } memory
      | none => .dataFault := by
  simp only [exec, retire, aluStepR, readRM, AluOp.flagsN]
  cases loadN memory
    (m.addr s (s.rip + BitVec.ofNat 64 (Instr.aluR sz .cmp dst (.mem m)).length)) sz.bytes <;>
    rfl

/-- `cmp eAX/rAX, imm32` (`3D id`), the accumulator form. Flags only, never
faults. -/
theorem exec_cmpA (sz : Sz) (imm : BitVec 32) :
    exec (.aluA sz .cmp imm) s memory =
      .ok { s with
        flags := subFlagsN (sz.read s .rax) (imm.signExtend sz.bits)
        rip := s.rip + BitVec.ofNat 64 (Instr.aluA sz .cmp imm).length } memory := by
  simp [exec, retire, aluStep, readRM, AluOp.flagsN]

theorem exec_cmpI8_reg (sz : Sz) (dst : Reg) (imm : BitVec 8) :
    exec (.aluI8 sz .cmp (.reg dst) imm) s memory =
      .ok { s with
        flags := subFlagsN (sz.read s dst) (imm.signExtend sz.bits)
        rip := s.rip + BitVec.ofNat 64 (Instr.aluI8 sz .cmp (.reg dst) imm).length } memory := by
  simp [exec, retire, aluStep, readRM, AluOp.flagsN]

/-- CDQE (`REX.W 98`, `cltq`): RAX becomes the sign-extension of EAX. -/
theorem exec_cxe_q :
    exec (.cxe .q) s memory =
      .ok { s.write .rax ((Sz.d.read s .rax).signExtend 64) with
        rip := s.rip + BitVec.ofNat 64 (Instr.cxe .q).length } memory := rfl

/-- CWDE (`98`, `cwtl`): EAX becomes the sign-extension of AX, zero-extended
into RAX. -/
theorem exec_cxe_d :
    exec (.cxe .d) s memory =
      .ok { Sz.d.write s .rax (((s.read .rax).setWidth 16).signExtend 32) with
        rip := s.rip + BitVec.ofNat 64 (Instr.cxe .d).length } memory := rfl

theorem exec_test_reg (sz : Sz) (dst src : Reg) :
    exec (.test sz (.reg dst) src) s memory =
      .ok { s with
        flags := logicFlagsN (sz.read s dst &&& sz.read s src)
        rip := s.rip + BitVec.ofNat 64 (Instr.test sz (.reg dst) src).length } memory := rfl

theorem exec_neg_reg (sz : Sz) (dst : Reg) :
    exec (.unary sz .neg (.reg dst)) s memory =
      .ok { sz.write s dst (0#sz.bits - sz.read s dst) with
        flags := negFlagsN (sz.read s dst)
        rip := s.rip + BitVec.ofNat 64 (Instr.unary sz .neg (.reg dst)).length } memory := rfl

theorem exec_not_reg (sz : Sz) (dst : Reg) :
    exec (.unary sz .not (.reg dst)) s memory =
      .ok { sz.write s dst (~~~(sz.read s dst)) with
        rip := s.rip + BitVec.ofNat 64 (Instr.unary sz .not (.reg dst)).length } memory := rfl

theorem exec_imul_reg (sz : Sz) (dst src : Reg) :
    exec (.imul sz dst (.reg src)) s memory =
      .ok { sz.write s dst (sz.read s dst * sz.read s src) with
        flags := imulFlags (sz.read s dst) (sz.read s src)
        rip := s.rip + BitVec.ofNat 64 (Instr.imul sz dst (.reg src)).length } memory := rfl

/-- Unsigned MUL samples the old accumulator and source, including when the
source aliases either result register. Only RAX/RDX, flags and RIP change. -/
theorem exec_mul_reg (sz : Sz) (src : Reg) :
    exec (.mul sz (.reg src)) s memory =
      let product := (sz.read s .rax).toNat * (sz.read s src).toNat
      let lo := BitVec.ofNat sz.bits product
      let hi := BitVec.ofNat sz.bits (product / 2 ^ sz.bits)
      .ok { sz.write (sz.write s .rax lo) .rdx hi with
        flags := mulFlags (hi != 0#sz.bits)
        rip := s.rip + BitVec.ofNat 64 (Instr.mul sz (.reg src)).length } memory := rfl

theorem exec_shift_reg (sz : Sz) (op : ShiftOp) (dst : Reg) (count : Count) :
    exec (.shift sz op (.reg dst) count) s memory =
      .ok { sz.write s dst (op.result (sz.read s dst) ((count.raw s).toNat % sz.bits)) with
        flags := op.flags (sz.read s dst) ((count.raw s).toNat % sz.bits) s.flags
        rip := s.rip + BitVec.ofNat 64 (Instr.shift sz op (.reg dst) count).length } memory := rfl

theorem exec_cxd (sz : Sz) :
    exec (.cxd sz) s memory =
      .ok { sz.write s .rdx (if (sz.read s .rax).msb then BitVec.allOnes sz.bits else 0#sz.bits) with
        rip := s.rip + BitVec.ofNat 64 (Instr.cxd sz).length } memory := rfl

theorem exec_div_reg (sz : Sz) (signed : Bool) (src : Reg) :
    exec (.div sz signed (.reg src)) s memory =
      match divide sz signed (sz.read s .rdx) (sz.read s .rax) (sz.read s src) with
      | none => .divideError
      | some (q, r) => .ok { sz.write (sz.write s .rax q) .rdx r with
          flags := undefinedFlags
          rip := s.rip + BitVec.ofNat 64 (Instr.div sz signed (.reg src)).length } memory := by
  simp only [exec, readRM]
  cases divide sz signed (sz.read s .rdx) (sz.read s .rax) (sz.read s src) <;> rfl

/-- BSWAP reverses the bytes of its register and changes no flag. -/
theorem exec_bswap (sz : Sz) (dst : Reg) :
    exec (.bswap sz dst) s memory =
      .ok { sz.write s dst (byteSwap sz (sz.read s dst)) with
        rip := s.rip + BitVec.ofNat 64 (Instr.bswap sz dst).length } memory := rfl

/-- INC and DEC add or subtract one and leave CF alone. -/
theorem exec_incdec_reg (sz : Sz) (dec : Bool) (dst : Reg) :
    exec (.incdec sz dec (.reg dst)) s memory =
      .ok { sz.write s dst (if dec then sz.read s dst - 1#sz.bits else sz.read s dst + 1#sz.bits)
          with
        flags := if dec then decFlagsN (sz.read s dst) s.flags else incFlagsN (sz.read s dst) s.flags
        rip := s.rip + BitVec.ofNat 64 (Instr.incdec sz dec (.reg dst)).length } memory := by
  cases dec <;> simp [exec, retire, readRM, writeRM]

/-- INC and DEC do not change the carry flag. -/
theorem incdec_carry (sz : Sz) (dec : Bool) (dst : Reg) {t : State} {after : Memory}
    (h : exec (.incdec sz dec (.reg dst)) s memory = .ok t after) : t.flags.carry = s.flags.carry := by
  rw [exec_incdec_reg] at h
  obtain ⟨rfl, -⟩ := Result.ok.injEq .. ▸ h
  cases dec <;> rfl

/-- `mov r32, imm32` zero-extends to 64 bits. -/
theorem exec_movI32 (dst : Reg) (imm : BitVec 32) :
    exec (.movI32 dst imm) s memory =
      .ok { s.write dst (imm.setWidth 64) with
        rip := s.rip + BitVec.ofNat 64 (Instr.movI32 dst imm).length } memory := rfl

/-- The accumulator ALU form is the `r/m` form with RAX as destination. -/
theorem exec_aluA (sz : Sz) (op : AluOp) (imm : BitVec 32) :
    exec (.aluA sz op imm) s memory =
      retire (s.rip + BitVec.ofNat 64 (Instr.aluA sz op imm).length)
        (aluStep sz op (.reg .rax) (imm.signExtend sz.bits) s memory
          (s.rip + BitVec.ofNat 64 (Instr.aluA sz op imm).length)) := rfl

theorem exec_aluA_nonCmp (sz : Sz) (op : AluOp) (imm : BitVec 32) (h : op ≠ .cmp) :
    exec (.aluA sz op imm) s memory =
      .ok { sz.write s .rax (AluOp.resultN op (sz.read s .rax) (imm.signExtend sz.bits)) with
        flags := AluOp.flagsN op (sz.read s .rax) (imm.signExtend sz.bits)
        rip := s.rip + BitVec.ofNat 64 (Instr.aluA sz op imm).length } memory := by
  simp [exec, retire, aluStep, readRM, writeRM, h]

/-- Byte TEST changes flags and RIP only, including when source and destination alias. -/
theorem exec_test8_reg (dst src : Reg) :
    exec (.test8 (.reg dst) src) s memory =
      .ok { s with
        flags := logicFlagsN ((s.read dst).setWidth 8 &&& (s.read src).setWidth 8)
        rip := s.rip + BitVec.ofNat 64 (Instr.test8 (.reg dst) src).length } memory := rfl

/-- Byte-immediate TEST preserves every register and memory; flags use width 8. -/
theorem exec_testI8_reg (dst : Reg) (imm : BitVec 8) :
    exec (.testI8 (.reg dst) imm) s memory =
      .ok { s with
        flags := logicFlagsN ((s.read dst).setWidth 8 &&& imm)
        rip := s.rip + BitVec.ofNat 64 (Instr.testI8 (.reg dst) imm).length } memory := rfl

theorem exec_testA8 (imm : BitVec 8) :
    exec (.testA8 imm) s memory =
      .ok { s with
        flags := logicFlagsN ((s.read .rax).setWidth 8 &&& imm)
        rip := s.rip + BitVec.ofNat 64 (Instr.testA8 imm).length } memory := rfl

/-- Byte CMP reads only the low byte and leaves every register and memory unchanged. -/
theorem exec_cmpI8_byte_reg (dst : Reg) (imm : BitVec 8) :
    exec (.cmpI8 (.reg dst) imm) s memory =
      .ok { s with
        flags := subFlagsN ((s.read dst).setWidth 8) imm
        rip := s.rip + BitVec.ofNat 64 (Instr.cmpI8 (.reg dst) imm).length } memory := rfl

theorem exec_cmpA8 (imm : BitVec 8) :
    exec (.cmpA8 imm) s memory =
      .ok { s with
        flags := subFlagsN ((s.read .rax).setWidth 8) imm
        rip := s.rip + BitVec.ofNat 64 (Instr.cmpA8 imm).length } memory := rfl

theorem exec_testA (sz : Sz) (imm : BitVec 32) :
    exec (.testA sz imm) s memory =
      .ok { s with
        flags := logicFlagsN (sz.read s .rax &&& imm.signExtend sz.bits)
        rip := s.rip + BitVec.ofNat 64 (Instr.testA sz imm).length } memory := rfl

theorem exec_mov8_reg (dst src : Reg) :
    exec (.mov8 dst (.reg src)) s memory =
      .ok { writeByte s dst ((s.read src).setWidth 8) with
        rip := s.rip + BitVec.ofNat 64 (Instr.mov8 dst (.reg src)).length } memory := rfl

/-- A NOP of any length changes nothing but RIP. -/
theorem exec_nop (len : Fin 15) :
    exec (.nop len) s memory =
      .ok { s with rip := s.rip + BitVec.ofNat 64 (Instr.nop len).length } memory := rfl

/-- ENDBR64 likewise: the model has no indirect-branch tracking. -/
theorem exec_endbr64 :
    exec .endbr64 s memory =
      .ok { s with rip := s.rip + BitVec.ofNat 64 Instr.endbr64.length } memory := rfl

/-- LEAVE is `mov rsp, rbp` followed by `pop rbp`. -/
theorem exec_leave :
    exec .leave s memory =
      match X86.popWord (s.write .rsp (s.read .rbp)) memory with
      | some (v, t) => .ok { t.write .rbp v with
          rip := s.rip + BitVec.ofNat 64 Instr.leave.length } memory
      | none => .dataFault := by
  simp only [exec]
  cases X86.popWord (s.write .rsp (s.read .rbp)) memory <;> rfl

/-! ## Conditions and control flow -/

theorem exec_setcc_reg (c : Cond) (dst : Reg) (v : Bool) (h : c.eval s.flags = some v) :
    exec (.setcc c (.reg dst)) s memory =
      .ok { writeByte s dst (if v then 1#8 else 0#8) with
        rip := s.rip + BitVec.ofNat 64 (Instr.setcc c (.reg dst)).length } memory := by
  simp [exec, h, retire, writeRM8]

theorem exec_setcc_undefined (c : Cond) (dst : RM) (h : c.eval s.flags = none) :
    exec (.setcc c dst) s memory = .undefinedCondition c := by
  simp [exec, h]

theorem exec_jmp8 (rel : BitVec 8) :
    exec (.jmp8 rel) s memory =
      .ok { s with rip := s.rip + BitVec.ofNat 64 (Instr.jmp8 rel).length + rel.signExtend 64 }
        memory := rfl

theorem exec_jcc8 (c : Cond) (rel : BitVec 8) (v : Bool) (h : c.eval s.flags = some v) :
    exec (.jcc8 c rel) s memory =
      .ok { s with
        rip := if v then s.rip + BitVec.ofNat 64 (Instr.jcc8 c rel).length + rel.signExtend 64
          else s.rip + BitVec.ofNat 64 (Instr.jcc8 c rel).length } memory := by
  cases v <;> simp [exec, h]

theorem exec_jmp (rel : BitVec 32) :
    exec (.jmp rel) s memory =
      .ok { s with rip := s.rip + BitVec.ofNat 64 (Instr.jmp rel).length + rel.signExtend 64 }
        memory := rfl

theorem exec_jcc (c : Cond) (rel : BitVec 32) (v : Bool) (h : c.eval s.flags = some v) :
    exec (.jcc c rel) s memory =
      .ok { s with rip := if v then s.rip + BitVec.ofNat 64 (Instr.jcc c rel).length + rel.signExtend 64
          else s.rip + BitVec.ofNat 64 (Instr.jcc c rel).length } memory := by
  cases v <;> simp [exec, h]

theorem exec_jcc_undefined (c : Cond) (rel : BitVec 32) (h : c.eval s.flags = none) :
    exec (.jcc c rel) s memory = .undefinedCondition c := by
  simp [exec, h]

/-- After a 32-bit compare, every condition is the corresponding comparison of
the 32-bit operands. -/
theorem eval_after_cmp_d (x y : BitVec 32) (c : Cond) :
    c.eval (subFlagsN x y) = some (Cond.afterCmp (w := 31) x y c) :=
  eval_subFlagsN (w := 31) x y c

/-- After a 64-bit compare, likewise. -/
theorem eval_after_cmp_q (x y : BitVec 64) (c : Cond) :
    c.eval (subFlagsN x y) = some (Cond.afterCmp (w := 63) x y c) :=
  eval_subFlagsN (w := 63) x y c

/-- After any retired CMP (register or memory operand), every condition is
defined: a SETcc or Jcc reading these flags never has an undefined outcome. -/
theorem cmp_conditions_defined {sz : Sz} {dst : RM} {src : Reg} {t : State} {after : Memory}
    (h : exec (.alu sz .cmp dst src) s memory = .ok t after) (c : Cond) :
    (c.eval t.flags).isSome := by
  simp only [exec, retire, aluStep] at h
  cases hr : readRM sz dst s memory (s.rip + BitVec.ofNat 64 (Instr.alu sz .cmp dst src).length)
    with
  | none => simp [hr] at h
  | some x =>
    simp only [hr, ite_true, Result.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact eval_subFlagsN_isSome _ _ c

theorem cmpI_conditions_defined {sz : Sz} {dst : RM} {imm : BitVec 32} {t : State}
    {after : Memory} (h : exec (.aluI sz .cmp dst imm) s memory = .ok t after) (c : Cond) :
    (c.eval t.flags).isSome := by
  simp only [exec, retire, aluStep] at h
  cases hr : readRM sz dst s memory (s.rip + BitVec.ofNat 64 (Instr.aluI sz .cmp dst imm).length)
    with
  | none => simp [hr] at h
  | some x =>
    simp only [hr, ite_true, Result.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact eval_subFlagsN_isSome _ _ c

theorem cmpR_conditions_defined {sz : Sz} {dst : Reg} {src : RM} {t : State} {after : Memory}
    (h : exec (.aluR sz .cmp dst src) s memory = .ok t after) (c : Cond) :
    (c.eval t.flags).isSome := by
  simp only [exec, retire, aluStepR] at h
  cases hr : readRM sz src s memory (s.rip + BitVec.ofNat 64 (Instr.aluR sz .cmp dst src).length)
    with
  | none => simp [hr] at h
  | some y =>
    simp only [hr, ite_true, Result.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact eval_subFlagsN_isSome _ _ c

theorem cmpI8_conditions_defined {sz : Sz} {dst : RM} {imm : BitVec 8} {t : State}
    {after : Memory} (h : exec (.aluI8 sz .cmp dst imm) s memory = .ok t after) (c : Cond) :
    (c.eval t.flags).isSome := by
  simp only [exec, retire, aluStep] at h
  cases hr : readRM sz dst s memory (s.rip + BitVec.ofNat 64 (Instr.aluI8 sz .cmp dst imm).length)
    with
  | none => simp [hr] at h
  | some x =>
    simp only [hr, ite_true, Result.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact eval_subFlagsN_isSome _ _ c

/-- After any retired TEST, every condition is defined. -/
theorem test_conditions_defined {sz : Sz} {dst : RM} {src : Reg} {t : State} {after : Memory}
    (h : exec (.test sz dst src) s memory = .ok t after) (c : Cond) :
    (c.eval t.flags).isSome := by
  simp only [exec, retire] at h
  cases hr : readRM sz dst s memory (s.rip + BitVec.ofNat 64 (Instr.test sz dst src).length) with
  | none => simp [hr] at h
  | some x =>
    simp only [hr, Option.map_some, Result.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact eval_logicFlagsN_isSome _ c

/-! ## Stack -/

theorem exec_push (src : Reg) :
    exec (.push src) s memory =
      match (X86.Insn.push src).exec s memory with
      | some (t, m) => .ok t m
      | none => .dataFault := exec_ofInsn (.push src) s memory

theorem exec_pop (dst : Reg) :
    exec (.pop dst) s memory =
      match (X86.Insn.pop dst).exec s memory with
      | some (t, m) => .ok t m
      | none => .dataFault := exec_ofInsn (.pop dst) s memory

theorem exec_call (rel : BitVec 32) :
    exec (.call rel) s memory =
      match (X86.Insn.call rel).exec s memory with
      | some (t, m) => .ok t m
      | none => .dataFault := exec_ofInsn (.call rel) s memory

theorem exec_ret :
    exec .ret s memory =
      match X86.Insn.ret.exec s memory with
      | some (t, m) => .ok t m
      | none => .dataFault := exec_ofInsn .ret s memory

theorem exec_ud2 : exec .ud2 s memory = .trap := rfl

theorem exec_bitcount_reg (op : BitCountOp) (sz : Sz) (dst src : Reg) :
    exec (.bitcount op sz dst (.reg src)) s memory =
      .ok { sz.write s dst (BitVec.ofNat sz.bits (op.count (sz.read s src))) with
        flags := op.flags (sz.read s src)
        rip := s.rip + BitVec.ofNat 64 (Instr.bitcount op sz dst (.reg src)).length } memory := rfl

/-! ## Division as compiled -/

/-- DIV with a zeroed high half is unsigned division; `#DE` exactly on a zero
divisor. -/
theorem divide_unsigned (sz : Sz) (lo y : BitVec sz.bits) :
    divide sz false 0#sz.bits lo y = if y = 0#sz.bits then none else some (lo / y, lo % y) := by
  have hlo := lo.isLt
  by_cases hy : y = 0#sz.bits
  · subst hy; simp [divide]
  · have hy' : y.toNat ≠ 0 := fun e => hy (BitVec.eq_of_toNat_eq (by simpa using e))
    have hq : lo.toNat / y.toNat < 2 ^ sz.bits :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlo
    simp only [divide, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat, Nat.zero_mod,
      Nat.zero_mul, Nat.zero_add, hy', hy, Nat.not_le.mpr hq]
    congr 2
    · exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_udiv, Nat.mod_eq_of_lt hq])
    · exact BitVec.eq_of_toNat_eq (by
        simp [BitVec.toNat_umod, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hlo)])

private theorem fill_toInt {n : Nat} (hn : 0 < n) (lo : BitVec n) :
    ((if lo.msb then BitVec.allOnes n else 0#n) ++ lo).toInt = lo.toInt := by
  rw [BitVec.toInt_append, BitVec.toInt_eq_msb_cond lo]
  have : (n == 0) = false := by simp; omega
  rw [this]
  cases h : lo.msb <;> simp [BitVec.toInt_allOnes, hn]
  omega

/-- IDIV after CDQ/CQO (the high half is the sign fill of the low half, as
`exec_cxd` writes it) is `BitVec.sdiv`/`srem`; `#DE` exactly on a zero divisor
or on the one overflowing quotient, the most negative value divided by -1. -/
theorem divide_signed (sz : Sz) (lo y : BitVec sz.bits) :
    divide sz true (if lo.msb then BitVec.allOnes sz.bits else 0#sz.bits) lo y =
      if y = 0#sz.bits ∨ (lo = BitVec.intMin sz.bits ∧ y = BitVec.allOnes sz.bits) then none
      else some (lo.sdiv y, lo.srem y) := by
  have hn := sz.bits_pos
  simp only [divide, ite_true, fill_toInt hn]
  by_cases hy : y = 0#sz.bits
  · subst hy; simp
  have hy' : y.toInt ≠ 0 := fun e => hy (BitVec.toInt_inj.mp (by simpa using e))
  simp only [hy', hy, false_or, ite_false]
  by_cases hm : lo = BitVec.intMin sz.bits ∧ y = BitVec.allOnes sz.bits
  · obtain ⟨rfl, rfl⟩ := hm
    simp only [and_self, ite_true, BitVec.toInt_allOnes, hn, BitVec.toInt_intMin]
    cases sz <;> simp
  · simp only [hm, ite_false]
    have hne : lo ≠ BitVec.intMin sz.bits ∨ y ≠ -1#sz.bits := by
      by_cases h1 : lo = BitVec.intMin sz.bits
      · right; intro h2; apply hm; refine ⟨h1, ?_⟩; rw [h2]; exact BitVec.neg_one_eq_allOnes
      · exact .inl h1
    have hq := BitVec.toInt_sdiv_of_ne_or_ne lo y hne
    have hlo := BitVec.le_toInt (lo.sdiv y)
    have hhi := BitVec.toInt_lt (x := lo.sdiv y)
    rw [hq] at hlo hhi
    have : ¬ (lo.toInt.tdiv y.toInt < -2 ^ (sz.bits - 1) ∨
        2 ^ (sz.bits - 1) ≤ lo.toInt.tdiv y.toInt) := by
      omega
    simp only [this, ite_false, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rw [← hq, BitVec.ofInt_toInt]
    · rw [← BitVec.toInt_srem, BitVec.ofInt_toInt]

/-- The high half written by CDQ/CQO, read back at the same size. -/
theorem cxd_read_rdx (sz : Sz) :
    sz.read (sz.write s .rdx
      (if (sz.read s .rax).msb then BitVec.allOnes sz.bits else 0#sz.bits)) .rdx =
      if (sz.read s .rax).msb then BitVec.allOnes sz.bits else 0#sz.bits :=
  Sz.read_write _ _ _ _

end Silmaril.X86.Ext
