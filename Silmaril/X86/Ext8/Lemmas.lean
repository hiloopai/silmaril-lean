module

public import Silmaril.X86.Ext8.Basic

/-! # Rewriting lemmas for the `Ext8` byte forms

`simp` lemmas that evaluate the new forms on register operands and on readable
memory, so a symbolic proof over a transcription (`Transcript8`) can step through
an 8-bit compare or shift without unfolding the decoder. Each is `rfl` or a
one-line `simp` from the definitions.
-/

@[expose] public section

namespace Silmaril.X86.Ext8

open Silmaril.X86 (Reg Word State Flags AluOp)
open Silmaril.X86.Ext (Mem Result retire loadN writeByte)
open Silmaril.Process (Memory)

@[simp] theorem BReg.read_low (s : State) (r : Reg) :
    (BReg.low r).read s = (s.read r).setWidth 8 := rfl

@[simp] theorem BReg.read_high (s : State) (r : Reg) :
    (BReg.high r).read s = (s.read r).extractLsb' 8 8 := rfl

@[simp] theorem RM8.read_reg (b : BReg) (s : State) (memory : Memory) (next : Word) :
    (RM8.reg b).read s memory next = some (b.read s) := rfl

@[simp] theorem RM8.read_mem (m : Mem) (s : State) (memory : Memory) (next : Word) :
    (RM8.mem m).read s memory next =
      (loadN memory (m.addr s next) 1).map fun v => v.setWidth 8 := rfl

@[simp] theorem RM8.write_reg (b : BReg) (v : BitVec 8) (s : State) (memory : Memory)
    (next : Word) : (RM8.reg b).write v s memory next = some (b.write s v, memory) := rfl

@[simp] theorem BReg.write_rip (s : State) (b : BReg) (v : BitVec 8) :
    (b.write s v).rip = s.rip := by cases b <;> rfl

@[simp] theorem BReg.write_flags (s : State) (b : BReg) (v : BitVec 8) :
    (b.write s v).flags = s.flags := by cases b <;> rfl

/-- An 8-bit compare only sets the flags. -/
theorem alu8_cmp {dst : RM8} {y x : BitVec 8} {s : State} {memory : Memory} {next : Word}
    (h : dst.read s memory next = some x) :
    alu8 .cmp dst y s memory next = some ({ s with flags := Ext.subFlagsN x y }, memory) := by
  simp [alu8, h, Ext.AluOp.flagsN]

/-- `cmp r/m8, r8` retires with the byte-subtraction flags. -/
theorem execNew_alu_cmp {dst : RM8} {src : BReg} {x : BitVec 8} {s : State}
    {memory : Memory} {next : Word} (h : dst.read s memory next = some x) :
    execNew (.alu .cmp dst src) s memory next =
      .ok { s with flags := Ext.subFlagsN x (src.read s), rip := next } memory := by
  simp [execNew, alu8_cmp h, retire]

/-- `cmp r8, r/m8` retires with the byte-subtraction flags. -/
theorem execNew_aluR_cmp {dst : BReg} {src : RM8} {y : BitVec 8} {s : State}
    {memory : Memory} {next : Word} (h : src.read s memory next = some y) :
    execNew (.aluR .cmp dst src) s memory next =
      .ok { s with flags := Ext.subFlagsN (dst.read s) y, rip := next } memory := by
  simp [execNew, h, alu8_cmp (dst := .reg dst) (x := dst.read s) rfl, retire]

/-- A non-compare 8-bit ALU form on a register writes the byte and sets the flags. -/
theorem execNew_alu_reg {op : AluOp} (hop : op ≠ .cmp) (d src : BReg) (s : State)
    (memory : Memory) (next : Word) :
    execNew (.alu op (.reg d) src) s memory next =
      .ok { d.write s (Ext.AluOp.resultN op (d.read s) (src.read s)) with
        flags := Ext.AluOp.flagsN op (d.read s) (src.read s), rip := next } memory := by
  simp [execNew, alu8, hop, retire]

/-- `shr`/`shl`/`sar r8, imm8` with a nonzero masked count. -/
theorem execNew_shift_reg_imm {op : Ext.ShiftOp} (d : BReg) (n : BitVec 8) (s : State)
    (memory : Memory) (next : Word) (hc : n.toNat % 32 ≠ 0) :
    execNew (.shift op (.reg d) (.imm n)) s memory next =
      .ok { d.write s (op.result (d.read s) (n.toNat % 32)) with
        flags := shift8Flags op (d.read s) (n.toNat % 32) s.flags, rip := next } memory := by
  simp [execNew, hc, Ext.Count.raw, retire]

/-- `movzx`/`movsx` from a byte register. -/
theorem execNew_movx_reg (sx : Bool) (sz : Ext.Sz) (dst : Reg) (b : BReg) (s : State)
    (memory : Memory) (next : Word) :
    execNew (.movx sx sz dst (.reg b)) s memory next =
      .ok { sz.write s dst (if sx then (b.read s).signExtend sz.bits
        else (b.read s).setWidth sz.bits) with rip := next } memory := rfl

end Silmaril.X86.Ext8
