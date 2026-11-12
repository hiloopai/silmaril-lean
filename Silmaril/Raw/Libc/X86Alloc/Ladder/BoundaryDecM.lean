module

public import Silmaril.Libc.X86Alloc.Ladder.Boundary.Defs
public import Silmaril.Raw.Libc.X86Alloc.Steps
public import Silmaril.Raw.Libc.X86Alloc.MemForms
public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryList
public import Silmaril.Raw.Libc.X86Alloc.Loop
public import Silmaril.X86.Sep.Alloc.Thms

/-! # Proofs: rung 08 (boundary tags) — the listing of `malloc`, decoded once -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary

open Silmaril.X86 (Word Byte Reg Flags)
open Silmaril.Libc.X86Alloc.Insn
open Silmaril.Libc.X86Alloc.Ladder.Boundary

/-- The operand `d(%b,%i,1)`. -/
def idx (b i : Reg) (h : i ≠ .rsp) (d : BitVec 32) : Silmaril.X86.Ext.Mem :=
  ⟨.reg b, some ⟨i, 0, h⟩, d, fun h => by cases h⟩

theorem idx_addr (b i : Reg) (h : i ≠ .rsp) (d : BitVec 32) (s : Silmaril.X86.State) (next : Word) :
    (idx b i h d).addr s next = s.read b + s.read i + d.signExtend 64 := by
  simp [Silmaril.X86.Ext.Mem.addr, idx, Silmaril.X86.Ext.Base.value, Silmaril.X86.Ext.Index.value]

theorem hlen : code.length = 576 := by decide +kernel

theorem fit (o k : Nat) (h : o + k ≤ 576 := by decide) : o + k ≤ code.length := hlen ▸ h

theorem d0 : Silmaril.X86.Ext.decode ((code.drop 0).take 7) =
    some (.aluI .q .cmp (.reg .rdi) 0x1000, 7) := by
  decide +kernel
theorem d7 : Silmaril.X86.Ext.decode ((code.drop 7).take 6) =
    some (.jcc .a 0xdb, 6) := by
  decide +kernel
theorem d13 : Silmaril.X86.Ext.decode ((code.drop 13).take 4) =
    some (.aluI8 .q .add (.reg .rdi) 0xf, 4) := by
  decide +kernel
theorem d17 : Silmaril.X86.Ext.decode ((code.drop 17).take 5) =
    some (.movI32 .rax 0x20, 5) := by
  decide +kernel
theorem d22 : Silmaril.X86.Ext.decode ((code.drop 22).take 4) =
    some (.aluI8 .q .and (.reg .rdi) 0xf0, 4) := by
  decide +kernel
theorem d26 : Silmaril.X86.Ext.decode ((code.drop 26).take 4) =
    some (.lea .q .rdx (Silmaril.X86.Sep.Insn.memAt .rdi 0x10), 4) := by
  decide +kernel
theorem d30 : Silmaril.X86.Ext.decode ((code.drop 30).take 3) =
    some (.alu .q .cmp (.reg .rdx) .rax, 3) := by
  decide +kernel
theorem d33 : Silmaril.X86.Ext.decode ((code.drop 33).take 4) =
    some (.cmov .q .b .rdx (.reg .rax), 4) := by
  decide +kernel
theorem d37 : Silmaril.X86.Ext.decode ((code.drop 37).take 7) =
    some (.load .q .rax (ripMem 0x1d44), 7) := by
  decide +kernel
theorem d44 : Silmaril.X86.Ext.decode ((code.drop 44).take 3) =
    some (.test .q (.reg .rax) .rax, 3) := by
  decide +kernel
theorem d47 : Silmaril.X86.Ext.decode ((code.drop 47).take 2) =
    some (.jcc8 .ne 0x10, 2) := by
  decide +kernel
theorem r49 : (code.drop 49).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem d56 : Silmaril.X86.Ext.decode ((code.drop 56).take 4) =
    some (.load .q .rax (Silmaril.X86.Sep.Insn.memAt .rax 0x8), 4) := by
  decide +kernel
theorem d60 : Silmaril.X86.Ext.decode ((code.drop 60).take 3) =
    some (.test .q (.reg .rax) .rax, 3) := by
  decide +kernel
theorem d63 : Silmaril.X86.Ext.decode ((code.drop 63).take 2) =
    some (.jcc8 .e 0x5f, 2) := by
  decide +kernel
theorem d65 : Silmaril.X86.Ext.decode ((code.drop 65).take 3) =
    some (.alu .q .cmp (.mem (Silmaril.X86.Sep.Insn.memAt .rax 0x0)) .rdx, 3) := by
  decide +kernel
theorem d68 : Silmaril.X86.Ext.decode ((code.drop 68).take 2) =
    some (.jcc8 .b 0xf2, 2) := by
  decide +kernel
theorem d70 : Silmaril.X86.Ext.decode ((code.drop 70).take 3) =
    some (.load .q .rcx (Silmaril.X86.Sep.Insn.memAt .rax 0x0), 3) := by
  decide +kernel
theorem d73 : Silmaril.X86.Ext.decode ((code.drop 73).take 3) =
    some (.mov .q (.reg .rsi) .rax, 3) := by
  decide +kernel
theorem d76 : Silmaril.X86.Ext.decode ((code.drop 76).take 7) =
    some (.aluI .q .sub (.reg .rsi) 0x4032c0, 7) := by
  decide +kernel
theorem d83 : Silmaril.X86.Ext.decode ((code.drop 83).take 3) =
    some (.mov .q (.reg .rdi) .rcx, 3) := by
  decide +kernel
theorem d86 : Silmaril.X86.Ext.decode ((code.drop 86).take 4) =
    some (.shift .q .shr (.reg .rsi) (.imm 0x4), 4) := by
  decide +kernel
theorem d90 : Silmaril.X86.Ext.decode ((code.drop 90).take 4) =
    some (.shift .q .shr (.reg .rcx) (.imm 0x4), 4) := by
  decide +kernel
theorem d94 : Silmaril.X86.Ext.decode ((code.drop 94).take 3) =
    some (.alu .q .sub (.reg .rdi) .rdx, 3) := by
  decide +kernel
theorem d97 : Silmaril.X86.Ext.decode ((code.drop 97).take 5) =
    some (.lea .q .r8 (idx .rsi .rcx (by decide) 0xffffffff), 5) := by
  decide +kernel
theorem d102 : Silmaril.X86.Ext.decode ((code.drop 102).take 4) =
    some (.aluI8 .q .cmp (.reg .rdi) 0x1f, 4) := by
  decide +kernel
theorem d106 : Silmaril.X86.Ext.decode ((code.drop 106).take 2) =
    some (.jcc8 .a 0x3c, 2) := by
  decide +kernel
theorem d108 : Silmaril.X86.Ext.decode ((code.drop 108).take 4) =
    some (.load .q .rcx (Silmaril.X86.Sep.Insn.memAt .rax 0x10), 4) := by
  decide +kernel
theorem d112 : Silmaril.X86.Ext.decode ((code.drop 112).take 4) =
    some (.load .q .rdx (Silmaril.X86.Sep.Insn.memAt .rax 0x8), 4) := by
  decide +kernel
theorem d116 : Silmaril.X86.Ext.decode ((code.drop 116).take 3) =
    some (.test .q (.reg .rcx) .rcx, 3) := by
  decide +kernel
theorem d119 : Silmaril.X86.Ext.decode ((code.drop 119).take 2) =
    some (.jcc8 .e 0x5f, 2) := by
  decide +kernel
theorem d121 : Silmaril.X86.Ext.decode ((code.drop 121).take 4) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rcx 0x8)) .rdx, 4) := by
  decide +kernel
theorem d125 : Silmaril.X86.Ext.decode ((code.drop 125).take 3) =
    some (.test .q (.reg .rdx) .rdx, 3) := by
  decide +kernel
theorem d128 : Silmaril.X86.Ext.decode ((code.drop 128).take 2) =
    some (.jcc8 .e 0x4, 2) := by
  decide +kernel
theorem d130 : Silmaril.X86.Ext.decode ((code.drop 130).take 4) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rdx 0x10)) .rcx, 4) := by
  decide +kernel
theorem d134 : Silmaril.X86.Ext.decode ((code.drop 134).take 7) =
    some (.movI8 (.mem (Silmaril.X86.Sep.Insn.memAt .rsi 0x4031c0)) 0x0, 7) := by
  decide +kernel
theorem d141 : Silmaril.X86.Ext.decode ((code.drop 141).take 4) =
    some (.aluI8 .q .add (.reg .rax) 0x10, 4) := by
  decide +kernel
theorem d145 : Silmaril.X86.Ext.decode ((code.drop 145).take 8) =
    some (.movI8 (.mem (Silmaril.X86.Sep.Insn.memAt .r8 0x4030c0)) 0x0, 8) := by
  decide +kernel
theorem r153 : (code.drop 153).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem r160 : (code.drop 160).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem d168 : Silmaril.X86.Ext.decode ((code.drop 168).take 3) =
    some (.mov .q (.reg .rcx) .rdi, 3) := by
  decide +kernel
theorem d171 : Silmaril.X86.Ext.decode ((code.drop 171).take 3) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rax 0x0)) .rdi, 3) := by
  decide +kernel
theorem d174 : Silmaril.X86.Ext.decode ((code.drop 174).take 4) =
    some (.shift .q .shr (.reg .rcx) (.imm 0x4), 4) := by
  decide +kernel
theorem d178 : Silmaril.X86.Ext.decode ((code.drop 178).take 5) =
    some (.mov .q (.mem (idx .rax .rdi (by decide) 0xfffffff8)) .rdi, 5) := by
  decide +kernel
theorem d183 : Silmaril.X86.Ext.decode ((code.drop 183).take 3) =
    some (.alu .q .add (.reg .rax) .rdi, 3) := by
  decide +kernel
theorem d186 : Silmaril.X86.Ext.decode ((code.drop 186).take 8) =
    some (.movI8 (.mem (idx .rsi .rcx (by decide) 0x4030bf)) 0x1, 8) := by
  decide +kernel
theorem d194 : Silmaril.X86.Ext.decode ((code.drop 194).take 4) =
    some (.aluI8 .q .add (.reg .rax) 0x10, 4) := by
  decide +kernel
theorem d198 : Silmaril.X86.Ext.decode ((code.drop 198).take 4) =
    some (.mov .q (.mem (Silmaril.X86.Sep.Insn.memAt .rax 0xfffffff0)) .rdx, 4) := by
  decide +kernel
theorem d202 : Silmaril.X86.Ext.decode ((code.drop 202).take 8) =
    some (.movI8 (.mem (Silmaril.X86.Sep.Insn.memAt .r8 0x4030c0)) 0x0, 8) := by
  decide +kernel
theorem r210 : (code.drop 210).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel
theorem d216 : Silmaril.X86.Ext.decode ((code.drop 216).take 7) =
    some (.mov .q (.mem (ripMem 0x1c91)) .rdx, 7) := by
  decide +kernel
theorem d223 : Silmaril.X86.Ext.decode ((code.drop 223).take 2) =
    some (.jmp8 0x9c, 2) := by
  decide +kernel
theorem d232 : Silmaril.X86.Ext.decode ((code.drop 232).take 2) =
    some (.alu .d .xor (.reg .rax) .rax, 2) := by
  decide +kernel
theorem r234 : (code.drop 234).take 1 = Silmaril.X86.Insn.encode .ret := by decide +kernel

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
