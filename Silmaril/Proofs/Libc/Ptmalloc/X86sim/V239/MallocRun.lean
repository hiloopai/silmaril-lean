module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.Code

/-!
# ptmalloc x86sim, glibc 2.39: `__libc_malloc`'s prologue and checks, as machine runs

The non-heap blocks of `__libc_malloc`'s tcache path (entry → the bin's count test): the
prologue's four pushes (`prologue`, offsets `0x0`–`0x13`) and the checks (`checks`,
`0x14`–`0x64`: `__malloc_initialized`, the sign of the request, the bin index `tcIdx`, the
thread's tcache pointer through the GOT slot of its TLS offset, `tc_idx < mp_.tcache_bins`).
They touch no heap state, so they carry over unchanged from the existing proof; the heap-facing
blocks (`tcache_get`) are the generic ones of `Silmaril.Proofs.Libc.Ptmalloc.X86sim`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN subFlagsN logicFlagsN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.Libc.Ptmalloc.X86sim
namespace Silmaril.Libc.Ptmalloc.X86sim.V239
variable {A : Word}
set_option maxRecDepth 100000

theorem d0 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 0).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.endbr64)))), 4) := by decide

theorem d4 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 4).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.rbp))))), 1) := by decide

theorem d5 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 5).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rbp)) (Silmaril.X86.Reg.rsp))))), 3) := by decide

theorem d8 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 8).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.r13))))), 2) := by decide

theorem d10 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 10).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.r12))))), 2) := by decide

theorem d12 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 12).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.rbx))))), 1) := by decide

theorem d13 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 13).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rbx)) (Silmaril.X86.Reg.rdi))))), 3) := by decide

theorem d16 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 16).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.sub) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rsp)) 0x18#8)))), 4) := by decide

theorem d20 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 20).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.cmpI8 (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofRip 0x0015da1d#32)) 0x00#8)))), 7) := by decide

theorem d27 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 27).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.e) 0x000001ef#32)))), 6) := by decide

theorem d33 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 33).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.test (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rbx)) (Silmaril.X86.Reg.rbx))))), 3) := by decide

theorem d36 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 36).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.s) 0x000001f4#32)))), 6) := by decide

theorem d42 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 42).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.lea (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rax) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rbx (none) 0x00000017#32))))), 4) := by decide

theorem d46 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 46).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.alu (Silmaril.X86.Ext.Sz.d) (Silmaril.X86.AluOp.xor) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.r12)) (Silmaril.X86.Reg.r12))))), 3) := by decide

theorem d49 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 49).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rax)) 0x1f#8)))), 4) := by decide

theorem d53 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 53).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc8 (Silmaril.X86.Ext.Cond.be) 0x0c#8)))), 2) := by decide

theorem d55 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 55).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.and) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rax)) 0xf0#8)))), 4) := by decide

theorem d59 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 59).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.lea (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.r12) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rax (none) 0xffffffef#32))))), 4) := by decide

theorem d63 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 63).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.shift (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.ShiftOp.shr) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.r12)) (Silmaril.X86.Ext.Count.imm 0x04#8))))), 4) := by decide

theorem d67 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 67).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.r13) (Silmaril.X86.Ext.Mem.ofRip 0x001565fe#32))))), 7) := by decide

theorem d74 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 74).take 5) = some (Silmaril.X86.Str9Fs.Instr.new (Silmaril.X86.Str9Fs.New.fs (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rdx) (Silmaril.X86.Ext.Mem.fsAt 0x00000000#32)))) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.r13 (none) 0x00000000#32)), 5) := by decide

theorem d79 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 79).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.test (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdx)) (Silmaril.X86.Reg.rdx))))), 3) := by decide

theorem d82 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 82).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.e) 0x000000b8#32)))), 6) := by decide

theorem d88 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 88).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluR (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Reg.r12) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofRip 0x00156a39#32)))))), 7) := by decide

theorem d95 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 95).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.b) 0x000000e3#32)))), 6) := by decide

theorem d328 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 328).take 5) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.movx false (Silmaril.X86.Ext.Sz.d) (Silmaril.X86.Ext.Narrow.w) (Silmaril.X86.Reg.rcx) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdx (some ⟨Silmaril.X86.Reg.r12, 0x1#2, by decide⟩) 0x00000000#32)))))), 5) := by decide

theorem d333 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 333).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.new (Silmaril.X86.Ext9.New.test16 (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rcx)) (Silmaril.X86.Reg.rcx)))), 3) := by decide

theorem d336 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 336).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.e) 0xffffff0f#32)))), 6) := by decide

theorem d342 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 342).take 5) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.lea (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rdi) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.r12 (none) 0x00000010#32))))), 5) := by decide

theorem d347 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 347).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rax) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdx (some ⟨Silmaril.X86.Reg.rdi, 0x3#2, by decide⟩) 0x00000000#32))))), 4) := by decide

theorem d351 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 351).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.testA8 0x0f#8)))), 2) := by decide

theorem d353 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 353).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.ne) 0x00000189#32)))), 6) := by decide

theorem d359 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 359).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rsi)) (Silmaril.X86.Reg.rax))))), 3) := by decide

theorem d362 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 362).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.d) (Silmaril.X86.AluOp.sub) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rcx)) 0x01#8)))), 3) := by decide

theorem d365 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 365).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.shift (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.ShiftOp.shr) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rsi)) (Silmaril.X86.Ext.Count.imm 0x0c#8))))), 4) := by decide

theorem d369 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 369).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluR (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.xor) (Silmaril.X86.Reg.rsi) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rax (none) 0x00000000#32)))))), 3) := by decide

theorem d372 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 372).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdx (some ⟨Silmaril.X86.Reg.rdi, 0x3#2, by decide⟩) 0x00000000#32)) (Silmaril.X86.Reg.rsi))))), 4) := by decide

theorem d376 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 376).take 5) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.store (Silmaril.X86.Ext.Narrow.w) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdx (some ⟨Silmaril.X86.Reg.r12, 0x1#2, by decide⟩) 0x00000000#32)) (Silmaril.X86.Reg.rcx))))), 5) := by decide

theorem d381 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 381).take 8) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.movI (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rax (none) 0x00000008#32)) 0x00000000#32)))), 8) := by decide

theorem d389 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 389).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.add) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rsp)) 0x18#8)))), 4) := by decide

theorem d393 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 393).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.rbx))))), 1) := by decide

theorem d394 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 394).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.r12))))), 2) := by decide

theorem d396 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 396).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.r13))))), 2) := by decide

theorem d398 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 398).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.rbp))))), 1) := by decide

theorem d399 : Silmaril.X86.Str9Fs.decode ((mallocCode.drop 399).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.ret)))), 1) := by decide



/-- The stack slots `[sp - 32, sp)`. -/
def stk (sp : Word) (a : Nat) : Prop := sp.toNat - 32 ≤ a ∧ a < sp.toNat

theorem exec_push {c : State} {mem mem' : Memory} {r : Reg} {l : Nat}
    (h : Silmaril.X86.pushWord c mem (c.read r) = some (c.write .rsp (c.read .rsp - 8#64), mem')) :
    Str9Fs.exec (.str9 (.ext9 (.ext8 (.base (.push r))))) c mem l =
      .ok { c.write .rsp (c.read .rsp - 8#64) with rip := c.rip + BitVec.ofNat 64 l } mem' := by
  rw [exec_base]; simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, h]

/-- One push inside the slots: it writes only there, and reads back. -/
theorem push_facts {c : State} {mem : Memory} {v sp : Word} (k : Nat) (hk : k < 4)
    (hsp : 32 ≤ sp.toNat) (hrsp : c.read .rsp = sp - BitVec.ofNat 64 (8 * k))
    (hw : mem.Permitted .write (sp.toNat - 32) 32) (hr : mem.Permitted .read (sp.toNat - 32) 32) :
    ∃ mem', Silmaril.X86.pushWord c mem v = some (c.write .rsp (c.read .rsp - 8#64), mem') ∧
      mem.WritesWithin mem' (stk sp) ∧
      mem'.readBytes (sp.toNat - 8 * (k + 1)) 8 = some (encodeWords [v]) ∧
      mem'.Permitted .write (sp.toNat - 32) 32 ∧ mem'.Permitted .read (sp.toNat - 32) 32 := by
  have ha : (c.read .rsp - 8#64).toNat = sp.toNat - 8 * (k + 1) := by
    rw [hrsp]; bv_omega
  have hsub : ∀ {acc}, mem.Permitted acc (sp.toNat - 32) 32 → mem.Permitted acc (sp.toNat - 8 * (k + 1)) 8 := by
    intro acc h
    simp only [Memory.Permitted, Memory.checkSpan_iff] at h ⊢
    refine ⟨by omega, by omega, fun o ho => ?_⟩
    have := h.2.2 (32 - 8 * (k + 1) + o) (by omega)
    rwa [show sp.toNat - 32 + (32 - 8 * (k + 1) + o) = sp.toNat - 8 * (k + 1) + o by omega] at this
  have hp := Silmaril.X86.pushWord_eq_some (s := c) (value := v) (by rw [ha]; exact hsub hw)
  refine ⟨_, hp, ?_, ?_, ?_, ?_⟩
  · have wo := Silmaril.X86.pushWord_writesOnly hp
    rw [Memory.writesOnly_iff_writesWithin] at wo
    refine wo.mono ?_
    intro a ⟨h1, h2⟩; rw [ha] at h1 h2; exact ⟨by omega, by omega⟩
  · rw [← ha]; exact Silmaril.X86.pushWord_readBytes hp (by rw [ha]; exact hsub hr)
  · exact hw
  · exact hr


theorem slot_apart {sp : Word} {k j : Nat} (hkj : k ≠ j) (hk : k < 4) (hj : j < 4) (hsp : 32 ≤ sp.toNat) :
    ∀ i < 8, ¬ (sp.toNat - 8 * (j + 1) ≤ sp.toNat - 8 * (k + 1) + i ∧
      sp.toNat - 8 * (k + 1) + i < sp.toNat - 8 * (j + 1) + 8) := by
  intro i hi ⟨h1, h2⟩; omega
/-- Slot `k` below `sp`. -/
def slot (sp : Word) (k : Nat) (a : Nat) : Prop := sp.toNat - 8 * (k + 1) ≤ a ∧ a < sp.toNat - 8 * (k + 1) + 8

theorem slot_stk {sp : Word} {k : Nat} (hk : k < 4) (hsp : 32 ≤ sp.toNat) {a : Nat} (h : slot sp k a) :
    stk sp a := by unfold slot at h; unfold stk; omega

theorem push_slot {c : State} {mem : Memory} {v sp : Word} (k : Nat) (hk : k < 4)
    (hsp : 32 ≤ sp.toNat) (hrsp : c.read .rsp = sp - BitVec.ofNat 64 (8 * k))
    (hw : mem.Permitted .write (sp.toNat - 32) 32) (hr : mem.Permitted .read (sp.toNat - 32) 32) :
    ∃ mem', Silmaril.X86.pushWord c mem v = some (c.write .rsp (c.read .rsp - 8#64), mem') ∧
      mem.WritesWithin mem' (slot sp k) ∧
      mem'.readBytes (sp.toNat - 8 * (k + 1)) 8 = some (encodeWords [v]) ∧
      mem'.Permitted .write (sp.toNat - 32) 32 ∧ mem'.Permitted .read (sp.toNat - 32) 32 := by
  have ha : (c.read .rsp - 8#64).toNat = sp.toNat - 8 * (k + 1) := by
    rw [hrsp]; bv_omega
  obtain ⟨mem', hp, -, hb, hw', hr'⟩ := push_facts (v := v) k hk hsp hrsp hw hr
  refine ⟨mem', hp, ?_, hb, hw', hr'⟩
  have wo := Silmaril.X86.pushWord_writesOnly hp
  rw [Memory.writesOnly_iff_writesWithin] at wo
  refine wo.mono ?_
  intro a ⟨h1, h2⟩; rw [ha] at h1 h2; exact ⟨h1, h2⟩

/-- **A push as a continuation**: the new memory, its frame and the pushed slot. -/
theorem ex_push {P : MState → Prop} {m : MState} {sp : Word} {k o l : Nat} {r : Reg}
    (hl : Loaded m.memory A mallocCode) (hrip : m.core.rip = A + BitVec.ofNat 64 o)
    (hfit : o + l ≤ 796)
    (hdec : Str9Fs.decode ((mallocCode.drop o).take l) = some (.str9 (.ext9 (.ext8 (.base (.push r)))), l))
    (hk : k < 4) (hsp : 32 ≤ sp.toNat) (hrsp : m.core.read .rsp = sp - BitVec.ofNat 64 (8 * k))
    (hw : m.memory.Permitted .write (sp.toNat - 32) 32) (hr : m.memory.Permitted .read (sp.toNat - 32) 32)
    (hcode : ∀ i < 796, ¬ stk sp (A.toNat + i))
    (cont : ∀ mem', m.memory.WritesWithin mem' (slot sp k) →
      mem'.readBytes (sp.toNat - 8 * (k + 1)) 8 = some (encodeWords [m.core.read r]) →
      mem'.Permitted .write (sp.toNat - 32) 32 → mem'.Permitted .read (sp.toNat - 32) 32 →
      Loaded mem' A mallocCode →
      ∃ u, Reaches Str9Fs.step
        ⟨{ m.core.write .rsp (m.core.read .rsp - 8#64) with rip := m.core.rip + BitVec.ofNat 64 l }, mem'⟩ u ∧ P u) :
    ∃ u, Reaches Str9Fs.step m u ∧ P u := by
  obtain ⟨mem', hp, hw', hb, hw2, hr2⟩ := push_slot (c := m.core) (mem := m.memory) (v := m.core.read r)
    k hk hsp hrsp hw hr
  exact ex_head (stepC mallocCode_length hl hrip hfit hdec (exec_push hp)) (cont mem' hw' hb hw2 hr2
    (loadedC_ww mallocCode_length hl hw' (fun i hi h => hcode i hi (slot_stk hk hsp h))))

set_option maxHeartbeats 4000000 in
theorem prologue {m : MState} {sp : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 0) (hrsp : m.core.read .rsp = sp) (hsp : 32 ≤ sp.toNat)
    (hw : m.memory.Permitted .write (sp.toNat - 32) 32)
    (hr : m.memory.Permitted .read (sp.toNat - 32) 32)
    (hcode : ∀ i < 796, ¬ stk sp (A.toNat + i)) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 20 ∧
      m'.core.read .rsp = sp - 0x38#64 ∧ m'.core.read .rbp = sp - 8#64 ∧
      m'.core.read .rbx = m.core.read .rdi ∧
      (∀ r, r ≠ .rsp → r ≠ .rbp → r ≠ .rbx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧
      m.memory.WritesWithin m'.memory (stk sp) ∧
      m'.memory.readBytes (sp.toNat - 8) 8 = some (encodeWords [m.core.read .rbp]) ∧
      m'.memory.readBytes (sp.toNat - 16) 8 = some (encodeWords [m.core.read .r13]) ∧
      m'.memory.readBytes (sp.toNat - 24) 8 = some (encodeWords [m.core.read .r12]) ∧
      m'.memory.readBytes (sp.toNat - 32) 8 = some (encodeWords [m.core.read .rbx]) := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrsp hw hr ⊢
  refine ex_head (stepC mallocCode_length (o := 0) (l := 4) hl hrip (by decide) d0 exec_endbr) ?_
  refine ex_push (k := 0) hl (by simp [hrip]) (by decide) d4 (by decide) hsp (by simp [hrsp]) hw hr hcode
    (fun mem1 hw1 hb1 hw1' hr1' hl1 => ?_)
  refine ex_head (stepC mallocCode_length (o := 5) (l := 3) hl1 (by simp [hrip, rip_add]) (by decide) d5 exec_movrr) ?_
  refine ex_push (k := 1) hl1 (by simp [hrip, rip_add]) (by decide) d8 (by decide) hsp (by simp [hrsp]) hw1' hr1' hcode
    (fun mem2 hw2 hb2 hw2' hr2' hl2 => ?_)
  refine ex_push (k := 2) hl2 (by simp [hrip, rip_add]) (by decide) d10 (by decide) hsp (by simp [hrsp]; bv_omega) hw2' hr2' hcode
    (fun mem3 hw3 hb3 hw3' hr3' hl3 => ?_)
  refine ex_push (k := 3) hl3 (by simp [hrip, rip_add]) (by decide) d12 (by decide) hsp (by simp [hrsp]; bv_omega) hw3' hr3' hcode
    (fun mem4 hw4 hb4 hw4' hr4' hl4 => ?_)
  refine ex_head (stepC mallocCode_length (o := 13) (l := 3) hl4 (by simp [hrip, rip_add]) (by decide) d13 exec_movrr) ?_
  refine ex_fC mallocCode_length hl4 (by simp [hrip, rip_add]) (by decide) d16 exec_subrsp (fun f => ?_)
  have e18 : (0x18#8).signExtend 64 = 0x18#64 := by decide
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip, rip_add]
  · simp [hrsp, e18]; bv_omega
  · simp [hrsp]
  · simp
  · intro r h1 h2 h3; simp [Silmaril.X86.State.read_write, h1, h2, h3]
  · rfl
  · exact (((hw1.mono fun a h => slot_stk (by decide) hsp h).trans
      (hw2.mono fun a h => slot_stk (by decide) hsp h)).trans
      (hw3.mono fun a h => slot_stk (by decide) hsp h)).trans
      (hw4.mono fun a h => slot_stk (by decide) hsp h)
  · have := rd_ww hw4 (fun i hi h => slot_apart (k := 0) (j := 3) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h))
      (rd_ww hw3 (fun i hi h => slot_apart (k := 0) (j := 2) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h))
        (rd_ww hw2 (fun i hi h => slot_apart (k := 0) (j := 1) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h)) hb1))
    simpa using this
  · have := rd_ww hw4 (fun i hi h => slot_apart (k := 1) (j := 3) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h))
      (rd_ww hw3 (fun i hi h => slot_apart (k := 1) (j := 2) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h)) hb2)
    simpa using this
  · have := rd_ww hw4 (fun i hi h => slot_apart (k := 2) (j := 3) (by decide) (by decide) (by decide) hsp i hi (by simpa [slot] using h)) hb3
    simpa using this
  · simpa using hb4

/-- The tcache index `malloc` computes from the request `n` (`csize2tidx (request2size n)`,
in machine words). -/
def tcIdx (n : Word) : Word :=
  if (n + 0x17#64).toNat ≤ 0x1f then 0 else (((n + 0x17#64) &&& 0xfffffffffffffff0#64) - 0x11#64) >>> 4

macro "mx" : tactic => `(tactic| simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip, rip_add, BitVec.add_assoc])

theorem ex_of {P Q : MState → Prop} {m : MState} (h : ∃ u, Reaches Str9Fs.step m u ∧ Q u)
    (hq : ∀ u, Q u → P u) : ∃ u, Reaches Str9Fs.step m u ∧ P u := by
  obtain ⟨u, hu, h⟩ := h; exact ⟨u, hu, hq u h⟩

set_option maxHeartbeats 4000000 in
/-- The second half of the checks (offsets `0x43`–`0x64`). -/
theorem checks2 {m : MState} {off tc idx : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 67) (hr12 : m.core.read .r12 = idx)
    (hgot : loadN m.memory (A + 0x156648#64) 8 = some off)
    (htc : loadN m.memory (m.core.fsBase + off) 8 = some tc) (htc0 : tc ≠ 0)
    (hbins : loadN m.memory (A + 0x156a98#64) 8 = some 64#64) (hidx : idx.toNat < 64) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 328 ∧
      m'.core.read .r12 = idx ∧ m'.core.read .rdx = tc ∧
      (∀ r, r ≠ .r13 → r ≠ .rdx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hr12 hgot htc hbins ⊢
  have a67 : c0.rip + BitVec.ofNat 64 7 + (0x1565fe#32).signExtend 64 = A + 0x156648#64 := by
    rw [hrip]; mx
  refine ex_head (stepC mallocCode_length (o := 67) (l := 7) hl hrip (by decide) d67 (exec_loadrip (by rw [a67]; exact hgot))) ?_
  refine ex_head (stepC mallocCode_length (o := 74) (l := 5) hl (by simp [hrip, rip_add]) (by decide) d74
    (exec_fsload (by simpa using htc))) ?_
  refine ex_head (stepC mallocCode_length (o := 79) (l := 3) hl (by simp [hrip, rip_add]) (by decide) d79 exec_testrr) ?_
  refine ex_head (stepC mallocCode_length (o := 82) (l := 6) hl (by simp [hrip, rip_add]) (by decide) d82
    (exec_jcc (b := false) (by simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, Silmaril.X86.Ext.isZeroN]; exact htc0))) ?_
  refine ex_head (stepC mallocCode_length (o := 88) (l := 7) hl (by simp [hrip, rip_add]) (by decide) d88
    (exec_cmprip (v := 64#64) (by simp [hrip, BitVec.add_assoc]; exact hbins))) ?_
  refine ex_head (stepC mallocCode_length (o := 95) (l := 6) hl (by simp [hrip, rip_add]) (by decide) d95
    (exec_jcc (b := true) (by
      simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, hr12, BitVec.ult]
      exact hidx))) ?_
  refine ⟨_, Reaches.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hrip]; mx
  · simp [hr12]
  · simp
  · intro r h1 h2; simp [h1, h2]
  · rfl
  · rfl

set_option maxHeartbeats 4000000 in
/-- **The checks** (offsets `0x14`–`0x64`): initialised, `n ≥ 0`, the index, the tcache
pointer from TLS, `idx < mp_.tcache_bins`; on to the tcache read at `0x148`. -/
theorem checks {m : MState} {n off tc : Word} (hl : Loaded m.memory A mallocCode)
    (hrip : m.core.rip = A + BitVec.ofNat 64 20) (hrbx : m.core.read .rbx = n) (hn : n.msb = false)
    (hinit : loadN m.memory (A + 0x15da38#64) 1 = some 1#64)
    (hgot : loadN m.memory (A + 0x156648#64) 8 = some off)
    (htc : loadN m.memory (m.core.fsBase + off) 8 = some tc) (htc0 : tc ≠ 0)
    (hbins : loadN m.memory (A + 0x156a98#64) 8 = some 64#64) (hidx : (tcIdx n).toNat < 64) :
    ∃ m', Reaches Str9Fs.step m m' ∧ m'.core.rip = A + BitVec.ofNat 64 328 ∧
      m'.core.read .r12 = tcIdx n ∧ m'.core.read .rdx = tc ∧
      (∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .r13 → r ≠ .rdx → m'.core.read r = m.core.read r) ∧
      m'.core.fsBase = m.core.fsBase ∧ m'.memory = m.memory := by
  obtain ⟨c0, mem0⟩ := m
  simp only at hl hrip hrbx hinit hgot htc hbins ⊢
  have a20 : (Silmaril.X86.Ext.Mem.ofRip 0x15da1d#32).addr c0 (c0.rip + BitVec.ofNat 64 7) = A + 0x15da38#64 := by
    rw [hrip]; mx
  refine ex_head (stepC mallocCode_length (o := 20) (l := 7) hl hrip (by decide) d20 (exec_cmpI8m (v := 1#64) (by rw [a20]; exact hinit))) ?_
  refine ex_head (stepC mallocCode_length (o := 27) (l := 6) hl (by simp [hrip, rip_add]) (by decide) d27
    (exec_jcc (b := false) (by simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.isZeroN]))) ?_
  refine ex_head (stepC mallocCode_length (o := 33) (l := 3) hl (by simp [hrip, rip_add]) (by decide) d33 exec_testrr) ?_
  refine ex_head (stepC mallocCode_length (o := 36) (l := 6) hl (by simp [hrip, rip_add]) (by decide) d36
    (exec_jcc (b := false) (by simp [Silmaril.X86.Ext.Cond.eval, logicFlagsN, hrbx, hn]))) ?_
  refine ex_head (stepC mallocCode_length (o := 42) (l := 4) hl (by simp [hrip, rip_add]) (by decide) d42 exec_lea) ?_
  refine ex_fC mallocCode_length hl (by simp [hrip, rip_add]) (by decide) d46 exec_xor32 (fun f1 => ?_)
  refine ex_head (stepC mallocCode_length (o := 49) (l := 4) hl (by simp [hrip, rip_add]) (by decide) d49 exec_cmpI8r) ?_
  have e1f : (0x1f#8).signExtend 64 = 0x1f#64 := by decide
  by_cases hs : (n + 0x17#64).toNat ≤ 0x1f
  · refine ex_head (stepC mallocCode_length (o := 53) (l := 2) hl (by simp [hrip, rip_add]) (by decide) d53
      (exec_jcc8 (b := true) (by
        simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, hrbx, BitVec.ult,
          e1f, Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.isZeroN]
        rcases Nat.lt_or_ge ((BitVec.toNat n + 23) % 18446744073709551616) 31 with h | h
        · simp [h]
        · have h2 : (n + 23#64 - 31#64 == 0#64) = true := by
            simp only [beq_iff_eq]; simp only [BitVec.toNat_add] at hs; bv_omega
          simp only [h2]
          generalize decide ((BitVec.toNat n + 23) % 18446744073709551616 < 31) = d; cases d <;> rfl))) ?_
    refine ex_of (checks2 (off := off) (tc := tc) (idx := 0) hl
      (by simp [hrip, rip_add, BitVec.add_assoc]) (by simp) hgot (by simpa using htc) htc0 hbins (by decide)) ?_
    rintro m' ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, ?_, h3, ?_, ?_, h6⟩
    · rw [h2]; unfold tcIdx; split
      · rfl
      · rename_i hne; exact absurd hs hne
    · intro r a b c d; rw [h4 r c d]; simp [a, b]
    · rw [h5]; rfl
  · refine ex_head (stepC mallocCode_length (o := 53) (l := 2) hl (by simp [hrip, rip_add]) (by decide) d53
      (exec_jcc8 (b := false) (by
        simp [Silmaril.X86.Ext.Cond.eval, subFlagsN, Silmaril.X86.Ext.subBorrowN_eq, hrbx, BitVec.ult,
          e1f, Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.isZeroN]
        have h1 : ¬ ((BitVec.toNat n + 23) % 18446744073709551616 < 31) := by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hs; omega
        have h2 : (n + 23#64 - 31#64 == 0#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hs; bv_omega
        simp [h1, h2]))) ?_
    refine ex_fC mallocCode_length hl (by simp [hrip, rip_add]) (by decide) d55 (exec_aluI8r (op := .and) (by decide)) (fun f2 => ?_)
    refine ex_head (stepC mallocCode_length (o := 59) (l := 4) hl (by simp [hrip, rip_add]) (by decide) d59 exec_lea) ?_
    refine ex_fC mallocCode_length hl (by simp [hrip, rip_add]) (by decide) d63 exec_shr (fun f3 => ?_)
    have ef0 : (0xf0#8).signExtend 64 = 0xfffffffffffffff0#64 := by decide
    have eef : ∀ x : Word, x + (0xffffffef#32).signExtend 64 = x - 0x11#64 := by
      intro x; rw [show (0xffffffef#32).signExtend 64 = 0 - 0x11#64 by decide]; bv_omega
    refine ex_of (checks2 (off := off) (tc := tc) (idx := tcIdx n) hl
      (by simp [hrip, rip_add, BitVec.add_assoc]) ?_ hgot (by simpa using htc) htc0 hbins hidx) ?_
    · simp [Silmaril.X86.Ext.AluOp.resultN, ef0, eef, hrbx, tcIdx, hs]
      have hs' : ¬ ((BitVec.toNat n + 23) % 18446744073709551616 ≤ 31) := by
        simpa [BitVec.toNat_add] using hs
      simp only [hs', ↓reduceIte]
      have e17 : ∀ x : Word, x + 18446744073709551599#64 = x - 17#64 := fun x => by bv_omega
      rw [e17]
    rintro m' ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, ?_, ?_, h6⟩
    · intro r a b c d; rw [h4 r c d]; simp [a, b]
    · rw [h5]; rfl

end Silmaril.Libc.Ptmalloc.X86sim.V239
