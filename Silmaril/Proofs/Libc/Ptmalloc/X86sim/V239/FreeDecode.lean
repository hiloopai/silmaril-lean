module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.V239.Code

/-!
# ptmalloc x86sim, glibc 2.39: decode facts of `free`'s tcache path

The decoded instruction at each offset of `__libc_free` (`f…`) and `_int_free` (`i…`) on the
tcache path of `free`, checked by `decide`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN Mem Index RM Sz Narrow Cond subFlagsN logicFlagsN)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.Libc.Ptmalloc.X86sim
namespace Silmaril.Libc.Ptmalloc.X86sim.V239
set_option maxRecDepth 100000

theorem f0 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 0).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.endbr64)))), 4) := by decide

theorem f4 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 4).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.test (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdi)) (Silmaril.X86.Reg.rdi))))), 3) := by decide

theorem f7 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 7).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.e) 0x000000d3#32)))), 6) := by decide

theorem f13 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 13).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.rbp))))), 1) := by decide

theorem f14 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 14).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rbp)) (Silmaril.X86.Reg.rsp))))), 3) := by decide

theorem f17 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 17).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.r13))))), 2) := by decide

theorem f19 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 19).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.lea (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.r13) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdi (none) 0xfffffff0#32))))), 4) := by decide

theorem f23 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 23).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.r12))))), 2) := by decide

theorem f25 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 25).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.rbx))))), 1) := by decide

theorem f26 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 26).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.sub) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rsp)) 0x18#8)))), 4) := by decide

theorem f30 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 30).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rbx) (Silmaril.X86.Ext.Mem.ofRip 0x00155fa3#32))))), 7) := by decide

theorem f37 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 37).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rax) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdi (none) 0xfffffff8#32))))), 4) := by decide

theorem f41 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 41).take 4) = some (Silmaril.X86.Str9Fs.Instr.new (Silmaril.X86.Str9Fs.New.fs (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.d) (Silmaril.X86.Reg.r12) (Silmaril.X86.Ext.Mem.fsAt 0x00000000#32)))) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rbx (none) 0x00000000#32)), 4) := by decide

theorem f45 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 45).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.testA8 0x02#8)))), 2) := by decide

theorem f47 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 47).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc8 (Silmaril.X86.Ext.Cond.ne) 0x5f#8)))), 2) := by decide

theorem f49 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 49).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rdx) (Silmaril.X86.Ext.Mem.ofRip 0x00155f30#32))))), 7) := by decide

theorem f56 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 56).take 5) = some (Silmaril.X86.Str9Fs.Instr.new (Silmaril.X86.Str9Fs.New.fs (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.fsAt 0x00000000#32)) 0x00#8))) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdx (none) 0x00000000#32)), 5) := by decide

theorem f61 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 61).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.e) 0x000000a5#32)))), 6) := by decide

theorem f67 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 67).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.lea (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rdi) (Silmaril.X86.Ext.Mem.ofRip 0x00156c46#32))))), 7) := by decide

theorem f74 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 74).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.testA8 0x04#8)))), 2) := by decide

theorem f76 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 76).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc8 (Silmaril.X86.Ext.Cond.e) 0x26#8)))), 2) := by decide

theorem f116 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 116).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rsi)) (Silmaril.X86.Reg.r13))))), 3) := by decide

theorem f119 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 119).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.alu (Silmaril.X86.Ext.Sz.d) (Silmaril.X86.AluOp.xor) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdx)) (Silmaril.X86.Reg.rdx))))), 2) := by decide

theorem f121 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 121).take 5) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.call 0xffffd3a2#32)))), 5) := by decide

theorem f126 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 126).take 4) = some (Silmaril.X86.Str9Fs.Instr.new (Silmaril.X86.Str9Fs.New.fs (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.d) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.fsAt 0x00000000#32)) (Silmaril.X86.Reg.r12)))) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rbx (none) 0x00000000#32)), 4) := by decide

theorem f130 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 130).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.add) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rsp)) 0x18#8)))), 4) := by decide

theorem f134 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 134).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.rbx))))), 1) := by decide

theorem f135 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 135).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.r12))))), 2) := by decide

theorem f137 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 137).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.r13))))), 2) := by decide

theorem f139 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 139).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.rbp))))), 1) := by decide

theorem f140 : Silmaril.X86.Str9Fs.decode ((freeCode.drop 140).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.ret)))), 1) := by decide

theorem i0 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 0).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.rbp))))), 1) := by decide

theorem i1 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 1).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rbp)) (Silmaril.X86.Reg.rsp))))), 3) := by decide

theorem i4 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 4).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.r13))))), 2) := by decide

theorem i6 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 6).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.r12))))), 2) := by decide

theorem i8 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 8).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.d) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.r12)) (Silmaril.X86.Reg.rdx))))), 3) := by decide

theorem i11 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 11).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.push (Silmaril.X86.Reg.rbx))))), 1) := by decide

theorem i12 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 12).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.sub) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rsp)) 0x28#8)))), 4) := by decide

theorem i16 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 16).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rcx) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rsi (none) 0x00000008#32))))), 4) := by decide

theorem i20 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 20).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdx)) (Silmaril.X86.Reg.rcx))))), 3) := by decide

theorem i23 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 23).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.and) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdx)) 0xf8#8)))), 4) := by decide

theorem i27 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 27).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rax)) (Silmaril.X86.Reg.rdx))))), 3) := by decide

theorem i30 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 30).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.unary (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.UnOp.neg) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rax)))))), 3) := by decide

theorem i33 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 33).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.alu (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rax)) (Silmaril.X86.Reg.rsi))))), 3) := by decide

theorem i36 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 36).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.b) 0x000001e6#32)))), 6) := by decide

theorem i42 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 42).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.testI8 (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rsi)) 0x0f#8)))), 4) := by decide

theorem i46 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 46).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.ne) 0x000001dc#32)))), 6) := by decide

theorem i52 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 52).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdx)) 0x1f#8)))), 4) := by decide

theorem i56 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 56).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.be) 0x000001e2#32)))), 6) := by decide

theorem i62 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 62).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.d) (Silmaril.X86.AluOp.and) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rcx)) 0x08#8)))), 3) := by decide

theorem i65 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 65).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.ne) 0x000001d9#32)))), 6) := by decide

theorem i71 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 71).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rbx)) (Silmaril.X86.Reg.rdi))))), 3) := by decide

theorem i74 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 74).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rdi) (Silmaril.X86.Ext.Mem.ofRip 0x00158af7#32))))), 7) := by decide

theorem i81 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 81).take 4) = some (Silmaril.X86.Str9Fs.Instr.new (Silmaril.X86.Str9Fs.New.fs (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.r8) (Silmaril.X86.Ext.Mem.fsAt 0x00000000#32)))) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdi (none) 0x00000000#32)), 4) := by decide

theorem i85 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 85).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.test (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.r8)) (Silmaril.X86.Reg.r8))))), 3) := by decide

theorem i88 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 88).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc8 (Silmaril.X86.Ext.Cond.e) 0x3e#8)))), 2) := by decide

theorem i90 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 90).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.lea (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rax) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdx (none) 0xffffffef#32))))), 4) := by decide

theorem i94 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 94).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.shift (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.ShiftOp.shr) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rax)) (Silmaril.X86.Ext.Count.imm 0x04#8))))), 4) := by decide

theorem i98 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 98).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluR (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Reg.rax) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofRip 0x00158f2f#32)))))), 7) := by decide

theorem i105 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 105).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc8 (Silmaril.X86.Ext.Cond.ae) 0x2d#8)))), 2) := by decide

theorem i107 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 107).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.r9) (Silmaril.X86.Ext.Mem.ofRip 0x00158f36#32))))), 7) := by decide

theorem i114 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 114).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.r11) (Silmaril.X86.Ext.Mem.ofRip 0x0015feaf#32))))), 7) := by decide

theorem i121 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 121).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.lea (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.r10) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rsi (none) 0x00000010#32))))), 4) := by decide

theorem i125 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 125).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.alu (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rsi (none) 0x00000018#32)) (Silmaril.X86.Reg.r11))))), 4) := by decide

theorem i129 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 129).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.e) 0x000002a9#32)))), 6) := by decide

theorem i135 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 135).take 5) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.movx false (Silmaril.X86.Ext.Sz.d) (Silmaril.X86.Ext.Narrow.w) (Silmaril.X86.Reg.rdi) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.r8 (some ⟨Silmaril.X86.Reg.rax, 0x1#2, by decide⟩) 0x00000000#32)))))), 5) := by decide

theorem i140 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 140).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rcx)) (Silmaril.X86.Reg.rdi))))), 3) := by decide

theorem i143 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 143).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.alu (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdi)) (Silmaril.X86.Reg.r9))))), 3) := by decide

theorem i146 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 146).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.b) 0x00000140#32)))), 6) := by decide

theorem i472 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 472).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rdx) (Silmaril.X86.Ext.Mem.ofRip 0x0015fd49#32))))), 7) := by decide

theorem i479 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 479).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.d) (Silmaril.X86.AluOp.add) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rcx)) 0x01#8)))), 3) := by decide

theorem i482 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 482).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rsi (none) 0x00000018#32)) (Silmaril.X86.Reg.rdx))))), 4) := by decide

theorem i486 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 486).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdx)) (Silmaril.X86.Reg.r10))))), 3) := by decide

theorem i489 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 489).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.shift (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.ShiftOp.shr) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdx)) (Silmaril.X86.Ext.Count.imm 0x0c#8))))), 4) := by decide

theorem i493 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 493).take 8) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluR (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.xor) (Silmaril.X86.Reg.rdx) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.r8 (some ⟨Silmaril.X86.Reg.rax, 0x3#2, by decide⟩) 0x00000080#32)))))), 8) := by decide

theorem i501 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 501).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rsi (none) 0x00000010#32)) (Silmaril.X86.Reg.rdx))))), 4) := by decide

theorem i505 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 505).take 8) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.r8 (some ⟨Silmaril.X86.Reg.rax, 0x3#2, by decide⟩) 0x00000080#32)) (Silmaril.X86.Reg.r10))))), 8) := by decide

theorem i513 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 513).take 5) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.store (Silmaril.X86.Ext.Narrow.w) (Silmaril.X86.Ext.RM.mem (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.r8 (some ⟨Silmaril.X86.Reg.rax, 0x1#2, by decide⟩) 0x00000000#32)) (Silmaril.X86.Reg.rcx))))), 5) := by decide

theorem i518 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 518).take 5) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jmp 0xffffff22#32)))), 5) := by decide

theorem i301 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 301).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.add) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rsp)) 0x28#8)))), 4) := by decide

theorem i305 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 305).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.rbx))))), 1) := by decide

theorem i306 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 306).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.r12))))), 2) := by decide

theorem i308 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 308).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.r13))))), 2) := by decide

theorem i310 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 310).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.pop (Silmaril.X86.Reg.rbp))))), 1) := by decide

theorem i311 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 311).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.ret)))), 1) := by decide

theorem i816 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 816).take 1) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.nop 0)))), 1) := by decide

theorem i817 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 817).take 4) = some (Silmaril.X86.Str9Fs.Instr.new (Silmaril.X86.Str9Fs.New.fs (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.r8) (Silmaril.X86.Ext.Mem.fsAt 0x00000000#32)))) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdi (none) 0x00000000#32)), 4) := by decide

theorem i821 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 821).take 7) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.r9) (Silmaril.X86.Ext.Mem.ofRip 0x00158c6c#32))))), 7) := by decide

theorem i828 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 828).take 8) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.rdi) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.r8 (some ⟨Silmaril.X86.Reg.rax, 0x3#2, by decide⟩) 0x00000080#32))))), 8) := by decide

theorem i836 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 836).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.test (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdi)) (Silmaril.X86.Reg.rdi))))), 3) := by decide

theorem i839 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 839).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc8 (Silmaril.X86.Ext.Cond.ne) 0x2d#8)))), 2) := by decide

theorem i841 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 841).take 5) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jmp 0xfffffd39#32)))), 5) := by decide

theorem i848 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 848).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.alu (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdi)) (Silmaril.X86.Reg.r10))))), 3) := by decide

theorem i851 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 851).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.e) 0x0000008a#32)))), 6) := by decide

theorem i857 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 857).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.r13)) (Silmaril.X86.Reg.rdi))))), 3) := by decide

theorem i860 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 860).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.load (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Reg.r11) (Silmaril.X86.Ext.Mem.ofReg Silmaril.X86.Reg.rdi (none) 0x00000000#32))))), 3) := by decide

theorem i863 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 863).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.aluI8 (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.add) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rcx)) 0x01#8)))), 4) := by decide

theorem i867 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 867).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.shift (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.ShiftOp.shr) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.r13)) (Silmaril.X86.Ext.Count.imm 0x0c#8))))), 4) := by decide

theorem i871 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 871).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.mov (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdi)) (Silmaril.X86.Reg.r13))))), 3) := by decide

theorem i874 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 874).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.alu (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.xor) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdi)) (Silmaril.X86.Reg.r11))))), 3) := by decide

theorem i877 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 877).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.alu (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.r13)) (Silmaril.X86.Reg.r11))))), 3) := by decide

theorem i880 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 880).take 6) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc (Silmaril.X86.Ext.Cond.e) 0xfffffd11#32)))), 6) := by decide

theorem i886 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 886).take 3) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.alu (Silmaril.X86.Ext.Sz.q) (Silmaril.X86.AluOp.cmp) (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rcx)) (Silmaril.X86.Reg.r9))))), 3) := by decide

theorem i889 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 889).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc8 (Silmaril.X86.Ext.Cond.e) 0x74#8)))), 2) := by decide

theorem i891 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 891).take 4) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.testI8 (Silmaril.X86.Ext.RM.reg (Silmaril.X86.Reg.rdi)) 0x0f#8)))), 4) := by decide

theorem i895 : Silmaril.X86.Str9Fs.decode ((intFreeCode.drop 895).take 2) = some (Silmaril.X86.Str9Fs.Instr.str9 (Silmaril.X86.Str9.Instr.ext9 (Silmaril.X86.Ext9.Instr.ext8 (Silmaril.X86.Ext8.Instr.base (Silmaril.X86.Ext.Instr.jcc8 (Silmaril.X86.Ext.Cond.e) 0xcf#8)))), 2) := by decide

end Silmaril.Libc.Ptmalloc.X86sim.V239
