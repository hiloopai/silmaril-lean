module

public import Silmaril.X86.Ext.Wire.Machine

/-! # Data spans for successful local x86 instructions

These are user-data spans, not instruction-fetch ranges or decoded operand
addresses. LEA and multi-byte NOP do not access their apparent memory operand.
CMOV reads its source even when false. Read/modify/write uses one span for the
same bytes; the LPS page materializer takes their union. Stack sources use the
old registers, and CALL/PUSH write at old RSP minus eight. These reports are
attached only to successful execution, after all permission/backing checks.

The supported syntax has no REP/string instruction. Such bytes remain
unmodeled by the decoder; no invented range or count is used for them. This
handwritten reporting layer follows the local executor, not a hardware ISA
correspondence theorem.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86Accesses

open Silmaril.X86
open Silmaril.X86.Ext

def rm (core : State) (next : Word) (width : Nat) : RM → List (Word × Nat)
  | .reg _ => []
  | .mem address => [(address.addr core next, width)]

/-- All data spans actually used by a successful canonical instruction.
`length` is the consumed spelling, needed for RIP-relative addressing. -/
def canonical (core : State) (length : Nat) (instruction : Ext.Instr) : List (Word × Nat) :=
  let next := core.rip + BitVec.ofNat 64 length
  match instruction with
  | .mov sz dst _ | .movI sz dst _ => rm core next sz.bytes dst
  | .movI16 dst _ => rm core next 2 dst
  | .mov8 _ src => rm core next 1 src
  | .movI8 dst _ => rm core next 1 dst
  | .load sz _ src => [(src.addr core next, sz.bytes)]
  | .store narrow dst _ => rm core next narrow.bytes dst
  | .movx _ _ narrow _ src => rm core next narrow.bytes src
  | .movsxd _ src => rm core next 4 src
  | .alu sz _ dst _ | .aluI sz _ dst _ | .aluI8 sz _ dst _ => rm core next sz.bytes dst
  | .aluR sz _ _ src => rm core next sz.bytes src
  | .test sz dst _ => rm core next sz.bytes dst
  | .test8 dst _ | .testI8 dst _ | .cmpI8 dst _ => rm core next 1 dst
  | .incdec sz _ dst | .unary sz _ dst | .shift sz _ dst _ => rm core next sz.bytes dst
  | .pushRM src => rm core next 8 src ++ [(core.read .rsp - 8, 8)]
  | .imul sz _ src | .mul sz src | .div sz _ src | .cmov sz _ _ src => rm core next sz.bytes src
  | .setcc _ dst => rm core next 1 dst
  | .call _ | .push _ => [(core.read .rsp - 8, 8)]
  | .ret | .pop _ => [(core.read .rsp, 8)]
  | .leave => [(core.read .rbp, 8)]
  | .bitcount _ sz _ src => rm core next sz.bytes src
  | .movI32 .. | .movabs .. | .lea .. | .aluA .. | .testA8 .. | .cmpA8 .. | .testA .. |
      .bswap .. | .cxd .. | .cxe .. | .jmp .. | .jmp8 .. | .jcc .. | .jcc8 .. |
      .endbr64 | .ud2 | .nop .. => []

def wire (core : State) (decoded : Ext.Wire.Decoded) : List (Word × Nat) :=
  let next := core.rip + BitVec.ofNat 64 decoded.length
  match decoded.instr with
  | .canonical instruction => canonical core decoded.length instruction
  | .callRM src => rm core next 8 src ++ [(core.read .rsp - 8, 8)]
  | .jmpRM src => rm core next 8 src
  | .cmov sz _ _ src | .mul sz src => rm core next sz.bytes src
  | .cmp8 _ src => rm core next 1 src
  | .testI sz dst _ => rm core next sz.bytes dst
  | .xchg .. | .cpuid => []

@[simp] theorem wire_canonical (core : State) (instruction : Ext.Instr) :
    wire core ⟨.canonical instruction, Ext.encode instruction⟩ =
      canonical core instruction.length instruction := rfl

theorem lea_no_data (core : State) (length : Nat) (sz : Sz)
    (dst : Silmaril.X86.Reg) (src : Mem) : canonical core length (.lea sz dst src) = [] := rfl

theorem cmov_reads_even_false (core : State) (length : Nat) (sz : Sz) (condition : Cond)
    (dst : Silmaril.X86.Reg) (src : Mem) :
    canonical core length (.cmov sz condition dst (.mem src)) =
      [(src.addr core (core.rip + BitVec.ofNat 64 length), sz.bytes)] := rfl

theorem pushRM_old_stack (core : State) (length : Nat) :
    canonical core length (.pushRM (.reg .rsp)) = [(core.read .rsp - 8, 8)] := rfl

theorem indirect_call_memory (core : State) (bytes : List Silmaril.X86.Byte) (src : Mem) :
    wire core ⟨.callRM (.mem src), bytes⟩ =
      [(src.addr core (core.rip + BitVec.ofNat 64 bytes.length), 8), (core.read .rsp - 8, 8)] := rfl

end Silmaril.Process.LPS.Machines.X86Accesses
