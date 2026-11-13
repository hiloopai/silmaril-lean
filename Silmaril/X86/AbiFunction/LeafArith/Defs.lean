module

public import Silmaril.X86.AbiFunction.Defs
public import Silmaril.X86.Ladder.LeafArith.Defs
/-!
# Rung 01 (`leaf-arith`) functions as `AbiFunction`s

The functions of `examples/elf-ladder/01-leaf-arith/arith.c`, compiled by GCC 13.3.0 at `-O2`
with the ladder flags (`examples/elf-ladder/common/flags.sh`). `gccS` is the `gcc -S` output
for the five functions of the transcribed region (the text a compiler explorer shows before
it filters directives); `-O3` gives the same text for this file.

* `satAdd`: `u32 sat_add_u32(u32 a, u32 b)` as a System V `AbiFunction`, its body written out
  as a term (`Thms.lean` checks by `#guard` that `ofGccS` reads exactly this body from `gccS`).
* `placement`: its place in the pinned executable, offset `0x90` of the transcribed `.text`
  region (`Ladder.LeafArith.code` at `Ladder.LeafArith.base = 0x401370`), i.e. the symbol's
  address `0x401400`.
* `assemblesToPinned name`: the function `name`, parsed from `gccS` and assembled at its
  symbol address, is the region's bytes there (the assembler checks in `Thms.lean`).
-/

@[expose] public section

namespace Silmaril.X86.AbiFunction.LeafArith

open Silmaril.X86.AbiFunction

/-- The C source. -/
def cSource : String :=
  "u32 sat_add_u32(u32 a, u32 b) {\n  u32 s = a + b;\n  return s < a ? 0xffffffffu : s;\n}\n"

/-- The compiler and flags (`examples/elf-ladder/common/flags.sh`). -/
def gccFlags : List String :=
  ["gcc-13.3.0", "-O2", "-std=gnu11", "-ffreestanding", "-fno-builtin", "-fno-stack-protector",
   "-fcf-protection=none", "-mgeneral-regs-only", "-fno-pic", "-fno-pie",
   "-fno-asynchronous-unwind-tables", "-fno-unwind-tables", "-fno-jump-tables",
   "-fno-tree-vectorize", "-fno-tree-slp-vectorize", "-fno-bit-tests", "-fno-if-conversion",
   "-fno-if-conversion2", "-fno-tree-loop-distribute-patterns", "-ffunction-sections",
   "-fdata-sections", "-fno-ident"]

/-- `gcc -S` output (verbatim, tabs included) for the five functions of `arith.c` in the
transcribed region, in address order: `gcd_u32`, `clamp_i32`, `isqrt_u32`, `sat_add_u32`,
`bswap32_manual`. (`popcount32` and `ilog2_u32` use `imul r, r/m, imm32` and `bsr`, outside
`X86.Ext`.) -/
def gccS : String :=
  "\t.section\t.text.gcd_u32,\"ax\",@progbits\n\
  \t.p2align 4\n\
  \t.globl\tgcd_u32\n\
  \t.type\tgcd_u32, @function\n\
  gcd_u32:\n\
  \tmovl\t%edi, %eax\n\
  \tmovl\t%esi, %edx\n\
  \ttestl\t%esi, %esi\n\
  \tje\t.L6\n\
  \t.p2align 4,,10\n\
  \t.p2align 3\n\
  .L5:\n\
  \tmovl\t%edx, %ecx\n\
  \txorl\t%edx, %edx\n\
  \tdivl\t%ecx\n\
  \tmovl\t%ecx, %eax\n\
  \ttestl\t%edx, %edx\n\
  \tjne\t.L5\n\
  \tmovl\t%ecx, %eax\n\
  \tret\n\
  \t.p2align 4,,10\n\
  \t.p2align 3\n\
  .L6:\n\
  \tmovl\t%edi, %ecx\n\
  \tmovl\t%ecx, %eax\n\
  \tret\n\
  \t.size\tgcd_u32, .-gcd_u32\n\
  \t.section\t.text.clamp_i32,\"ax\",@progbits\n\
  \t.p2align 4\n\
  \t.globl\tclamp_i32\n\
  \t.type\tclamp_i32, @function\n\
  clamp_i32:\n\
  \tcmpl\t%esi, %edi\n\
  \tjl\t.L10\n\
  \tcmpl\t%edx, %edi\n\
  \tmovl\t%edx, %eax\n\
  \tcmovle\t%edi, %eax\n\
  \tret\n\
  \t.p2align 4,,10\n\
  \t.p2align 3\n\
  .L10:\n\
  \tmovl\t%esi, %eax\n\
  \tret\n\
  \t.size\tclamp_i32, .-clamp_i32\n\
  \t.section\t.text.isqrt_u32,\"ax\",@progbits\n\
  \t.p2align 4\n\
  \t.globl\tisqrt_u32\n\
  \t.type\tisqrt_u32, @function\n\
  isqrt_u32:\n\
  \tmovl\t$1073741824, %eax\n\
  \tcmpl\t$1073741823, %edi\n\
  \tja\t.L12\n\
  \t.p2align 4,,10\n\
  \t.p2align 3\n\
  .L13:\n\
  \tshrl\t$2, %eax\n\
  \tcmpl\t%eax, %edi\n\
  \tjb\t.L13\n\
  \ttestl\t%eax, %eax\n\
  \tje\t.L21\n\
  .L12:\n\
  \txorl\t%edx, %edx\n\
  \t.p2align 4,,10\n\
  \t.p2align 3\n\
  .L16:\n\
  \tleal\t(%rdx,%rax), %ecx\n\
  \tshrl\t%edx\n\
  \tcmpl\t%ecx, %edi\n\
  \tjb\t.L15\n\
  \tsubl\t%ecx, %edi\n\
  \taddl\t%eax, %edx\n\
  .L15:\n\
  \tshrl\t$2, %eax\n\
  \tjne\t.L16\n\
  \tmovl\t%edx, %eax\n\
  \tret\n\
  \t.p2align 4,,10\n\
  \t.p2align 3\n\
  .L21:\n\
  \txorl\t%edx, %edx\n\
  \tmovl\t%edx, %eax\n\
  \tret\n\
  \t.size\tisqrt_u32, .-isqrt_u32\n\
  \t.section\t.text.sat_add_u32,\"ax\",@progbits\n\
  \t.p2align 4\n\
  \t.globl\tsat_add_u32\n\
  \t.type\tsat_add_u32, @function\n\
  sat_add_u32:\n\
  \txorl\t%edx, %edx\n\
  \taddl\t%esi, %edi\n\
  \tjc\t.L27\n\
  .L23:\n\
  \tmovl\t%edi, %eax\n\
  \ttestl\t%edx, %edx\n\
  \tjne\t.L28\n\
  \tret\n\
  \t.p2align 4,,10\n\
  \t.p2align 3\n\
  .L28:\n\
  \tmovl\t$-1, %eax\n\
  \tret\n\
  .L27:\n\
  \tmovl\t$1, %edx\n\
  \tjmp\t.L23\n\
  \t.size\tsat_add_u32, .-sat_add_u32\n\
  \t.section\t.text.bswap32_manual,\"ax\",@progbits\n\
  \t.p2align 4\n\
  \t.globl\tbswap32_manual\n\
  \t.type\tbswap32_manual, @function\n\
  bswap32_manual:\n\
  \tmovl\t%edi, %eax\n\
  \tbswap\t%eax\n\
  \tret\n\
  \t.size\tbswap32_manual, .-bswap32_manual\n"

/-- The body. -/
def body : List Line :=
  [.instr (.alu .d .xor (.reg .rdx) .rdx),
   .instr (.alu .d .add (.reg .rdi) .rsi),
   .jcc .b ".L27",
   .label ".L23",
   .instr (.mov .d (.reg .rax) .rdi),
   .instr (.test .d (.reg .rdx) .rdx),
   .jcc .ne ".L28",
   .instr .ret,
   .align 4 10,
   .align 3 7,
   .label ".L28",
   .instr (.movI32 .rax 0xffffffff),
   .instr .ret,
   .label ".L27",
   .instr (.movI32 .rdx 1),
   .jmp ".L23"]

/-- `sat_add_u32` as a System V `AbiFunction`. -/
def satAdd : AbiFunction Link.Abi.Conv where
  abi := .sysv64
  name := "sat_add_u32"
  sig := Ladder.LeafArith.sigU2
  body := body
  align := 4
  source := some cSource
  flags := gccFlags

/-- Its place in the pinned executable: offset `0x90` of the transcribed region at
`0x401370`, i.e. the symbol's address `0x401400`. -/
def placement : Placement where
  base := Ladder.LeafArith.base
  code := Ladder.LeafArith.code
  off := 0x90

/-- The symbol addresses of the five functions (`Transcript.image`). -/
def symbols : List (String × Nat) :=
  [("gcd_u32", 0x401370), ("clamp_i32", 0x4013a0), ("isqrt_u32", 0x4013c0),
   ("sat_add_u32", 0x401400), ("bswap32_manual", 0x401420)]

/-- Does the function `name`, parsed from `gccS` and assembled at its symbol address, give
the bytes of the transcribed region there? (Signatures are irrelevant to the bytes; `sigU2`
stands in.) -/
def assemblesToPinned (name : String) : Bool :=
  match (symbols.lookup name, ofGccS Link.Abi.Conv.sysv64 Ladder.LeafArith.sigU2 name gccS) with
  | (some a, .ok f) =>
    match f.bytesAt a noSymbols with
    | some bs => (Ladder.LeafArith.code.drop (a - 0x401370)).take bs.length == bs
    | none => false
  | _ => false

end Silmaril.X86.AbiFunction.LeafArith
