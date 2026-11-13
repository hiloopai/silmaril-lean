module

public import Silmaril.X86.Ext.Encoding

/-!
# Encoding examples for the extended x86-64 model

Each `encode` example below is checked by `decide` against the bytes emitted
by the LLVM integrated assembler (`clang -c -target x86_64-linux-gnu`, Intel
syntax) for the instruction in the comment, disassembled with `objdump -d`.
The branch examples use the displacement computed by the assembler for a
target `0x20B`, `0x205` and `0x200` bytes past the end of the instruction.

Assembler output is evidence for these particular byte strings; it is not a
proof about other instructions or about processor behavior. Forms for which
the assembler prefers another encoding are avoided here: the accumulator forms
(`05 id` for `add rax, imm32`), the imm8 forms (`83 /digit ib`), the
shift-by-one forms (`D1 /digit`) and `B8+r id` for `mov r32, imm32`. The
decoder rejects those (see the last group of examples).
-/

@[expose] public section

namespace Silmaril.X86.Ext.Examples

open Silmaril.X86 (Reg AluOp Byte)

/-- `[base + disp]`. -/
def at_ (base : Reg) (disp : BitVec 32 := 0) : Mem := Mem.ofReg base none disp

/-- `[base + index * 2^scale + disp]`. -/
def atIdx (base index : Reg) (scale : BitVec 2) (h : index ≠ .rsp) (disp : BitVec 32 := 0) :
    Mem :=
  Mem.ofReg base (some ⟨index, scale, h⟩) disp

/-- `[index * 2^scale + disp32]`: no base register. -/
def atNoBase (index : Reg) (scale : BitVec 2) (h : index ≠ .rsp) (disp : BitVec 32 := 0) : Mem :=
  Mem.ofIndex (some ⟨index, scale, h⟩) disp

/-- `[disp32]`: no base and no index. -/
def atAbs (disp : BitVec 32) : Mem := Mem.ofIndex none disp

/-! ## Register moves and memory operands, including SIB special cases -/

-- mov rax, rdi
example : encode (.mov .q (.reg .rax) .rdi) = [0x48, 0x89, 0xF8] := by decide
-- mov eax, edi (no REX)
example : encode (.mov .d (.reg .rax) .rdi) = [0x89, 0xF8] := by decide
-- mov r8d, r9d
example : encode (.mov .d (.reg .r8) .r9) = [0x45, 0x89, 0xC8] := by decide
-- mov qword ptr [rsp], rax: RSP base needs a SIB byte
example : encode (.mov .q (.mem (at_ .rsp)) .rax) = [0x48, 0x89, 0x04, 0x24] := by decide
-- mov qword ptr [r12+8], rax: R12 base needs a SIB byte
example : encode (.mov .q (.mem (at_ .r12 8)) .rax) = [0x49, 0x89, 0x44, 0x24, 0x08] := by
  decide
-- mov qword ptr [rbp], rax: RBP base with zero displacement uses a zero disp8
example : encode (.mov .q (.mem (at_ .rbp)) .rax) = [0x48, 0x89, 0x45, 0x00] := by decide
-- mov qword ptr [r13], rax: likewise R13
example : encode (.mov .q (.mem (at_ .r13)) .rax) = [0x49, 0x89, 0x45, 0x00] := by decide
-- mov rax, qword ptr [rbx+rcx*8+0x12345678]
example : encode (.load .q .rax (atIdx .rbx .rcx 3 (by decide) 0x12345678)) =
    [0x48, 0x8B, 0x84, 0xCB, 0x78, 0x56, 0x34, 0x12] := by decide
-- mov eax, dword ptr [rdi+r12*4-8]: R12 as an index (REX.X)
example : encode (.load .d .rax (atIdx .rdi .r12 2 (by decide) (-8))) =
    [0x42, 0x8B, 0x44, 0xA7, 0xF8] := by decide
-- mov rax, qword ptr [r13+rax*2]: R13 base with SIB and zero disp8
example : encode (.load .q .rax (atIdx .r13 .rax 1 (by decide))) =
    [0x49, 0x8B, 0x44, 0x45, 0x00] := by decide
-- mov qword ptr [rsp+r12+0x200], r15: RSP base, R12 index, disp32
example : encode (.mov .q (.mem (atIdx .rsp .r12 0 (by decide) 0x200)) .r15) =
    [0x4E, 0x89, 0xBC, 0x24, 0x00, 0x02, 0x00, 0x00] := by decide
-- mov eax, dword ptr [rbp-0x80]
example : encode (.load .d .rax (at_ .rbp (-0x80))) = [0x8B, 0x45, 0x80] := by decide

/-! ## Narrow stores, extensions, immediates and LEA -/

-- mov byte ptr [rdi], sil: SIL needs a REX prefix
example : encode (.store .b (.mem (at_ .rdi)) .rsi) = [0x40, 0x88, 0x37] := by decide
-- mov word ptr [rdi+2], ax
example : encode (.store .w (.mem (at_ .rdi 2)) .rax) = [0x66, 0x89, 0x47, 0x02] := by decide
-- mov dword ptr [rax], 0x12345678
example : encode (.movI .d (.mem (at_ .rax)) 0x12345678) = [0xC7, 0x00, 0x78, 0x56, 0x34, 0x12] := by
  decide
-- mov rcx, -1
example : encode (.movI .q (.reg .rcx) 0xFFFFFFFF) = [0x48, 0xC7, 0xC1, 0xFF, 0xFF, 0xFF, 0xFF] := by
  decide
-- movabs rax, 0x123456789abcdef0
example : encode (.movabs .rax 0x123456789abcdef0) =
    [0x48, 0xB8, 0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12] := by decide
-- movzx eax, byte ptr [rsi]
example : encode (.movx false .d .b .rax (.mem (at_ .rsi))) = [0x0F, 0xB6, 0x06] := by decide
-- movzx eax, sil
example : encode (.movx false .d .b .rax (.reg .rsi)) = [0x40, 0x0F, 0xB6, 0xC6] := by decide
-- movsx rax, word ptr [rsi+4]
example : encode (.movx true .q .w .rax (.mem (at_ .rsi 4))) = [0x48, 0x0F, 0xBF, 0x46, 0x04] := by
  decide
-- movzx ecx, word ptr [rdx]
example : encode (.movx false .d .w .rcx (.mem (at_ .rdx))) = [0x0F, 0xB7, 0x0A] := by decide
-- movsx eax, byte ptr [rdx]
example : encode (.movx true .d .b .rax (.mem (at_ .rdx))) = [0x0F, 0xBE, 0x02] := by decide
-- movsxd rax, dword ptr [rdi]
example : encode (.movsxd .rax (.mem (at_ .rdi))) = [0x48, 0x63, 0x07] := by decide
-- movsxd rax, ecx
example : encode (.movsxd .rax (.reg .rcx)) = [0x48, 0x63, 0xC1] := by decide
-- lea rax, [rdi+rsi*4+16]
example : encode (.lea .q .rax (atIdx .rdi .rsi 2 (by decide) 16)) = [0x48, 0x8D, 0x44, 0xB7, 0x10] := by
  decide

/-! ## Arithmetic -/

-- add ecx, edx
example : encode (.alu .d .add (.reg .rcx) .rdx) = [0x01, 0xD1] := by decide
-- add rcx, 0x12345678
example : encode (.aluI .q .add (.reg .rcx) 0x12345678) =
    [0x48, 0x81, 0xC1, 0x78, 0x56, 0x34, 0x12] := by decide
-- sub dword ptr [rbx], 0x10000
example : encode (.aluI .d .sub (.mem (at_ .rbx)) 0x10000) = [0x81, 0x2B, 0x00, 0x00, 0x01, 0x00] := by
  decide
-- xor r10d, r10d
example : encode (.alu .d .xor (.reg .r10) .r10) = [0x45, 0x31, 0xD2] := by decide
-- cmp qword ptr [rsp+8], rax
example : encode (.alu .q .cmp (.mem (at_ .rsp 8)) .rax) = [0x48, 0x39, 0x44, 0x24, 0x08] := by
  decide
-- test rax, rbx
example : encode (.test .q (.reg .rax) .rbx) = [0x48, 0x85, 0xD8] := by decide
-- test ecx, ecx
example : encode (.test .d (.reg .rcx) .rcx) = [0x85, 0xC9] := by decide
-- neg rax
example : encode (.unary .q .neg (.reg .rax)) = [0x48, 0xF7, 0xD8] := by decide
-- not dword ptr [rdi]
example : encode (.unary .d .not (.mem (at_ .rdi))) = [0xF7, 0x17] := by decide
-- imul rax, rbx
example : encode (.imul .q .rax (.reg .rbx)) = [0x48, 0x0F, 0xAF, 0xC3] := by decide
-- imul ecx, dword ptr [rsp+4]
example : encode (.imul .d .rcx (.mem (at_ .rsp 4))) = [0x0F, 0xAF, 0x4C, 0x24, 0x04] := by decide
-- shl rax, cl
example : encode (.shift .q .shl (.reg .rax) .cl) = [0x48, 0xD3, 0xE0] := by decide
-- sar edx, cl
example : encode (.shift .d .sar (.reg .rdx) .cl) = [0xD3, 0xFA] := by decide
-- shr r11, 5
example : encode (.shift .q .shr (.reg .r11) (.imm 5)) = [0x49, 0xC1, 0xEB, 0x05] := by decide
-- rol rax, cl
example : encode (.shift .q .rol (.reg .rax) .cl) = [0x48, 0xD3, 0xC0] := by decide
-- ror ecx, cl
example : encode (.shift .d .ror (.reg .rcx) .cl) = [0xD3, 0xC9] := by decide
-- cqo / cdq
example : encode (.cxd .q) = [0x48, 0x99] := by decide
example : encode (.cxd .d) = [0x99] := by decide
-- idiv rcx
example : encode (.div .q true (.reg .rcx)) = [0x48, 0xF7, 0xF9] := by decide
-- div dword ptr [rbx]
example : encode (.div .d false (.mem (at_ .rbx))) = [0xF7, 0x33] := by decide

/-! ## Conditions and control flow -/

-- sete al
example : encode (.setcc .e (.reg .rax)) = [0x0F, 0x94, 0xC0] := by decide
-- setl sil: SIL needs a REX prefix
example : encode (.setcc .l (.reg .rsi)) = [0x40, 0x0F, 0x9C, 0xC6] := by decide
-- setg r9b
example : encode (.setcc .g (.reg .r9)) = [0x41, 0x0F, 0x9F, 0xC1] := by decide
-- setne byte ptr [rax]
example : encode (.setcc .ne (.mem (at_ .rax))) = [0x0F, 0x95, 0x00] := by decide
-- push r12 / pop rbx / ud2 / ret
example : encode (.push .r12) = [0x41, 0x54] := by decide
example : encode (.pop .rbx) = [0x5B] := by decide
example : encode .ud2 = [0x0F, 0x0B] := by decide
example : encode .ret = [0xC3] := by decide
-- jmp, je and call with the assembler's rel32
example : encode (.jmp 0x20B) = [0xE9, 0x0B, 0x02, 0x00, 0x00] := by decide
example : encode (.jcc .e 0x205) = [0x0F, 0x84, 0x05, 0x02, 0x00, 0x00] := by decide
example : encode (.call 0x200) = [0xE8, 0x00, 0x02, 0x00, 0x00] := by decide

/-! ## RIP-relative and base-less addressing

`mod = 00, r/m = 101` without a SIB byte is `[rip + disp32]`, and a SIB `base`
field of `101` with `mod = 00` is `[index * 2^scale + disp32]` (or `[disp32]`
when the index field is `100`). Both always carry a disp32. -/

-- lea rax, [rip+0x100]: the form that materialises a `.rodata` address.
example : encode (.lea .q .rax (Mem.ofRip 0x100)) =
    [0x48, 0x8D, 0x05, 0x00, 0x01, 0x00, 0x00] := by decide
-- mov eax, dword ptr [rip-4]
example : encode (.load .d .rax (Mem.ofRip (-4))) =
    [0x8B, 0x05, 0xFC, 0xFF, 0xFF, 0xFF] := by decide
-- mov dword ptr [rip+0], ecx
example : encode (.mov .d (.mem (Mem.ofRip 0)) .rcx) =
    [0x89, 0x0D, 0x00, 0x00, 0x00, 0x00] := by decide
-- mov eax, dword ptr [rax*4+0x200]: no base register
example : encode (.load .d .rax (atNoBase .rax 2 (by decide) 0x200)) =
    [0x8B, 0x04, 0x85, 0x00, 0x02, 0x00, 0x00] := by decide
-- mov rax, qword ptr [r9*8+0x40]: no base, REX.X for R9
example : encode (.load .q .rax (atNoBase .r9 3 (by decide) 0x40)) =
    [0x4A, 0x8B, 0x04, 0xCD, 0x40, 0x00, 0x00, 0x00] := by decide
-- mov eax, dword ptr [0x200]: no base and no index
example : encode (.load .d .rax (atAbs 0x200)) =
    [0x8B, 0x04, 0x25, 0x00, 0x02, 0x00, 0x00] := by decide
-- The three base-free bytes decode back.
example : decode [0x48, 0x8B, 0x05, 0x00, 0x00, 0x00, 0x00] =
    some (.load .q .rax (Mem.ofRip 0), 7) := by decide
example : decode [0x8B, 0x04, 0x25, 0x00, 0x02, 0x00, 0x00] =
    some (.load .d .rax (atAbs 0x200), 7) := by decide
-- A set REX.B is not canonical for either base-free form: those bits are
-- ignored by the hardware, so the encoder clears them.
example : decode [0x41, 0x8B, 0x05, 0x00, 0x00, 0x00, 0x00] = none := by decide
example : decode [0x41, 0x8B, 0x04, 0x25, 0x00, 0x02, 0x00, 0x00] = none := by decide

/-! ## RIP-relative encodings with a symbolic displacement

The `lea` that materialises a `.rodata` address carries the function's one
`R_X86_64_PC32` displacement, so its bytes depend on where the sections land
and no closed `decide` reaches them. `encode_lea_rip` splits the encoding at
the displacement, leaving a three-byte head that *is* closed, so the general
statement follows from `rfl` on that head. These are the two instantiations the
pilot images use. -/

example (d : BitVec 32) :
    encode (.lea .q .rcx (Mem.ofRip d)) = [0x48, 0x8D, 0x0D] ++ Silmaril.X86.imm32Bytes d := by
  rw [encode_lea_rip]; rfl

example (d : BitVec 32) :
    encode (.lea .q .rax (Mem.ofRip d)) = [0x48, 0x8D, 0x05] ++ Silmaril.X86.imm32Bytes d := by
  rw [encode_lea_rip]; rfl

-- An extended destination sets REX.R, and the head is still closed.
example (d : BitVec 32) :
    encode (.lea .q .r11 (Mem.ofRip d)) = [0x4C, 0x8D, 0x1D] ++ Silmaril.X86.imm32Bytes d := by
  rw [encode_lea_rip]; rfl

-- The length does not depend on the displacement, so instruction boundaries
-- are the same at every layout.
example (d : BitVec 32) : (encode (.lea .q .rcx (Mem.ofRip d))).length = 7 := by simp

-- Relocation is a local edit: only the four displacement bytes move.
example (d e : BitVec 32) :
    ∃ head tail, encode (.lea .q .rcx (Mem.ofRip d)) = head ++ Silmaril.X86.imm32Bytes d ++ tail ∧
      encode (.lea .q .rcx (Mem.ofRip e)) = head ++ Silmaril.X86.imm32Bytes e ++ tail :=
  rmRaw_bytes_rip_congr _ _ _ _ _ _ _ d e

/-! ## Direction-1 ALU, imm8 ALU and CWDE/CDQE -/

-- add eax, ecx
example : encode (.aluR .d .add .rax (.reg .rcx)) = [0x03, 0xC1] := by decide
-- add rax, qword ptr [rbx]
example : encode (.aluR .q .add .rax (.mem (at_ .rbx))) = [0x48, 0x03, 0x03] := by decide
-- or ecx, dword ptr [rbp-8]
example : encode (.aluR .d .or .rcx (.mem (at_ .rbp (-8)))) = [0x0B, 0x4D, 0xF8] := by decide
-- and eax, dword ptr [rsi]
example : encode (.aluR .d .and .rax (.mem (at_ .rsi))) = [0x23, 0x06] := by decide
-- sub r8, r9
example : encode (.aluR .q .sub .r8 (.reg .r9)) = [0x4D, 0x2B, 0xC1] := by decide
-- xor eax, dword ptr [rdi+4]
example : encode (.aluR .d .xor .rax (.mem (at_ .rdi 4))) = [0x33, 0x47, 0x04] := by decide
-- cmp eax, dword ptr [rbp-4]
example : encode (.aluR .d .cmp .rax (.mem (at_ .rbp (-4)))) = [0x3B, 0x45, 0xFC] := by decide
-- add rax, 1
example : encode (.aluI8 .q .add (.reg .rax) 1) = [0x48, 0x83, 0xC0, 0x01] := by decide
-- cmp dword ptr [rbp-4], 0x40
example : encode (.aluI8 .d .cmp (.mem (at_ .rbp (-4))) 0x40) = [0x83, 0x7D, 0xFC, 0x40] := by
  decide
-- sub rsp, 0x20
example : encode (.aluI8 .q .sub (.reg .rsp) 0x20) = [0x48, 0x83, 0xEC, 0x20] := by decide
-- and eax, -16
example : encode (.aluI8 .d .and (.reg .rax) 0xF0) = [0x83, 0xE0, 0xF0] := by decide
-- cdqe (`cltq`) and cwde (`cwtl`)
example : encode (.cxe .q) = [0x48, 0x98] := by decide
example : encode (.cxe .d) = [0x98] := by decide
-- The imm8 and imm32 ALU forms are different instructions, each canonical.
example : decode [0x48, 0x83, 0xC0, 0x01] = some (.aluI8 .q .add (.reg .rax) 1, 4) := by decide
example : decode [0x48, 0x81, 0xC0, 0x01, 0x00, 0x00, 0x00] =
    some (.aluI .q .add (.reg .rax) 1, 7) := by decide
example : decode [0x48, 0x98] = some (.cxe .q, 2) := by decide

/-! ## BSWAP, rel8 branches, INC/DEC, PUSH r/m, and the accumulator forms

These are the forms `clang -O1` and above emit for `sha256_compress`, plus the
`05 id` accumulator ADD that `clang -O0` emits 64 times for the MD5
T-constants. -/

-- bswap eax / bswap rbx / bswap r12d / bswap r15
example : encode (.bswap .d .rax) = [0x0F, 0xC8] := by decide
example : encode (.bswap .q .rbx) = [0x48, 0x0F, 0xCB] := by decide
example : encode (.bswap .d .r12) = [0x41, 0x0F, 0xCC] := by decide
example : encode (.bswap .q .r15) = [0x49, 0x0F, 0xCF] := by decide
-- jmp rel8 and jcc rel8
example : encode (.jmp8 0x10) = [0xEB, 0x10] := by decide
example : encode (.jcc8 .e 0x0E) = [0x74, 0x0E] := by decide
example : encode (.jcc8 .ne (-0x22)) = [0x75, 0xDE] := by decide
example : encode (.jcc8 .ge 0) = [0x7D, 0x00] := by decide
-- inc dword ptr [rbp-4] / inc rax / dec ecx / dec qword ptr [rbx]
example : encode (.incdec .d false (.mem (at_ .rbp (-4)))) = [0xFF, 0x45, 0xFC] := by decide
example : encode (.incdec .q false (.reg .rax)) = [0x48, 0xFF, 0xC0] := by decide
example : encode (.incdec .d true (.reg .rcx)) = [0xFF, 0xC9] := by decide
example : encode (.incdec .q true (.mem (at_ .rbx))) = [0x48, 0xFF, 0x0B] := by decide
-- push qword ptr [rsp+8]
example : encode (.pushRM (.mem (at_ .rsp 8))) = [0xFF, 0x74, 0x24, 0x08] := by decide
-- mov eax, imm32 and mov r9d, imm32
example : encode (.movI32 .rax 0x12345678) = [0xB8, 0x78, 0x56, 0x34, 0x12] := by decide
example : encode (.movI32 .r9 1) = [0x41, 0xB9, 0x01, 0x00, 0x00, 0x00] := by decide
-- accumulator ALU immediates and TEST
example : encode (.aluA .d .add 0x12345678) = [0x05, 0x78, 0x56, 0x34, 0x12] := by decide
example : encode (.aluA .q .add 0x12345678) = [0x48, 0x05, 0x78, 0x56, 0x34, 0x12] := by decide
example : encode (.aluA .d .cmp 0x12345678) = [0x3D, 0x78, 0x56, 0x34, 0x12] := by decide
example : encode (.testA .d 0x7F) = [0xA9, 0x7F, 0x00, 0x00, 0x00] := by decide
example : encode (.testA .q 1) = [0x48, 0xA9, 0x01, 0x00, 0x00, 0x00] := by decide
-- shift by one (`D1 /digit`), which the assembler prefers to `C1 /digit 01`
example : encode (.shift .q .shl (.reg .rax) .one) = [0x48, 0xD1, 0xE0] := by decide
example : encode (.shift .d .shr (.mem (at_ .rbp (-8))) .one) = [0xD1, 0x6D, 0xF8] := by decide
example : encode (.shift .d .rol (.reg .rcx) .one) = [0xD1, 0xC1] := by decide
-- `C1 /digit 01` is the same count in a different, also canonical, encoding
example : encode (.shift .q .shl (.reg .rax) (.imm 1)) = [0x48, 0xC1, 0xE0, 0x01] := by decide
-- mov word ptr [rdi+2], 0x1234
example : encode (.movI16 (.mem (at_ .rdi 2)) 0x1234) = [0x66, 0xC7, 0x47, 0x02, 0x34, 0x12] := by
  decide
-- The decoder reads them back.
example : decode [0x0F, 0xC8] = some (.bswap .d .rax, 2) := by decide
example : decode [0xFF, 0x74, 0x24, 0x08] = some (.pushRM (.mem (at_ .rsp 8)), 4) := by decide
example : decode [0x66, 0xC7, 0x47, 0x02, 0x34, 0x12] =
    some (.movI16 (.mem (at_ .rdi 2)) 0x1234, 6) := by decide
-- `FF /2` (indirect CALL) and `FF /4` (indirect JMP) are outside the model.
example : decode [0xFF, 0xD0] = none := by decide
example : decode [0xFF, 0xE0] = none := by decide

/-! ## LEAVE, ENDBR64 and the byte moves

`leave` and `endbr64` are what gcc adds (`-O0` frames, and `endbr64` because
gcc defaults to `-fcf-protection=full`); `8A /r` and `C6 /0 ib` are motivated
by `MD5_memcpy`, `SHA1Input`, `SHA1Result` and `SHA1PadMessage` rather than by
the compression functions themselves. -/

example : encode .leave = [0xC9] := by decide
example : encode .endbr64 = [0xF3, 0x0F, 0x1E, 0xFA] := by decide
-- mov al, byte ptr [rdi]
example : encode (.mov8 .rax (.mem (at_ .rdi))) = [0x8A, 0x07] := by decide
-- mov sil, byte ptr [rdi+4]: SIL needs a REX prefix
example : encode (.mov8 .rsi (.mem (at_ .rdi 4))) = [0x40, 0x8A, 0x77, 0x04] := by decide
-- mov r9b, byte ptr [rsp]
example : encode (.mov8 .r9 (.mem (at_ .rsp))) = [0x44, 0x8A, 0x0C, 0x24] := by decide
-- mov byte ptr [rdi], 0x41 and mov byte ptr [rbp-1], 0
example : encode (.movI8 (.mem (at_ .rdi)) 0x41) = [0xC6, 0x07, 0x41] := by decide
example : encode (.movI8 (.mem (at_ .rbp (-1))) 0) = [0xC6, 0x45, 0xFF, 0x00] := by decide
-- The register form `C6 /0 ib`; the assembler prefers `B0+r ib`, which is
-- outside the model.
example : encode (.movI8 (.reg .rdx) 0x7F) = [0xC6, 0xC2, 0x7F] := by decide
example : decode [0xB2, 0x7F] = none := by decide
-- Only `F3 0F 1E FA` is ENDBR64; `F3 0F 1E FB` (ENDBR32) is outside the model.
example : decode [0xF3, 0x0F, 0x1E, 0xFA] = some (.endbr64, 4) := by decide
example : decode [0xF3, 0x0F, 0x1E, 0xFB] = none := by decide
example : decode [0xC9] = some (.leave, 1) := by decide

/-! ## `88 /r` and `66 89 /r` with `mod = 11`

The destination of a narrow move is an `r/m`, so these are register-to-register
moves at 8 and 16 bits. `clang -O0` emits `88 c2` in `MD5_memset`. Note that
the REX prefix is forced by *either* byte-register field: `mov sil, al` needs
one for the destination even though the source is AL. -/

-- mov dl, al
example : encode (.store .b (.reg .rdx) .rax) = [0x88, 0xC2] := by decide
-- mov sil, al: REX forced by the destination
example : encode (.store .b (.reg .rsi) .rax) = [0x40, 0x88, 0xC6] := by decide
-- mov dl, sil: REX forced by the source
example : encode (.store .b (.reg .rdx) .rsi) = [0x40, 0x88, 0xF2] := by decide
-- mov r9b, al
example : encode (.store .b (.reg .r9) .rax) = [0x41, 0x88, 0xC1] := by decide
-- mov cx, ax / mov r10w, ax
example : encode (.store .w (.reg .rcx) .rax) = [0x66, 0x89, 0xC1] := by decide
example : encode (.store .w (.reg .r10) .rax) = [0x66, 0x41, 0x89, 0xC2] := by decide
-- The byte that used to stop the decoder, read back.
example : decode [0x88, 0xC2] = some (.store .b (.reg .rdx) .rax, 2) := by decide
example : decode [0x66, 0x89, 0xC1] = some (.store .w (.reg .rcx) .rax, 3) := by decide
-- `8A /r` is the same 8-bit move written the other way round. Both are
-- canonical for their own constructor, so each byte string has one reading.
example : decode [0x8A, 0xD0] = some (.mov8 .rdx (.reg .rax), 2) := by decide
example : encode (.mov8 .rdx (.reg .rax)) = [0x8A, 0xD0] := by decide
-- Without a REX prefix the field `110` names DH, which is outside the model,
-- so the non-canonical spelling of `mov sil, al` does not decode.
example : decode [0x88, 0xC6] = none := by decide

/-! ## NOP padding

The fifteen canonical paddings, checked against GNU `as` (`.nops N`, binutils
2.42) and `llvm-mc` (LLVM 18.1.3), which disassembles each of these byte
strings as a single instruction. The multi-byte forms use a displacement wider
than the value needs; that is how an assembler reaches a target length, so each
length is its own instruction here rather than a `0F 1F` with an operand. -/

example : encode (.nop 0) = [0x90] := by decide
example : encode (.nop 1) = [0x66, 0x90] := by decide
example : encode (.nop 2) = [0x0F, 0x1F, 0x00] := by decide
example : encode (.nop 3) = [0x0F, 0x1F, 0x40, 0x00] := by decide
example : encode (.nop 4) = [0x0F, 0x1F, 0x44, 0x00, 0x00] := by decide
example : encode (.nop 5) = [0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00] := by decide
example : encode (.nop 6) = [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00] := by decide
example : encode (.nop 7) = [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] := by decide
example : encode (.nop 8) = [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] := by decide
example : encode (.nop 9) =
    [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] := by decide
example : encode (.nop 10) =
    [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] := by decide
example : encode (.nop 11) =
    [0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] := by decide
example : encode (.nop 12) =
    [0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] := by decide
example : encode (.nop 13) =
    [0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00,
      0x00] := by decide
example : encode (.nop 14) =
    [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00,
      0x00] := by decide

-- Every padding has the length its index names, and the longest is the
-- architectural maximum of fifteen bytes.
example : ∀ k : Fin 15, (encode (.nop k)).length = k.val + 1 := by decide

-- The decoder reads each of them back, including the `66`-run forms that
-- `clang -O1`/`-O2` emit.
example : decode [0x0F, 0x1F, 0x44, 0x00, 0x00] = some (.nop 4, 5) := by decide
example : decode [0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] =
    some (.nop 12, 13) := by decide
-- A `66` run that is not followed by `2E` and `0F 1F` is not an instruction.
example : decode [0x66, 0x66, 0x89, 0xC1] = none := by decide
-- A bare `2E` segment override is not accepted: segment prefixes are modelled
-- only as NOP padding.
example : decode [0x2E, 0x8B, 0x00] = none := by decide

/-! ## Bit counts (need the LZCNT, BMI1 and POPCNT features) -/

-- lzcnt rax, rbx
example : encode (.bitcount .lzcnt .q .rax (.reg .rbx)) = [0xF3, 0x48, 0x0F, 0xBD, 0xC3] := by decide
-- popcnt ecx, edx
example : encode (.bitcount .popcnt .d .rcx (.reg .rdx)) = [0xF3, 0x0F, 0xB8, 0xCA] := by decide
-- tzcnt r8, qword ptr [rdi]
example : encode (.bitcount .tzcnt .q .r8 (.mem (at_ .rdi))) = [0xF3, 0x4C, 0x0F, 0xBC, 0x07] := by
  decide
-- lzcnt esi, dword ptr [rsp+4]
example : encode (.bitcount .lzcnt .d .rsi (.mem (at_ .rsp 4))) =
    [0xF3, 0x0F, 0xBD, 0x74, 0x24, 0x04] := by decide
-- `bsr rax, rbx` (no F3) is outside the model.
example : decode [0x48, 0x0F, 0xBD, 0xC3] = none := by decide

/-! ## Decoding -/

-- The decoder recovers instructions and their lengths, ignoring what follows.
example : decode [0x49, 0x89, 0x44, 0x24, 0x08, 0xC3] = some (.mov .q (.mem (at_ .r12 8)) .rax, 5) := by
  decide
example : decode [0x40, 0x0F, 0x9C, 0xC6] = some (.setcc .l (.reg .rsi), 4) := by decide

-- `sete ah` (no REX): AH is outside the model.
example : decode [0x0F, 0x94, 0xC4] = none := by decide
-- `mov rax, rdi` in the `8B` direction: valid, but not canonical here.
example : decode [0x48, 0x8B, 0xC7] = none := by decide
-- `mov rax, [rsp+0]` with a redundant zero disp8: not canonical.
example : decode [0x48, 0x8B, 0x44, 0x24, 0x00] = none := by decide
-- `shl rax, 1` (`D1 /4`), `add rax, imm32` in the accumulator form `05 id`
-- and `mov eax, imm32` (`B8+r id`) are instructions of their own.
example : decode [0x48, 0xD1, 0xE0] = some (.shift .q .shl (.reg .rax) .one, 3) := by decide
example : decode [0x48, 0x05, 0x78, 0x56, 0x34, 0x12] = some (.aluA .q .add 0x12345678, 6) := by
  decide
example : decode [0xB8, 0x78, 0x56, 0x34, 0x12] = some (.movI32 .rax 0x12345678, 5) := by decide
-- `rcl`/`rcr` (`D1 /2`, `D1 /3`) read CF and are outside the model, as they
-- already are in the `C1` and `D3` groups.
example : decode [0x48, 0xD1, 0xD0] = none := by decide
-- `40 89 F8` (`mov eax, edi` with a redundant REX): not canonical.
example : decode [0x40, 0x89, 0xF8] = none := by decide
-- A truncated encoding.
example : decode [0x48, 0x81, 0xC1, 0x78, 0x56] = none := by decide

/-! ## The FS segment override

The two instructions gcc's `-fstack-protector-strong` emits, which are the only
segment-overridden instructions in the pinned x86-64 matrix: the canary load at
function entry and the compare before the epilogue. The `64` prefix precedes
the REX prefix, which is the order `llvm-mc` also emits. -/

-- `mov %fs:0x28,%rax`
example : encode (.load .q .rax (Mem.fsAt 0x28)) =
    [0x64, 0x48, 0x8B, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00] := by decide
example : decode [0x64, 0x48, 0x8B, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00] =
    some (.load .q .rax (Mem.fsAt 0x28), 9) := by decide

-- `sub %fs:0x28,%rax`, the direction-1 ALU form with an `fs:` source.
example : encode (.aluR .q .sub .rax (.mem (Mem.fsAt 0x28))) =
    [0x64, 0x48, 0x2B, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00] := by decide
example : decode [0x64, 0x48, 0x2B, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00] =
    some (.aluR .q .sub .rax (.mem (Mem.fsAt 0x28)), 9) := by decide

-- The override composes with REX.R, with a scaled index, and with the `66` and
-- `F3` legacy prefixes; `llvm-mc` agrees on all of these (see `EncDump.lean`).
example : encode (.load .d .r11 (Mem.fsAt 0x10)) =
    [0x64, 0x44, 0x8B, 0x1C, 0x25, 0x10, 0x00, 0x00, 0x00] := by decide
example : encode (.load .q .rax (Mem.ofFs (some ⟨.rcx, 2, by decide⟩) 0x28)) =
    [0x64, 0x48, 0x8B, 0x04, 0x8D, 0x28, 0x00, 0x00, 0x00] := by decide
example : encode (.store .b (.mem (Mem.fsAt 8)) .rsi) =
    [0x64, 0x40, 0x88, 0x34, 0x25, 0x08, 0x00, 0x00, 0x00] := by decide
example : encode (.store .w (.mem (Mem.fsAt 8)) .rcx) =
    [0x64, 0x66, 0x89, 0x0C, 0x25, 0x08, 0x00, 0x00, 0x00] := by decide
example : encode (.bitcount .lzcnt .d .rax (.mem (Mem.fsAt 8))) =
    [0x64, 0xF3, 0x0F, 0xBD, 0x04, 0x25, 0x08, 0x00, 0x00, 0x00] := by decide

-- GS (`65`) is not modeled, and neither is `fs:` on an operand that has a base
-- register: both are rejected rather than silently misread as something else.
example : decode [0x65, 0x48, 0x8B, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00] = none := by decide
example : decode [0x64, 0x48, 0x8B, 0x40, 0x08] = none := by decide
-- A segment override on an instruction with no memory operand is inert on
-- hardware and is not a distinct instruction here, so it does not decode.
example : decode [0x64, 0xC3] = none := by decide
example : decode [0x64, 0x48, 0x89, 0xC0] = none := by decide

/-! ## 32-bit `lea`

`gcc -O0` computes index arithmetic with `lea r32`, which needs no REX.W. -/

example : encode (.lea .d .rcx (Mem.ofReg .rdx (some ⟨.rax, 0, by decide⟩) 0)) =
    [0x8D, 0x0C, 0x02] := by decide
example : decode [0x8D, 0x0C, 0x02] =
    some (.lea .d .rcx (Mem.ofReg .rdx (some ⟨.rax, 0, by decide⟩) 0), 3) := by decide

end Silmaril.X86.Ext.Examples
