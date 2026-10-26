module

public import Silmaril.X86.Lift.Transcript
public import Silmaril.X86.SegVC
public import Silmaril.Apps.Sha256sum.Binary.Load

/-! # The update region of `digest_file` in `sha256sum-min`

`digest_file` (0x402de0) inlines `digest_fd`, `sha_update` and `sha_final`. The bytes here are
its read loop and `sha_update`: `[0x402ef0, 0x402fe8)`, 248 bytes, 61 instructions, every one
inside `X86.Ext` (no 8-bit ALU form). The listing was produced by `tools/x86-lift --raw` and is
re-checked by `SegVC.Listing.valid` (`listing_valid`, by `decide`) against Silmaril's decoder;
`code_eq` ties the bytes to the loaded image (`Binary.Image`).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest

open Silmaril.X86 (Byte)
open Silmaril.X86.Ext (Mem)
open Silmaril.X86.Lift (ix)
open Silmaril.X86

/-- The region's load address. -/
def base : Word := 0x402ef0#64

def code : List Byte := [
  0x48, 0x8b, 0x74, 0x24, 0x08, 0x31, 0xff, 0xb9, 0x00, 0x80, 0x00, 0x00, 0xba, 0xc0, 0xa0, 0x40,
  0x00, 0xe8, 0x0a, 0xe1, 0xff, 0xff, 0x48, 0x85, 0xc0, 0x0f, 0x88, 0xd9, 0x00, 0x00, 0x00, 0x48,
  0x8b, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0f, 0x84, 0x17, 0x01, 0x00, 0x00, 0x48, 0x01, 0xc2,
  0x49, 0x89, 0xc7, 0x41, 0xbc, 0xc0, 0xa0, 0x40, 0x00, 0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00,
  0x00, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00,
  0x49, 0x83, 0xff, 0x3f, 0x76, 0x05, 0x48, 0x85, 0xd2, 0x74, 0x65, 0x49, 0x89, 0xd8, 0x48, 0x8d,
  0x74, 0x24, 0x40, 0x49, 0x29, 0xd0, 0x48, 0x8d, 0x3c, 0x16, 0x4d, 0x39, 0xf8, 0x4d, 0x0f, 0x47,
  0xc7, 0x4d, 0x89, 0xc6, 0x4d, 0x85, 0xc0, 0x74, 0x20, 0x31, 0xd2, 0x0f, 0x1f, 0x44, 0x00, 0x00,
  0x41, 0x0f, 0xb6, 0x0c, 0x14, 0x88, 0x0c, 0x17, 0x48, 0x83, 0xc2, 0x01, 0x49, 0x39, 0xd6, 0x75,
  0xef, 0x48, 0x8b, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4c, 0x01, 0xf2, 0x48, 0x89, 0x94, 0x24,
  0x80, 0x00, 0x00, 0x00, 0x48, 0x83, 0xfa, 0x40, 0x74, 0x36, 0x4d, 0x01, 0xf4, 0x4d, 0x29, 0xf7,
  0x4d, 0x85, 0xff, 0x75, 0x93, 0xe9, 0x46, 0xff, 0xff, 0xff, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00,
  0x4c, 0x89, 0xe6, 0x48, 0x8d, 0x7c, 0x24, 0x20, 0x49, 0x83, 0xc4, 0x40, 0x49, 0x83, 0xef, 0x40,
  0xe8, 0x3b, 0x22, 0x00, 0x00, 0xeb, 0xd9, 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x48, 0x8d, 0x7c, 0x24, 0x20, 0xe8, 0x26, 0x22, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0x80, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xeb, 0xb2
  ]

set_option maxRecDepth 100000 in
def listing : List (Nat × Ext.Instr × Nat) := [
  (0, .load .q .rsi (Mem.ofReg .rsp none 0x8), 5), -- 0x402ef0: 488b742408  mov 8(%rsp),%rsi
  (5, .alu .d .xor (.reg .rdi) .rdi, 2), -- 0x402ef5: 31ff  xor %edi,%edi
  (7, .movI32 .rcx 0x8000, 5), -- 0x402ef7: b900800000  mov $0x8000,%ecx
  (12, .movI32 .rdx 0x40a0c0, 5), -- 0x402efc: bac0a04000  mov $0x40A0C0,%edx
  (17, .call 0xffffe10a, 5), -- 0x402f01: e80ae1ffff  call 0x0000000000401010
  (22, .test .q (.reg .rax) .rax, 3), -- 0x402f06: 4885c0  test %rax,%rax
  (25, .jcc .s 0xd9, 6), -- 0x402f09: 0f88d9000000  js 0x0000000000402FE8
  (31, .load .q .rdx (Mem.ofReg .rsp none 0x88), 8), -- 0x402f0f: 488b942488000000  mov 0x88(%rsp),%rdx
  (39, .jcc .e 0x117, 6), -- 0x402f17: 0f8417010000  je 0x0000000000403034
  (45, .alu .q .add (.reg .rdx) .rax, 3), -- 0x402f1d: 4801c2  add %rax,%rdx
  (48, .mov .q (.reg .r15) .rax, 3), -- 0x402f20: 4989c7  mov %rax,%r15
  (51, .movI32 .r12 0x40a0c0, 6), -- 0x402f23: 41bcc0a04000  mov $0x40A0C0,%r12d
  (57, .mov .q (.mem (Mem.ofReg .rsp none 0x88)) .rdx, 8), -- 0x402f29: 4889942488000000  mov %rdx,0x88(%rsp)
  (65, .nop 6, 7), -- 0x402f31: 0f1f8000000000  nopl (%rax)
  (72, .load .q .rdx (Mem.ofReg .rsp none 0x80), 8), -- 0x402f38: 488b942480000000  mov 0x80(%rsp),%rdx
  (80, .aluI8 .q .cmp (.reg .r15) 0x3f, 4), -- 0x402f40: 4983ff3f  cmp $0x3F,%r15
  (84, .jcc8 .be 0x5, 2), -- 0x402f44: 7605  jbe 0x0000000000402F4B
  (86, .test .q (.reg .rdx) .rdx, 3), -- 0x402f46: 4885d2  test %rdx,%rdx
  (89, .jcc8 .e 0x65, 2), -- 0x402f49: 7465  je 0x0000000000402FB0
  (91, .mov .q (.reg .r8) .rbx, 3), -- 0x402f4b: 4989d8  mov %rbx,%r8
  (94, .lea .q .rsi (Mem.ofReg .rsp none 0x40), 5), -- 0x402f4e: 488d742440  lea 0x40(%rsp),%rsi
  (99, .alu .q .sub (.reg .r8) .rdx, 3), -- 0x402f53: 4929d0  sub %rdx,%r8
  (102, .lea .q .rdi (Mem.ofReg .rsi (some (ix .rdx 0)) 0x0), 4), -- 0x402f56: 488d3c16  lea (%rsi,%rdx),%rdi
  (106, .alu .q .cmp (.reg .r8) .r15, 3), -- 0x402f5a: 4d39f8  cmp %r15,%r8
  (109, .cmov .q .a .r8 (.reg .r15), 4), -- 0x402f5d: 4d0f47c7  cmova %r15,%r8
  (113, .mov .q (.reg .r14) .r8, 3), -- 0x402f61: 4d89c6  mov %r8,%r14
  (116, .test .q (.reg .r8) .r8, 3), -- 0x402f64: 4d85c0  test %r8,%r8
  (119, .jcc8 .e 0x20, 2), -- 0x402f67: 7420  je 0x0000000000402F89
  (121, .alu .d .xor (.reg .rdx) .rdx, 2), -- 0x402f69: 31d2  xor %edx,%edx
  (123, .nop 4, 5), -- 0x402f6b: 0f1f440000  nopl (%rax,%rax)
  (128, .movx false .d .b .rcx (.mem (Mem.ofReg .r12 (some (ix .rdx 0)) 0x0)), 5), -- 0x402f70: 410fb60c14  movzbl (%r12,%rdx),%ecx
  (133, .store .b (.mem (Mem.ofReg .rdi (some (ix .rdx 0)) 0x0)) .rcx, 3), -- 0x402f75: 880c17  mov %cl,(%rdi,%rdx)
  (136, .aluI8 .q .add (.reg .rdx) 0x1, 4), -- 0x402f78: 4883c201  add $1,%rdx
  (140, .alu .q .cmp (.reg .r14) .rdx, 3), -- 0x402f7c: 4939d6  cmp %rdx,%r14
  (143, .jcc8 .ne 0xef, 2), -- 0x402f7f: 75ef  jne 0x0000000000402F70
  (145, .load .q .rdx (Mem.ofReg .rsp none 0x80), 8), -- 0x402f81: 488b942480000000  mov 0x80(%rsp),%rdx
  (153, .alu .q .add (.reg .rdx) .r14, 3), -- 0x402f89: 4c01f2  add %r14,%rdx
  (156, .mov .q (.mem (Mem.ofReg .rsp none 0x80)) .rdx, 8), -- 0x402f8c: 4889942480000000  mov %rdx,0x80(%rsp)
  (164, .aluI8 .q .cmp (.reg .rdx) 0x40, 4), -- 0x402f94: 4883fa40  cmp $0x40,%rdx
  (168, .jcc8 .e 0x36, 2), -- 0x402f98: 7436  je 0x0000000000402FD0
  (170, .alu .q .add (.reg .r12) .r14, 3), -- 0x402f9a: 4d01f4  add %r14,%r12
  (173, .alu .q .sub (.reg .r15) .r14, 3), -- 0x402f9d: 4d29f7  sub %r14,%r15
  (176, .test .q (.reg .r15) .r15, 3), -- 0x402fa0: 4d85ff  test %r15,%r15
  (179, .jcc8 .ne 0x93, 2), -- 0x402fa3: 7593  jne 0x0000000000402F38
  (181, .jmp 0xffffff46, 5), -- 0x402fa5: e946ffffff  jmp 0x0000000000402EF0
  (186, .nop 5, 6), -- 0x402faa: 660f1f440000  nopw (%rax,%rax)
  (192, .mov .q (.reg .rsi) .r12, 3), -- 0x402fb0: 4c89e6  mov %r12,%rsi
  (195, .lea .q .rdi (Mem.ofReg .rsp none 0x20), 5), -- 0x402fb3: 488d7c2420  lea 0x20(%rsp),%rdi
  (200, .aluI8 .q .add (.reg .r12) 0x40, 4), -- 0x402fb8: 4983c440  add $0x40,%r12
  (204, .aluI8 .q .sub (.reg .r15) 0x40, 4), -- 0x402fbc: 4983ef40  sub $0x40,%r15
  (208, .call 0x223b, 5), -- 0x402fc0: e83b220000  call 0x0000000000405200
  (213, .jmp8 0xd9, 2), -- 0x402fc5: ebd9  jmp 0x0000000000402FA0
  (215, .nop 8, 9), -- 0x402fc7: 660f1f840000000000  nopw (%rax,%rax)
  (224, .lea .q .rdi (Mem.ofReg .rsp none 0x20), 5), -- 0x402fd0: 488d7c2420  lea 0x20(%rsp),%rdi
  (229, .call 0x2226, 5), -- 0x402fd5: e826220000  call 0x0000000000405200
  (234, .movI .q (.mem (Mem.ofReg .rsp none 0x80)) 0x0, 12), -- 0x402fda: 48c784248000000000000000  movq $0,0x80(%rsp)
  (246, .jmp8 0xb2, 2)  -- 0x402fe6: ebb2  jmp 0x0000000000402F9A
  ]

set_option maxRecDepth 100000 in
/-- **The lift**: every listed instruction is what Silmaril's decoder reads at its offset. -/
theorem listing_valid : SegVC.Listing.valid (SegVC.Isa.ext 0) code listing = true := by decide

/-- The executable segment holds these bytes at `0x402ef0`. -/
theorem seg1_code : (Image.seg1.contents.drop (0x402ef0 - 0x401000)).take 248 = code := by
  decide +kernel

/-- **Loading puts the region at `base`.** -/
theorem loaded {memory : Silmaril.Process.Memory} (h : Image.image.Mapped memory) :
    Ext.Loaded memory base code := by
  have := readWith_segment h seg1_mem Image.image_wf (acc := .execute) (by decide)
    (0x402ef0 - 0x401000) 248 (by decide) (by decide)
  rw [seg1_code] at this
  exact this

end Silmaril.Apps.Sha256sum.Binary.Digest
