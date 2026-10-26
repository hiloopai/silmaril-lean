module

public import Silmaril.X86.Lift.Transcript
public import Silmaril.Apps.Sha256sum.X86Sys.SegVC8
public import Silmaril.Apps.Sha256sum.Binary.Load

/-! # The prologue of `digest_file` in `sha256sum-min`

`digest_file` (0x402de0) up to its read loop's head (0x402ef0): the six pushes and the frame,
the comparison of the operand with `"-"` (for `"-"`: `have_read_stdin = 1`, the descriptor slot
`8(%rsp) = 0`), the `openat` path for other operands, and the inlined `sha_init` (`h` = the
SHA-256 initial value as four quadwords, `blen = total = 0`). The region is
`[0x402de0, 0x402ef0)`, 272 bytes. The listing is the driver listing's (`Lift.Gen.listing`,
produced by Silmaril's own `Ext8` decoder) at these addresses, re-checked against the `Ext8`
instance's decoder (`listing_valid`, by `decide`); `seg1_code` ties the bytes to the image.
`cmp %r13b,%bpl` (0x402e39) is an `Ext8` new form.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest.Prologue

open Silmaril.X86 (Byte)
open Silmaril.X86.Ext (Mem)
open Silmaril.X86.Lift (ix)
open Silmaril.X86
open Silmaril.Apps.Sha256sum.X86Sys (Isa.sys8)

/-- The region's load address. -/
def base : Word := 0x402de0#64

def code : List Byte := [
  0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x89, 0xd3, 0x48, 0x81, 0xec,
  0x98, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0x2f, 0x48, 0x89, 0x3c, 0x24, 0x48, 0x89, 0x74, 0x24, 0x10,
  0x40, 0x84, 0xed, 0x0f, 0x84, 0x45, 0x04, 0x00, 0x00, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x41, 0xbd,
  0x2d, 0x00, 0x00, 0x00, 0xeb, 0x23, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x48, 0x8b, 0x34, 0x24, 0x0f, 0xb6, 0x2c, 0x06, 0x48, 0x83, 0xc0, 0x01, 0x44, 0x0f, 0xb6, 0xa8,
  0x51, 0x60, 0x40, 0x00, 0x40, 0x84, 0xed, 0x74, 0x37, 0x44, 0x38, 0xed, 0x74, 0xe2, 0xc7, 0x03,
  0x00, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x14, 0x24, 0x31, 0xc9, 0xbf, 0x01, 0x01, 0x00, 0x00, 0x48,
  0xc7, 0xc6, 0x9c, 0xff, 0xff, 0xff, 0xe8, 0xb5, 0xe1, 0xff, 0xff, 0x49, 0x89, 0xc7, 0x48, 0x85,
  0xc0, 0x0f, 0x88, 0xaa, 0x02, 0x00, 0x00, 0x48, 0x98, 0x48, 0x89, 0x44, 0x24, 0x08, 0xeb, 0x1e,
  0xc7, 0x03, 0x00, 0x00, 0x00, 0x00, 0x45, 0x84, 0xed, 0x75, 0xc9, 0xc7, 0x05, 0x1b, 0x72, 0x00,
  0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xb8,
  0x67, 0xe6, 0x09, 0x6a, 0x85, 0xae, 0x67, 0xbb, 0xbb, 0x40, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84,
  0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0xb8,
  0x72, 0xf3, 0x6e, 0x3c, 0x3a, 0xf5, 0x4f, 0xa5, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0xb8, 0x7f,
  0x52, 0x0e, 0x51, 0x8c, 0x68, 0x05, 0x9b, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0xb8, 0xab, 0xd9,
  0x83, 0x1f, 0x19, 0xcd, 0xe0, 0x5b, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0xc7, 0x84, 0x24, 0x88,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00
  ]

set_option maxRecDepth 100000 in
def listing : List (Nat × Ext8.Instr × Nat) := [
  (0, .base (.push (.r15)), 2), -- 0x402de0
  (2, .base (.push (.r14)), 2), -- 0x402de2
  (4, .base (.push (.r13)), 2), -- 0x402de4
  (6, .base (.push (.r12)), 2), -- 0x402de6
  (8, .base (.push (.rbp)), 1), -- 0x402de8
  (9, .base (.push (.rbx)), 1), -- 0x402de9
  (10, .base (.mov (.q) (.reg (.rbx)) (.rdx)), 3), -- 0x402dea
  (13, .base (.aluI (.q) (.sub) (.reg (.rsp)) 0x00000098#32), 7), -- 0x402ded
  (20, .base (.movx false (.d) (.b) (.rbp) (.mem (Mem.ofReg .rdi none 0x00000000#32))), 3), -- 0x402df4
  (23, .base (.mov (.q) (.mem (Mem.ofReg .rsp none 0x00000000#32)) (.rdi)), 4), -- 0x402df7
  (27, .base (.mov (.q) (.mem (Mem.ofReg .rsp none 0x00000010#32)) (.rsi)), 5), -- 0x402dfb
  (32, .base (.test8 (.reg (.rbp)) (.rbp)), 3), -- 0x402e00
  (35, .base (.jcc (.e) 0x00000445#32), 6), -- 0x402e03
  (41, .base (.movI32 (.rax) 0x00000001#32), 5), -- 0x402e09
  (46, .base (.movI32 (.r13) 0x0000002d#32), 6), -- 0x402e0e
  (52, .base (.jmp8 0x23#8), 2), -- 0x402e14
  (54, .base (.nop 9), 10), -- 0x402e16
  (64, .base (.load (.q) (.rsi) (Mem.ofReg .rsp none 0x00000000#32)), 4), -- 0x402e20
  (68, .base (.movx false (.d) (.b) (.rbp) (.mem (Mem.ofReg .rsi (some (ix .rax 0x0#2)) 0x00000000#32))), 4), -- 0x402e24
  (72, .base (.aluI8 (.q) (.add) (.reg (.rax)) 0x01#8), 4), -- 0x402e28
  (76, .base (.movx false (.d) (.b) (.r13) (.mem (Mem.ofReg .rax none 0x00406051#32))), 8), -- 0x402e2c
  (84, .base (.test8 (.reg (.rbp)) (.rbp)), 3), -- 0x402e34
  (87, .base (.jcc8 (.e) 0x37#8), 2), -- 0x402e37
  (89, .new (.alu (.cmp) (.reg (.low (.rbp))) (.low (.r13))), 3), -- 0x402e39
  (92, .base (.jcc8 (.e) 0xe2#8), 2), -- 0x402e3c
  (94, .base (.movI (.d) (.mem (Mem.ofReg .rbx none 0x00000000#32)) 0x00000000#32), 6), -- 0x402e3e
  (100, .base (.load (.q) (.rdx) (Mem.ofReg .rsp none 0x00000000#32)), 4), -- 0x402e44
  (104, .base (.alu (.d) (.xor) (.reg (.rcx)) (.rcx)), 2), -- 0x402e48
  (106, .base (.movI32 (.rdi) 0x00000101#32), 5), -- 0x402e4a
  (111, .base (.movI (.q) (.reg (.rsi)) 0xffffff9c#32), 7), -- 0x402e4f
  (118, .base (.call 0xffffe1b5#32), 5), -- 0x402e56
  (123, .base (.mov (.q) (.reg (.r15)) (.rax)), 3), -- 0x402e5b
  (126, .base (.test (.q) (.reg (.rax)) (.rax)), 3), -- 0x402e5e
  (129, .base (.jcc (.s) 0x000002aa#32), 6), -- 0x402e61
  (135, .base (.cxe (.q)), 2), -- 0x402e67
  (137, .base (.mov (.q) (.mem (Mem.ofReg .rsp none 0x00000008#32)) (.rax)), 5), -- 0x402e69
  (142, .base (.jmp8 0x1e#8), 2), -- 0x402e6e
  (144, .base (.movI (.d) (.mem (Mem.ofReg .rbx none 0x00000000#32)) 0x00000000#32), 6), -- 0x402e70
  (150, .base (.test8 (.reg (.r13)) (.r13)), 3), -- 0x402e76
  (153, .base (.jcc8 (.ne) 0xc9#8), 2), -- 0x402e79
  (155, .base (.movI (.d) (.mem (Mem.ofRip 0x0000721b#32)) 0x00000001#32), 10), -- 0x402e7b
  (165, .base (.movI (.q) (.mem (Mem.ofReg .rsp none 0x00000008#32)) 0x00000000#32), 9), -- 0x402e85
  (174, .base (.movabs (.rax) 0xbb67ae856a09e667#64), 10), -- 0x402e8e
  (184, .base (.movI32 (.rbx) 0x00000040#32), 5), -- 0x402e98
  (189, .base (.movI (.q) (.mem (Mem.ofReg .rsp none 0x00000080#32)) 0x00000000#32), 12), -- 0x402e9d
  (201, .base (.mov (.q) (.mem (Mem.ofReg .rsp none 0x00000020#32)) (.rax)), 5), -- 0x402ea9
  (206, .base (.movabs (.rax) 0xa54ff53a3c6ef372#64), 10), -- 0x402eae
  (216, .base (.mov (.q) (.mem (Mem.ofReg .rsp none 0x00000028#32)) (.rax)), 5), -- 0x402eb8
  (221, .base (.movabs (.rax) 0x9b05688c510e527f#64), 10), -- 0x402ebd
  (231, .base (.mov (.q) (.mem (Mem.ofReg .rsp none 0x00000030#32)) (.rax)), 5), -- 0x402ec7
  (236, .base (.movabs (.rax) 0x5be0cd191f83d9ab#64), 10), -- 0x402ecc
  (246, .base (.mov (.q) (.mem (Mem.ofReg .rsp none 0x00000038#32)) (.rax)), 5), -- 0x402ed6
  (251, .base (.movI (.q) (.mem (Mem.ofReg .rsp none 0x00000088#32)) 0x00000000#32), 12), -- 0x402edb
  (263, .base (.nop 8), 9) -- 0x402ee7
  ]

set_option maxRecDepth 100000 in
/-- **The lift**: every listed instruction is what the `Ext8` decoder reads at its offset. -/
theorem listing_valid : SegVC.Listing.valid Isa.sys8 code listing = true := by decide

set_option maxRecDepth 100000 in
/-- The executable segment holds these bytes at `0x402de0`. -/
theorem seg1_code : (Image.seg1.contents.drop (0x402de0 - 0x401000)).take 272 = code := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Loading puts the region at `base`.** -/
theorem loaded {memory : Silmaril.Process.Memory} (h : Image.image.Mapped memory) :
    Ext.Loaded memory base code := by
  have := readWith_segment h seg1_mem Image.image_wf (acc := .execute) (by decide)
    (0x402de0 - 0x401000) 272 (by decide) (by decide)
  rw [seg1_code] at this
  exact this

set_option maxRecDepth 100000 in
theorem code_length : code.length = 272 := by decide

end Silmaril.Apps.Sha256sum.Binary.Digest.Prologue
