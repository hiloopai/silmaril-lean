module

public import Silmaril.X86.Lift.Transcript
public import Silmaril.X86.SegVC
public import Silmaril.Apps.Sha256sum.Binary.Load

/-! # The system-call wrapper `sc3` of `sha256sum-min`

`sc3(nr, a, b, c)` at `0x401010` moves its arguments into the x86-64 Linux system-call
registers and traps: `mov %rdi,%rax; mov %rsi,%rdi; mov %rdx,%rsi; mov %rcx,%rdx; syscall;
ret` (then one byte of padding). Every system call of the stdin tier except `exit_group`
goes through it. The listing is re-checked against Silmaril's decoder (`listing_valid`, by
`decide`); `loaded` ties the bytes to the loaded image.

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Sc3

open Silmaril.X86 (Byte)
open Silmaril.X86

/-- The wrapper's load address. -/
def base : Word := 0x401010#64

def code : List Byte :=
  [0x48, 0x89, 0xf8, 0x48, 0x89, 0xf7, 0x48, 0x89, 0xd6, 0x48, 0x89, 0xca, 0x0f, 0x05, 0xc3,
    0x90]

def listing : List (Nat × Ext.Instr × Nat) := [
  (0, .mov .q (.reg .rax) .rdi, 3), -- 0x401010: 4889f8  mov %rdi,%rax
  (3, .mov .q (.reg .rdi) .rsi, 3), -- 0x401013: 4889f7  mov %rsi,%rdi
  (6, .mov .q (.reg .rsi) .rdx, 3), -- 0x401016: 4889d6  mov %rdx,%rsi
  (9, .mov .q (.reg .rdx) .rcx, 3), -- 0x401019: 4889ca  mov %rcx,%rdx
  (14, .ret, 1)                     -- 0x40101e: c3  ret
  ]

/-- **The lift**: every listed instruction is what Silmaril's decoder reads at its offset. -/
theorem listing_valid : SegVC.Listing.valid (SegVC.Isa.ext 0) code listing = true := by decide

/-- The `syscall` is at offset 12. -/
theorem code_syscall : (code.drop 12).take 2 = [0x0f, 0x05] := by decide

/-- The executable segment holds these bytes at `0x401010`. -/
theorem seg1_code : (Image.seg1.contents.drop (0x401010 - 0x401000)).take 16 = code := by
  decide +kernel

/-- **Loading puts the wrapper at `base`.** -/
theorem loaded {memory : Silmaril.Process.Memory} (h : Image.image.Mapped memory) :
    Ext.Loaded memory base code := by
  have := readWith_segment h seg1_mem Image.image_wf (acc := .execute) (by decide)
    (0x401010 - 0x401000) 16 (by decide) (by decide)
  rw [seg1_code] at this
  exact this

end Silmaril.Apps.Sha256sum.Binary.Sc3
