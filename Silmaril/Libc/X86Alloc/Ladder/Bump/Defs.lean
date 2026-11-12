module

public import Silmaril.Libc.X86Alloc.Spec.Defs

/-!
# Allocator ladder, rung 02: bump allocation over a static arena

A C bump allocator compiled at `-O2`, as a static executable. `used` is the word at
`0x403088`, the 4096-byte `arena` starts at `0x4030a0` (both in `.bss`). `malloc(n)` fails iff
`n > 4096 - used`; otherwise it returns `arena + used` and adds `n` to `used`. `free` is `ret`.

```
401330: mov 0x1d51(%rip),%rax     # used
401337: mov $0x1000,%edx
40133c: sub %rax,%rdx
40133f: cmp %rdi,%rdx
401342: jb  401358
401344: add %rax,%rdi
401347: add $0x4030a0,%rax
40134d: mov %rdi,0x1d34(%rip)     # used
401354: ret
401358: xor %eax,%eax
40135a: ret
401360: ret                       # free
```

* `ref`: the reference model, state `used`; `iface`: the allocator's memory at each state
  (the `used` word, the unused tail of the arena, and `strue`, which absorbs the padding before
  the arena and every freed block: this allocator leaks).
* `cap`/`α`: the bump capacity model (`CapModel.bump id`), at `4096 - used`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.Bump

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep

/-- `[0x401330, 0x401370)` of that executable. -/
def code : List Byte :=
  [0x48, 0x8b, 0x05, 0x51, 0x1d, 0x00, 0x00, 0xba, 0x00, 0x10, 0x00, 0x00, 0x48, 0x29, 0xc2, 0x48,
   0x39, 0xfa, 0x72, 0x14, 0x48, 0x01, 0xc7, 0x48, 0x05, 0xa0, 0x30, 0x40, 0x00, 0x48, 0x89, 0x3d,
   0x34, 0x1d, 0x00, 0x00, 0xc3, 0x0f, 0x1f, 0x00, 0x31, 0xc0, 0xc3, 0x0f, 0x1f, 0x44, 0x00, 0x00,
   0xc3, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x44, 0x00, 0x00]

/-- The `used` word. -/
abbrev usedAddr : Nat := 0x403088
/-- The arena. -/
abbrev arena : Nat := 0x4030a0
/-- The arena size. -/
abbrev size : Nat := 4096

/-- The layout: the static state is `[used, arena + 4096)`, all zero at load (`.bss`). -/
def layout : Layout where
  codeAddr := 0x401330
  code := code
  malloc := 0x401330
  free := 0x401360
  dataAddr := usedAddr
  data := List.replicate (arena + size - usedAddr) 0

/-- **The reference model**: the state is `used`. -/
def ref : Silmaril.Libc.X86Alloc.RefModel where
  St := Nat
  malloc u n := if n ≤ size - u then BitVec.ofNat 64 (arena + u) else 0
  alloc u n := u + n
  dealloc u _ _ := u

/-- The allocator's memory at `used = u`. -/
def iface : Silmaril.Libc.X86Alloc.IfaceL ref.toCap where
  mmS (u : Nat) := ⌜u ≤ size⌝ ∗ wordPt usedAddr (BitVec.ofNat 64 u) ∗ blockAny (arena + u) (size - u) ∗
    strue
  tok _ _ := emp
  align := 1
  stack := 0

/-- Bump capacity: a request of `n` bytes costs `n`. -/
abbrev cap : Silmaril.Libc.X86Alloc.CapModel := Silmaril.Libc.X86Alloc.CapModel.bump id

/-- The capacity left at `used = u`. -/
def α (u : Nat) : Nat := size - u

end Silmaril.Libc.X86Alloc.Ladder.Bump
