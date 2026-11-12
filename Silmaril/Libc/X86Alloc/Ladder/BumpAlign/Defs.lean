module

public import Silmaril.Libc.X86Alloc.Spec.Defs

/-!
# Allocator ladder, rung 03: bump allocation with 16-byte alignment

`examples/alloc-ladder/03-bump-align/alloc.c` at `-O2` (`pinned/alloc`). `used` is the word at
`0x403088`, the 16-aligned 4096-byte `arena` starts at `0x403090`. `malloc(n)` fails iff
`n > 4096 - used`; otherwise it returns `arena + used` and adds `n` rounded up to 16 to `used`
(so `used` stays a multiple of 16). `free` is `ret`.

```
401330: mov 0x1d51(%rip),%rax     # used
401337: mov $0x1000,%edx
40133c: sub %rax,%rdx
40133f: cmp %rdi,%rdx
401342: jb  401360
401344: add $0xf,%rdi
401348: and $0xfffffffffffffff0,%rdi
40134c: add %rax,%rdi
40134f: add $0x403090,%rax
401355: mov %rdi,0x1d2c(%rip)     # used
40135c: ret
401360: xor %eax,%eax
401362: ret
401370: ret                       # free
```

* `ref`: the reference model, state `used`; `iface`: the allocator's memory at each state
  (the `used` word, the unused tail of the arena, and `strue`, which absorbs the rounding
  padding and every freed block: this allocator leaks).
* `cap`/`α`: the bump capacity model (`CapModel.bump (roundUp 16)`), at `4096 - used`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.BumpAlign

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc (roundUp)

/-- `[0x401330, 0x401380)` of `pinned/alloc`. -/
def code : List Byte :=
  [0x48, 0x8b, 0x05, 0x51, 0x1d, 0x00, 0x00, 0xba, 0x00, 0x10, 0x00, 0x00, 0x48, 0x29, 0xc2, 0x48,
   0x39, 0xfa, 0x72, 0x1c, 0x48, 0x83, 0xc7, 0x0f, 0x48, 0x83, 0xe7, 0xf0, 0x48, 0x01, 0xc7, 0x48,
   0x05, 0x90, 0x30, 0x40, 0x00, 0x48, 0x89, 0x3d, 0x2c, 0x1d, 0x00, 0x00, 0xc3, 0x0f, 0x1f, 0x00,
   0x31, 0xc0, 0xc3, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x00,
   0xc3, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x44, 0x00, 0x00]

/-- The `used` word. -/
abbrev usedAddr : Nat := 0x403088
/-- The arena. -/
abbrev arena : Nat := 0x403090
/-- The arena size. -/
abbrev size : Nat := 4096

/-- The layout: the static state is `[used, arena + 4096)`, all zero at load (`.bss`). -/
def layout : Layout where
  codeAddr := 0x401330
  code := code
  malloc := 0x401330
  free := 0x401370
  dataAddr := usedAddr
  data := List.replicate (arena + size - usedAddr) 0

/-- **The reference model**: the state is `used`. -/
def ref : Silmaril.Libc.X86Alloc.RefModel where
  St := Nat
  malloc u n := if n ≤ size - u then BitVec.ofNat 64 (arena + u) else 0
  alloc u n := u + roundUp 16 n
  dealloc u _ _ := u

/-- The allocator's memory at `used = u`. -/
def iface : Silmaril.Libc.X86Alloc.IfaceL ref.toCap where
  mmS (u : Nat) := ⌜u ≤ size ∧ u % 16 = 0⌝ ∗ wordPt usedAddr (BitVec.ofNat 64 u) ∗ blockAny (arena + u) (size - u) ∗
    strue
  tok _ _ := emp
  align := 16
  stack := 0

/-- Bump capacity: a request of `n` bytes costs `n` rounded up to 16. -/
abbrev cap : Silmaril.Libc.X86Alloc.CapModel :=
  Silmaril.Libc.X86Alloc.CapModel.bump (roundUp 16)

/-- The capacity left at `used = u`. -/
def α (u : Nat) : Nat := size - u

end Silmaril.Libc.X86Alloc.Ladder.BumpAlign
