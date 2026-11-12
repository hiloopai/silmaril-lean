module

public import Silmaril.Libc.X86Alloc.Spec.Defs

/-!
# Allocator ladder, rung 01: the allocator that never allocates

`examples/alloc-ladder/01-never/alloc.c` at `-O2` (`pinned/alloc`): `malloc` is
`xor %eax, %eax; ret` at `0x401330`, `free` is `ret` at `0x401340`. The code region is the
32 bytes `[0x401330, 0x401350)`, padding included; the static state is empty.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.Never

open Silmaril.X86 (Byte)

/-- `[0x401330, 0x401350)` of `pinned/alloc`. -/
def code : List Byte :=
  [0x31, 0xc0, 0xc3, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x00,
   0xc3, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x44, 0x00, 0x00]

/-- The layout: code at `0x401330`, `malloc` there, `free` at `0x401340`, no static state (the
empty slice at the start of `.bss`, `0x40301c`). -/
def layout : Layout where
  codeAddr := 0x401330
  code := code
  malloc := 0x401330
  free := 0x401340
  dataAddr := 0x40301c
  data := []

end Silmaril.Libc.X86Alloc.Ladder.Never
