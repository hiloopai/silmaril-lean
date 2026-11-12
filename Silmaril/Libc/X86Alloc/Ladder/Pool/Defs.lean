module

public import Silmaril.Libc.X86Alloc.Spec.Defs

/-!
# Allocator ladder, rung 04: fixed-size blocks with a LIFO free list

`examples/alloc-ladder/04-pool/alloc.c` at `-O2` (`pinned/alloc`): 64 blocks of 64 bytes in
`pool` (`0x4030e0`, 16-aligned); `head` (`0x4030d0`) is an intrusive free list of returned blocks
(the link is a block's first word); `next` (`0x4030c8`) counts the blocks ever handed out by
bumping. `malloc(n)` fails for `n > 64`; otherwise it pops `head` if non-empty, else hands out
block `next` if `next < 64`, else fails. `free(p)` pushes `p` (and ignores `NULL`).

```
401330: cmp  $0x40,%rdi            401390: test %rdi,%rdi          # free
401334: ja   401380                401393: je   4013a6
401336: mov  0x1d93(%rip),%rax     401395: mov  0x1d34(%rip),%rax  # head
40133d: test %rax,%rax             40139c: mov  %rdi,0x1d2d(%rip)  # head
401340: je   401350                4013a3: mov  %rax,(%rdi)
401342: mov  (%rax),%rdx           4013a6: ret
401345: mov  %rdx,0x1d84(%rip)     # head
40134c: ret
401350: mov  0x1d71(%rip),%rdx     # next
401357: cmp  $0x3f,%rdx
40135b: ja   401382                # returns rax = head = 0
40135d: mov  %rdx,%rax
401360: add  $0x1,%rdx
401364: shl  $0x6,%rax
401368: mov  %rdx,0x1d59(%rip)     # next
40136f: add  $0x4030e0,%rax
401375: ret
401380: xor  %eax,%eax
401382: ret
```

* `ref`: the reference model, state `(free list, next)`: **LIFO reuse** (the most recently freed
  block is returned first), then bump order.
* `iface`: the free list as a list segment of 64-byte blocks (`flist`), the never-used tail of the
  pool, and `strue` for the padding. A token `tok p n` holds the tail of the block beyond the `n`
  requested bytes, so `free` gets the whole block back.
* `cap`/`α`: the pool capacity model (`CapModel.pool 64`), at `|free list| + (64 - next)`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.Pool

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep

/-- `[0x401330, 0x4013b0)` of `pinned/alloc`. -/
def code : List Byte :=
  [0x48, 0x83, 0xff, 0x40, 0x77, 0x4a, 0x48, 0x8b, 0x05, 0x93, 0x1d, 0x00, 0x00, 0x48, 0x85, 0xc0,
   0x74, 0x0e, 0x48, 0x8b, 0x10, 0x48, 0x89, 0x15, 0x84, 0x1d, 0x00, 0x00, 0xc3, 0x0f, 0x1f, 0x00,
   0x48, 0x8b, 0x15, 0x71, 0x1d, 0x00, 0x00, 0x48, 0x83, 0xfa, 0x3f, 0x77, 0x25, 0x48, 0x89, 0xd0,
   0x48, 0x83, 0xc2, 0x01, 0x48, 0xc1, 0xe0, 0x06, 0x48, 0x89, 0x15, 0x59, 0x1d, 0x00, 0x00, 0x48,
   0x05, 0xe0, 0x30, 0x40, 0x00, 0xc3, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x31, 0xc0, 0xc3, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x00,
   0x48, 0x85, 0xff, 0x74, 0x11, 0x48, 0x8b, 0x05, 0x34, 0x1d, 0x00, 0x00, 0x48, 0x89, 0x3d, 0x2d,
   0x1d, 0x00, 0x00, 0x48, 0x89, 0x07, 0xc3, 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- `next`. -/
abbrev nextAddr : Nat := 0x4030c8
/-- `head`. -/
abbrev headAddr : Nat := 0x4030d0
/-- `pool`. -/
abbrev pool : Nat := 0x4030e0

/-- The layout: the static state is `[next, pool + 4096)`, all zero at load (`.bss`). -/
def layout : Layout where
  codeAddr := 0x401330
  code := code
  malloc := 0x401330
  free := 0x401390
  dataAddr := nextAddr
  data := List.replicate (pool + 4096 - nextAddr) 0

/-- A free list from `h` through the blocks `ps`: each a non-null 16-aligned 64-byte block whose
first word links to the next. -/
def flist : List Word → Word → SProp
  | [], h => ⌜h = 0⌝
  | p :: ps, h => ⌜h = p ∧ p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗
      sexists fun q => wordPt p.toNat q ∗ blockAny (p.toNat + 8) 56 ∗ flist ps q

/-- **The reference model**: state `(free list, next)`. -/
def ref : RefModel where
  St := List Word × Nat
  malloc s n := if 64 < n then 0 else
    match s.1 with
    | p :: _ => p
    | [] => if s.2 < 64 then BitVec.ofNat 64 (pool + 64 * s.2) else 0
  alloc s _ := match s.1 with
    | _ :: ps => (ps, s.2)
    | [] => ([], s.2 + 1)
  dealloc s p _ := (p :: s.1, s.2)

/-- The allocator's memory at `(free list, next)`. -/
def iface : IfaceL ref.toCap where
  mmS (s : List Word × Nat) := sexists fun h => ⌜s.2 ≤ 64⌝ ∗ wordPt headAddr h ∗ flist s.1 h ∗
    wordPt nextAddr (BitVec.ofNat 64 s.2) ∗ blockAny (pool + 64 * s.2) (64 * (64 - s.2)) ∗ strue
  tok p n := ⌜n ≤ 64 ∧ p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗ blockAny (p.toNat + n) (64 - n)
  align := 16
  stack := 0

/-- Pool capacity: 64-byte blocks. -/
abbrev cap : CapModel := CapModel.pool 64

/-- The number of free blocks. -/
def α (s : List Word × Nat) : Nat := s.1.length + (64 - s.2)

/-- The invariant: at most 64 blocks handed out by bumping, and free blocks are non-null. -/
def Inv : ref.St → Prop := fun (s : List Word × Nat) => s.2 ≤ 64 ∧ ∀ p ∈ s.1, p ≠ 0

end Silmaril.Libc.X86Alloc.Ladder.Pool
