module

public import Silmaril.Libc.X86Alloc.Spec.Defs

/-!
# Allocator ladder, rung 07: segregated size classes

`examples/alloc-ladder/07-sizeclass/alloc.c` at `-O2` (`pinned/alloc`): four size classes of
payload size 16, 32, 64 and 128 bytes, each with an intrusive LIFO free list whose head is a
separate global (`h16` `0x4030e0`, `h32` `0x4030d8`, `h64` `0x4030d0`, `h128` `0x4030c8`);
fresh blocks come from a 4096-byte bump arena (`arena` `0x4030f0`, 16-aligned, cursor `used`
`0x4030e8`). Every block has a 16-byte header whose first word is the payload size of its class,
so `free` finds the class from the header. `malloc(n)` fails for `n > 128`; otherwise it pops the
list of the smallest class holding `n` bytes, or else carves `16 + class` bytes off the arena,
or else fails. The code is loop-free.

```
401330: cmp  $0x10,%rdi        ; n <= 16?          401400: test %rdi,%rdi        # free
401334: ja   401358                                 401403: je   40142d
401336: mov  h16(%rip),%rax                         401405: mov  -0x10(%rdi),%rax ; header
40133d: mov  $0x10,%edx                             401409: cmp  $0x10,%rax
401342: mov  $h16,%ecx                              40140d: je   401440
401347: test %rax,%rax       ; shared: pick         40140f: cmp  $0x20,%rax
40134a: je   401378                                 401413: je   401450
40134c: mov  (%rax),%rdx     ; pop                  401415: cmp  $0x40,%rax
40134f: mov  %rdx,(%rcx)                            401419: je   401430
401352: ret                                         40141b: mov  h128(%rip),%rdx
401358: cmp  $0x20,%rdi                             401422: mov  $h128,%eax
40135c: ja   4013b0                                 401427: mov  %rdx,(%rdi)      ; push
40135e: mov  h32(%rip),%rax                         40142a: mov  %rdi,(%rax)
401365: mov  $0x20,%edx                             40142d: ret
40136a: mov  $h32,%ecx                              401430: mov  h64(%rip),%rdx
40136f: test %rax,%rax                              401437: mov  $h64,%eax
401372: jne  40134c                                 40143c: jmp  401427
401374: nopl 0x0(%rax)                              401440: mov  h16(%rip),%rdx
401378: mov  used(%rip),%rsi ; bump                 401447: mov  $h16,%eax
40137f: mov  $0x1000,%ecx                           40144c: jmp  401427
401384: lea  0x10(%rdx),%rdi                        401450: mov  h32(%rip),%rdx
401388: sub  %rsi,%rcx                              401457: mov  $h32,%eax
40138b: cmp  %rdi,%rcx                              40145c: jmp  401427
40138e: jb   4013ad          ; rax = head = 0
401390: lea  0x10(%rsi),%rax
401394: mov  %rdx,0x4030f0(%rsi)   ; header
40139b: lea  (%rdx,%rax,1),%rcx
40139f: lea  0x403100(%rsi),%rax
4013a6: mov  %rcx,used(%rip)
4013ad: ret
4013b0: cmp  $0x40,%rdi;  4013b4: jbe 4013d8
4013b6: cmp  $0x80,%rdi;  4013bd: ja  4013f0
4013bf: mov  h128(%rip),%rax; mov $0x80,%edx; mov $h128,%ecx; jmp 401347
4013d8: mov  h64(%rip),%rax;  mov $0x40,%edx; mov $h64,%ecx;  jmp 401347
4013f0: xor  %eax,%eax; ret
```

* `ref`: the reference model, state: the four free lists and the arena cursor. Each class is
  **LIFO**; a class whose list is empty is served from the arena, in address order.
* `iface`: each class list as a list segment of headed blocks (`clist`), the unused arena,
  and `strue` for the rest of `.bss`. A token `tok p n` holds the block's header (its class
  word and the padding word) and the tail of the block beyond the `n` requested bytes.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.SizeClass

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep

/-- `[0x401330, 0x401460)` of `pinned/alloc`. -/
def code : List Byte :=
  [0x48, 0x83, 0xff, 0x10, 0x77, 0x22, 0x48, 0x8b, 0x05, 0xa3, 0x1d, 0x00, 0x00, 0xba, 0x10, 0x00,
   0x00, 0x00, 0xb9, 0xe0, 0x30, 0x40, 0x00, 0x48, 0x85, 0xc0, 0x74, 0x2c, 0x48, 0x8b, 0x10, 0x48,
   0x89, 0x11, 0xc3, 0x0f, 0x1f, 0x44, 0x00, 0x00, 0x48, 0x83, 0xff, 0x20, 0x77, 0x52, 0x48, 0x8b,
   0x05, 0x73, 0x1d, 0x00, 0x00, 0xba, 0x20, 0x00, 0x00, 0x00, 0xb9, 0xd8, 0x30, 0x40, 0x00, 0x48,
   0x85, 0xc0, 0x75, 0xd8, 0x0f, 0x1f, 0x40, 0x00, 0x48, 0x8b, 0x35, 0x69, 0x1d, 0x00, 0x00, 0xb9,
   0x00, 0x10, 0x00, 0x00, 0x48, 0x8d, 0x7a, 0x10, 0x48, 0x29, 0xf1, 0x48, 0x39, 0xf9, 0x72, 0x1d,
   0x48, 0x8d, 0x46, 0x10, 0x48, 0x89, 0x96, 0xf0, 0x30, 0x40, 0x00, 0x48, 0x8d, 0x0c, 0x02, 0x48,
   0x8d, 0x86, 0x00, 0x31, 0x40, 0x00, 0x48, 0x89, 0x0d, 0x3b, 0x1d, 0x00, 0x00, 0xc3, 0x66, 0x90,
   0x48, 0x83, 0xff, 0x40, 0x76, 0x22, 0x48, 0x81, 0xff, 0x80, 0x00, 0x00, 0x00, 0x77, 0x31, 0x48,
   0x8b, 0x05, 0x02, 0x1d, 0x00, 0x00, 0xba, 0x80, 0x00, 0x00, 0x00, 0xb9, 0xc8, 0x30, 0x40, 0x00,
   0xe9, 0x72, 0xff, 0xff, 0xff, 0x0f, 0x1f, 0x00, 0x48, 0x8b, 0x05, 0xf1, 0x1c, 0x00, 0x00, 0xba,
   0x40, 0x00, 0x00, 0x00, 0xb9, 0xd0, 0x30, 0x40, 0x00, 0xe9, 0x59, 0xff, 0xff, 0xff, 0x66, 0x90,
   0x31, 0xc0, 0xc3, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x00,
   0x48, 0x85, 0xff, 0x74, 0x28, 0x48, 0x8b, 0x47, 0xf0, 0x48, 0x83, 0xf8, 0x10, 0x74, 0x31, 0x48,
   0x83, 0xf8, 0x20, 0x74, 0x3b, 0x48, 0x83, 0xf8, 0x40, 0x74, 0x15, 0x48, 0x8b, 0x15, 0xa6, 0x1c,
   0x00, 0x00, 0xb8, 0xc8, 0x30, 0x40, 0x00, 0x48, 0x89, 0x17, 0x48, 0x89, 0x38, 0xc3, 0x66, 0x90,
   0x48, 0x8b, 0x15, 0x99, 0x1c, 0x00, 0x00, 0xb8, 0xd0, 0x30, 0x40, 0x00, 0xeb, 0xe9, 0x66, 0x90,
   0x48, 0x8b, 0x15, 0x99, 0x1c, 0x00, 0x00, 0xb8, 0xe0, 0x30, 0x40, 0x00, 0xeb, 0xd9, 0x66, 0x90,
   0x48, 0x8b, 0x15, 0x81, 0x1c, 0x00, 0x00, 0xb8, 0xd8, 0x30, 0x40, 0x00, 0xeb, 0xc9, 0x66, 0x90]

/-- `h128`, the lowest static address of the allocator. -/
abbrev h128A : Nat := 0x4030c8
/-- `h64`. -/
abbrev h64A : Nat := 0x4030d0
/-- `h32`. -/
abbrev h32A : Nat := 0x4030d8
/-- `h16`. -/
abbrev h16A : Nat := 0x4030e0
/-- `used`. -/
abbrev usedA : Nat := 0x4030e8
/-- `arena`. -/
abbrev arena : Nat := 0x4030f0

/-- The layout: the static state is `[h128, arena + 4096)`, all zero at load (`.bss`). -/
def layout : Layout where
  codeAddr := 0x401330
  code := code
  malloc := 0x401330
  free := 0x401400
  dataAddr := h128A
  data := List.replicate (arena + 4096 - h128A) 0

/-- The payload size of the class serving a request of `n ≤ 128` bytes. -/
def cls (n : Nat) : Nat := if n ≤ 16 then 16 else if n ≤ 32 then 32 else if n ≤ 64 then 64 else 128

/-- The address of the head of class `c`. -/
def headA (c : Nat) : Nat := if c = 16 then h16A else if c = 32 then h32A else if c = 64 then h64A
  else h128A

/-- **The abstract state**: the four free lists and the arena cursor. -/
structure St where
  l16 : List Word
  l32 : List Word
  l64 : List Word
  l128 : List Word
  u : Nat

/-- The list of class `c`. -/
def St.lst (s : St) (c : Nat) : List Word :=
  if c = 16 then s.l16 else if c = 32 then s.l32 else if c = 64 then s.l64 else s.l128

/-- Replace the list of class `c`. -/
def St.set (s : St) (c : Nat) (l : List Word) : St :=
  if c = 16 then { s with l16 := l } else if c = 32 then { s with l32 := l }
  else if c = 64 then { s with l64 := l } else { s with l128 := l }

/-- **The reference model**: LIFO per class, then the arena. -/
def ref : RefModel where
  St := St
  malloc s n := if 128 < n then 0 else
    match s.lst (cls n) with
    | p :: _ => p
    | [] => if cls n + 16 ≤ 4096 - s.u then BitVec.ofNat 64 (arena + s.u + 16) else 0
  alloc s n := match s.lst (cls n) with
    | _ :: ps => s.set (cls n) ps
    | [] => { s with u := s.u + cls n + 16 }
  dealloc s p n := s.set (cls n) (p :: s.lst (cls n))

/-- A free list of class `c` from `h` through the blocks `ps`: each non-null and 16-aligned,
with the class word in its header, a padding word, and the link in its first payload word. -/
def clist (c : Nat) : List Word → Word → SProp
  | [], h => ⌜h = 0⌝
  | p :: ps, h => ⌜h = p ∧ p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat⌝ ∗
      wordPt (p.toNat - 16) (BitVec.ofNat 64 c) ∗ blockAny (p.toNat - 8) 8 ∗
      sexists fun q => wordPt p.toNat q ∗ blockAny (p.toNat + 8) (c - 8) ∗ clist c ps q

/-- The head of class `c` and its list. -/
def hd (c : Nat) (l : List Word) : SProp := sexists fun h => wordPt (headA c) h ∗ clist c l h

/-- The heads of the classes other than `c` (all four for `c = 0`). -/
def others (s : St) (c : Nat) : SProp :=
  (if c = 16 then emp else hd 16 s.l16) ∗ (if c = 32 then emp else hd 32 s.l32) ∗
    (if c = 64 then emp else hd 64 s.l64) ∗ (if c = 128 then emp else hd 128 s.l128)

/-- The arena cursor and the unused arena. -/
def arenaPt (u : Nat) : SProp := wordPt usedA (BitVec.ofNat 64 u) ∗ blockAny (arena + u) (4096 - u)

/-- The allocator's memory at an abstract state. -/
def iface : IfaceL ref.toCap where
  mmS (s : St) := ⌜s.u ≤ 4096 ∧ s.u % 16 = 0⌝ ∗ others s 0 ∗ arenaPt s.u ∗ strue
  tok p n := ⌜n ≤ 128 ∧ p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat⌝ ∗
    wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
    blockAny (p.toNat + n) (cls n - n)
  align := 16
  stack := 0

/-- The initial state: empty lists, an unused arena. -/
def s0 : St := ⟨[], [], [], [], 0⟩

/-- **The size-class capacity model**: the number of free blocks of each class (`k c`, for the
class sizes `c`) and the bytes left in the arena (`r`). A request of `n ≤ 128` bytes must succeed
when its class has a free block or the arena has room for the class plus a header; it takes a
free block of the class if there is one, else `16 + class` arena bytes; `free` returns a block
to its class. -/
structure CapSt where
  k : Nat → Nat
  r : Nat

/-- The size-class capacity model. -/
def cap : CapModel where
  St := CapSt
  avail s n := n ≤ 128 ∧ (0 < s.k (cls n) ∨ cls n + 16 ≤ s.r)
  alloc s n _ := if 0 < s.k (cls n) then { s with k := Function.update s.k (cls n) (s.k (cls n) - 1) }
    else { s with r := s.r - (cls n + 16) }
  dealloc s _ n := { s with k := Function.update s.k (cls n) (s.k (cls n) + 1) }

/-- A class size. -/
def IsClass (c : Nat) : Prop := c = 16 ∨ c = 32 ∨ c = 64 ∨ c = 128

instance : DecidablePred IsClass := fun c => by unfold IsClass; infer_instance

/-- The abstraction: the lengths of the class lists and the unused arena. -/
def α (s : St) : CapSt := ⟨fun c => if IsClass c then (s.lst c).length else 0, 4096 - s.u⟩

/-- The capacity at load: no free blocks, 4096 arena bytes. -/
def capS0 : CapSt := α s0

end Silmaril.Libc.X86Alloc.Ladder.SizeClass
