module

public import Silmaril.X86.Safe.Exc.Defs

/-!
# The `jmp_buf` and the bytes of a System V `setjmp`/`longjmp`

A minimal `setjmp.S` for x86-64 uses the System V AMD64 layout

| word | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| contents | `rbx` | `rbp` | `r12` | `r13` | `r14` | `r15` | `rsp` after return | return `rip` |

* `words k`, `enc k`: a continuation (`Safe.Cont`) as the eight words and the 64 bytes.
* `jbPt b k`: the 64 writable bytes at `b` hold `k`. It is an ordinary owned resource: the
  `jmp_buf` lives in the caller's frame (or inside a caller's structure) and is passed by
  pointer; a stale `longjmp` after the frame is gone cannot own it.
* `jbAny b`: the 64 bytes are owned, contents unknown (an uninitialised `jmp_buf`).
* `setjmpBytes`, `longjmpBytes`: the two functions as assembled by GNU as 2.42
  (`objdump -d`; 43 and 41 bytes; the listing is in the comments).
* `retVal v`: the value `longjmp(b, v)` makes `setjmp` return.

The triples are in `Sep/JmpBuf/Thms.lean`; a worked example (`catch → throw2 → throw1 →
longjmp`) is in `Sep/JmpBuf/Catch`.
-/

@[expose] public section

namespace Silmaril.X86.Sep.JmpBuf

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Safe (Cont)

/-- The eight words of a `jmp_buf` holding `k`. -/
def words (k : Cont) : List Word := k.cs ++ [k.sp, k.ret]

/-- The 64 bytes of a `jmp_buf` holding `k` (little-endian words). -/
def enc (k : Cont) : List Byte := Silmaril.Machine.LittleEndian.encodeWords (words k)

/-- **The `jmp_buf` at `b` holds `k`.** -/
def jbPt (b : Nat) (k : Cont) : SProp := bytesPt b (enc k)

/-- An owned `jmp_buf` at `b` with unknown contents. -/
def jbAny (b : Nat) : SProp := blockAny b 64

/-- The continuation saved by `setjmp` called with callee-saved registers `cs`, entry stack
pointer `sp` (pointing at the return address `ret`). -/
def saved (cs : List Word) (sp ret : Word) : Cont := ⟨cs, sp + 8#64, ret⟩

/-! ## Bytes -/

/-- `setjmp` (43 bytes). -/
def setjmpBytes : List Byte :=
  [0x48, 0x89, 0x1f,             -- mov %rbx, (%rdi)
   0x48, 0x89, 0x6f, 0x08,       -- mov %rbp, 0x8(%rdi)
   0x4c, 0x89, 0x67, 0x10,       -- mov %r12, 0x10(%rdi)
   0x4c, 0x89, 0x6f, 0x18,       -- mov %r13, 0x18(%rdi)
   0x4c, 0x89, 0x77, 0x20,       -- mov %r14, 0x20(%rdi)
   0x4c, 0x89, 0x7f, 0x28,       -- mov %r15, 0x28(%rdi)
   0x48, 0x8d, 0x54, 0x24, 0x08, -- lea 0x8(%rsp), %rdx
   0x48, 0x89, 0x57, 0x30,       -- mov %rdx, 0x30(%rdi)
   0x48, 0x8b, 0x14, 0x24,       -- mov (%rsp), %rdx
   0x48, 0x89, 0x57, 0x38,       -- mov %rdx, 0x38(%rdi)
   0x31, 0xc0,                   -- xor %eax, %eax
   0xc3]                         -- ret

/-- `longjmp` (41 bytes). -/
def longjmpBytes : List Byte :=
  [0x89, 0xf0,                   -- mov %esi, %eax
   0x85, 0xc0,                   -- test %eax, %eax
   0x75, 0x05,                   -- jne +5
   0xb8, 0x01, 0x00, 0x00, 0x00, -- mov $1, %eax
   0x48, 0x8b, 0x1f,             -- mov (%rdi), %rbx
   0x48, 0x8b, 0x6f, 0x08,       -- mov 0x8(%rdi), %rbp
   0x4c, 0x8b, 0x67, 0x10,       -- mov 0x10(%rdi), %r12
   0x4c, 0x8b, 0x6f, 0x18,       -- mov 0x18(%rdi), %r13
   0x4c, 0x8b, 0x77, 0x20,       -- mov 0x20(%rdi), %r14
   0x4c, 0x8b, 0x7f, 0x28,       -- mov 0x28(%rdi), %r15
   0x48, 0x8b, 0x67, 0x30,       -- mov 0x30(%rdi), %rsp
   0xff, 0x67, 0x38]             -- jmp *0x38(%rdi)

/-- The value `longjmp(b, v)` makes `setjmp` return: `v` as an `int`, or `1` if it is `0`
(zero-extended to 64 bits, as `movl %esi, %eax` does). -/
def retVal (v : Word) : Word :=
  if (v.setWidth 32).setWidth 64 = 0 then 1 else (v.setWidth 32).setWidth 64

end Silmaril.X86.Sep.JmpBuf
