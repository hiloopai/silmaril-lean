module

public import Silmaril.Libc.X86Alloc.Spec.Defs

/-!
# Allocator ladder, rung 05: first fit with splitting, no coalescing

`examples/alloc-ladder/05-firstfit/alloc.c` at `-O2` (`pinned/alloc`): `malloc` at `0x401330`, `free` at
`0x4013b0`; `freelist` at `0x4030a0` and the 4096-byte `heap` at `0x4030b0`, both in `.data`
(the heap starts as one free block: header `{4080, NULL}`). The code has loops (the free-list
walk), so its proof needs loop invariants (a list-segment predicate over the headers, `HdrSeg`);
the proofs are in `Ladder.FirstFit.Thms`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.FirstFit

open Silmaril.X86 (Word Byte)
open Silmaril.Libc.X86Alloc

/-- `[0x401330, 0x4013d0)` of `pinned/alloc`. -/
def code : List Byte :=
  [0x48, 0x81, 0xff, 0x00, 0x10, 0x00, 0x00, 0x77, 0x57, 0x48, 0x8b, 0x05, 0x60, 0x1d, 0x00, 0x00,
   0x48, 0x83, 0xc7, 0x0f, 0x48, 0x83, 0xe7, 0xf0, 0x48, 0x85, 0xc0, 0x74, 0x45, 0xbe, 0xa0, 0x30,
   0x40, 0x00, 0x48, 0x8b, 0x10, 0x48, 0x8b, 0x48, 0x08, 0x48, 0x39, 0xfa, 0x72, 0x3a, 0x4c, 0x8d,
   0x47, 0x20, 0x4c, 0x39, 0xc2, 0x72, 0x19, 0x48, 0x29, 0xfa, 0x4c, 0x8d, 0x44, 0x38, 0x10, 0x48,
   0x83, 0xea, 0x10, 0x49, 0x89, 0x48, 0x08, 0x4c, 0x89, 0xc1, 0x49, 0x89, 0x10, 0x48, 0x89, 0x38,
   0x48, 0x89, 0x0e, 0x48, 0x83, 0xc0, 0x10, 0xc3, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x31, 0xc0, 0xc3, 0x0f, 0x1f, 0x44, 0x00, 0x00, 0x48, 0x8d, 0x70, 0x08, 0x48, 0x85, 0xc9, 0x74,
   0xef, 0x48, 0x89, 0xc8, 0xeb, 0xac, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x48, 0x85, 0xff, 0x74, 0x16, 0x48, 0x8b, 0x05, 0xe4, 0x1c, 0x00, 0x00, 0x48, 0x83, 0xef, 0x10,
   0x48, 0x89, 0x47, 0x08, 0x48, 0x89, 0x3d, 0xd5, 0x1c, 0x00, 0x00, 0xc3, 0x0f, 0x1f, 0x40, 0x00]

/-- The static state as loaded: `freelist = &heap`, padding, the first header, zeros. -/
def data : List Byte :=
  Silmaril.Machine.LittleEndian.encodeWords [0x4030b0] ++ List.replicate 8 0 ++
    Silmaril.Machine.LittleEndian.encodeWords [4080, 0] ++ List.replicate 4080 0

/-- The layout. -/
def layout : Layout where
  codeAddr := 0x401330
  code := code
  malloc := 0x401330
  free := 0x4013b0
  dataAddr := 0x4030a0
  data := data

/-- The first block of the free list with at least `need` payload bytes. -/
def ffFind (need : Nat) (fl : List (Word × Nat)) : Option (Word × Nat) :=
  fl.find? fun e => need ≤ e.2

/-- The free list after serving `need` bytes from its first fitting block: the block is split
when at least 32 bytes would remain (a header and a minimal payload), else removed. -/
def ffTake (need : Nat) : List (Word × Nat) → List (Word × Nat)
  | [] => []
  | (h, sz) :: t =>
    if need ≤ sz then
      (if need + 32 ≤ sz then (h + BitVec.ofNat 64 (16 + need), sz - need - 16) :: t else t)
    else (h, sz) :: ffTake need t

/-- **The first-fit reference model** (no coalescing): the state is the free list of
`(header, payload size)` in list order and the live blocks; `free` pushes the block back at the
head with its full payload size. -/
def ref : RefModel where
  St := List (Word × Nat) × List (Word × Nat)
  malloc s n := if 4096 < n then 0 else
    match ffFind (roundUp 16 n) s.1 with
    | some (h, _) => h + 16#64
    | none => 0
  alloc s n :=
    match ffFind (roundUp 16 n) s.1 with
    | some (h, sz) => (ffTake (roundUp 16 n) s.1,
        (h, if roundUp 16 n + 32 ≤ sz then roundUp 16 n else sz) :: s.2)
    | none => s
  dealloc s p _ :=
    match s.2.find? (fun e => e.1 = p - 16#64) with
    | some e => (e :: s.1, s.2.erase e)
    | none => s

/-- The initial state: one free block spanning the arena. -/
def s0 : ref.St := ([(0x4030b0, 4080)], [])

end Silmaril.Libc.X86Alloc.Ladder.FirstFit
