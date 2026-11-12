module

public import Silmaril.Libc.X86Alloc.Ladder.FirstFit.Defs
public import Silmaril.Libc.X86Alloc.HdrSeg.Defs

/-!
# Rung 05 (first-fit): the liveness interface

**Why live and not functional.** First-fit's `free(p)` pushes the block back with its *real*
payload size, which is in the block's header, and the header is held by the client's token
between `malloc` and `free`. `RefModel.dealloc s p n` sees only the requested size `n`, so a
functional reference model cannot know the size it must push, and nothing in the logic ties the
token's size to the model's state (that needs ghost state). The functional row stays open for that
reason. Liveness does not need the size at `free`.

**The capacity model `ffCap`** (state: a set of free blocks the allocator is committed to):

* `avail s n`: `n ≤ 4096` and some block of `s` has at least `roundUp 16 n` payload bytes;
* `alloc s n v`: drop the block at `v - 16` from `s`, and add its split remainder when first fit
  splits it; blocks not in `s` change nothing;
* `dealloc s _ _ = s`: freed blocks are not promised back (an honest, weaker liveness than reuse).

`iface`: the real free list `fl` is a `hdrSeg` from the `freelist` global, with every block of the
abstract state `s` in `fl` (first fit scans the whole list, so a fitting block in `s` means
success). A token holds its block's header (size and next slot) and the payload beyond the
requested `n` bytes.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.FirstFit

open Silmaril.X86 (Word)
open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc

/-- The split remainder of the block `b` after serving `need` bytes. -/
def rem (b : Block) (need : Nat) : Block := ⟨b.addr + BitVec.ofNat 64 (16 + need), b.size - need - 16⟩

/-- The abstract state after `malloc(n)` returned `v`: drop the block at `v - 16`, add its split
remainder. -/
def ffAlloc (s : List Block) (n : Nat) (v : Word) : List Block :=
  match s.find? (fun b => b.addr + 16#64 = v) with
  | some b => s.filter (fun c => c.addr ≠ b.addr) ++
      (if roundUp 16 n + 32 ≤ b.size then [rem b (roundUp 16 n)] else [])
  | none => s

/-- **The first-fit capacity model.** -/
def ffCap : CapModel where
  St := List Block
  avail s n := n ≤ 4096 ∧ ∃ b ∈ s, roundUp 16 n ≤ b.size
  alloc := ffAlloc
  dealloc s _ _ := s

/-- The `freelist` global. -/
abbrev flAddr : Word := 0x4030a0

/-- **The allocator's memory**: the free list `fl ⊇ s` from the `freelist` global. -/
def iface : IfaceL ffCap where
  mmS (s : List Block) := sexists fun (fl : List Block) => sexists fun (h : Word) =>
    ⌜∀ b ∈ s, b ∈ fl⌝ ∗ wordPt flAddr.toNat h ∗ hdrSeg fl h ∗ strue
  tok p n := sexists fun (sz : Nat) =>
    ⌜n ≤ sz ∧ (Block.WF ⟨p - 16#64, sz⟩) ∧ p = (p - 16#64) + 16#64⌝ ∗
      wordPt (p - 16#64).toNat (BitVec.ofNat 64 sz) ∗ blockAny ((p - 16#64) + 8#64).toNat 8 ∗
      blockAny (p.toNat + n) (sz - n)
  align := 16
  stack := 0

/-- The initial abstract state: the one block spanning the heap. -/
def ffS0 : ffCap.St := ([⟨0x4030b0, 4080⟩] : List Block)

end Silmaril.Libc.X86Alloc.Ladder.FirstFit

namespace Silmaril.Libc.X86Alloc.Ladder.FirstFit

open Silmaril.X86 (Word)
open Silmaril.Libc.X86Alloc

/-- The first block of an exact free list with at least `need` payload bytes. -/
def ffFindB (need : Nat) (fl : List Block) : Option Block := fl.find? fun b => need ≤ b.size

/-- The exact free list after serving `need` bytes from its first fitting block. -/
def ffTakeB (need : Nat) : List Block → List Block
  | [] => []
  | b :: t => if need ≤ b.size then (if need + 32 ≤ b.size then rem b need :: t else t)
    else b :: ffTakeB need t

/-- **The relational first-fit model**: the state is the exact free list; `malloc` returns the
first fit (or `NULL` for `n > 4096` or no fit); `free` pushes the block at `p - 16` with *some*
size (the one its header holds). -/
def ffRel : RelModel where
  St := List Block
  malloc s n := if 4096 < n then 0 else
    match ffFindB (roundUp 16 n) s with
    | some b => b.addr + 16#64
    | none => 0
  alloc s n := ffTakeB (roundUp 16 n) s
  dealloc s p _ s' := ∃ sz, s' = ⟨p - 16#64, sz⟩ :: s

end Silmaril.Libc.X86Alloc.Ladder.FirstFit

namespace Silmaril.Libc.X86Alloc.Ladder.FirstFit

open Silmaril.X86 (Word)
open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc

/-- **The allocator's memory at the exact free list `s`** (for `ffRel`); tokens as `iface`'s. -/
def ifaceR : IfaceL ffRel.toCap where
  mmS (s : List Block) := sexists fun (h : Word) => wordPt flAddr.toNat h ∗ hdrSeg s h ∗ strue
  tok := iface.tok
  align := 16
  stack := 0

/-- The initial exact free list. -/
def relS0 : ffRel.St := ([⟨0x4030b0, 4080⟩] : List Block)

end Silmaril.Libc.X86Alloc.Ladder.FirstFit

namespace Silmaril.Libc.X86Alloc.Ladder.Coalesce

open Silmaril.X86 (Word)
open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Ladder.FirstFit (ffRel ifaceR)

/-- **Rung 06's relational model**: `malloc` as first fit (`ffRel`) on the exact free list;
`free` relates to *any* well-formed list (the precise merge relation is open). -/
def coalRel : RelModel where
  St := List Block
  malloc := ffRel.malloc
  alloc := ffRel.alloc
  dealloc _ _ _ _ := True

/-- The exact interface, at `coalRel`. -/
def ifaceC : IfaceL coalRel.toCap where
  mmS (s : List Block) := ifaceR.mmS s
  tok := ifaceR.tok
  align := 16
  stack := 0

end Silmaril.Libc.X86Alloc.Ladder.Coalesce
