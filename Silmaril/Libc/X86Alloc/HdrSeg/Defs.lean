module

public import Silmaril.X86.Sep.Defs

/-!
# A header list-segment predicate for free-list allocators

The free-list allocators (rungs 05–06, and glibc) keep their free blocks in a singly linked
list of **headed blocks**: a block at address `p` has a 16-byte header (an 8-byte payload size
at `p`, an 8-byte next pointer at `p + 8`) followed by its payload at `p + 16`. A `Block` records
the header address and the payload size.

* `hdrSeg blocks head`: the null-terminated free list whose first block is at `head`, owning each
  block's header, next pointer and payload. `head = 0` for the empty list.
* `plist prev blocks cur`: an **open list segment** from the link slot at `prev` through `blocks`
  to a continuation `cur`: the slot at `prev` holds the first block (or `cur` if `blocks` is
  empty), and each block's next slot is the `prev` of the rest.

These are the reusable pieces for the loop proof: the loop invariant of a free-list walk is
`plist freelist passed cur ∗ hdrSeg rest cur`, with the measure the length of `rest`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep

/-- A free block: its header address and its payload size (a multiple of 16). -/
structure Block where
  addr : Word
  size : Nat

/-- A well-formed block: non-null, 16-aligned, and its header and payload fit below `2 ^ 64`
(so `addr + 16 + k` does not wrap for `k ≤ size`). -/
def Block.WF (b : Block) : Prop :=
  b.addr ≠ 0 ∧ b.addr.toNat % 16 = 0 ∧ b.addr.toNat + 16 + b.size < 2 ^ 64

/-- `hdrSeg blocks head`: the null-terminated free list starting at `head`. -/
def hdrSeg : List Block → Word → SProp
  | [], head => ⌜head = 0⌝
  | b :: rest, head =>
      ⌜head = b.addr ∧ b.WF⌝ ∗ sexists fun nxt =>
        wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗ wordPt (b.addr + 8#64).toNat nxt ∗
        blockAny (b.addr.toNat + 16) b.size ∗ hdrSeg rest nxt

/-- The address of the final link slot after walking `blocks` from the slot at `prev`. -/
def lastSlot (prev : Word) : List Block → Word
  | [] => prev
  | b :: rest => lastSlot (b.addr + 8#64) rest

/-- `plist prev blocks cur`: an open list segment from the slot at `prev` through `blocks`,
ending in a slot that points at `cur`. The slot at `prev` holds the first block (or `cur` when
`blocks = []`); each block's next slot is the `prev` of the rest. -/
def plist (prev : Word) : List Block → Word → SProp
  | [], cur => wordPt prev.toNat cur
  | b :: rest, cur =>
      ⌜b.WF⌝ ∗ wordPt prev.toNat b.addr ∗
        wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
        blockAny (b.addr.toNat + 16) b.size ∗ plist (b.addr + 8#64) rest cur

/-- An open list segment without its final link slot (`plist = plistO ∗ final slot`). -/
def plistO (prev : Word) : List Block → SProp
  | [] => emp
  | b :: rest =>
      ⌜b.WF⌝ ∗ wordPt prev.toNat b.addr ∗
        wordPt b.addr.toNat (BitVec.ofNat 64 b.size) ∗
        blockAny (b.addr.toNat + 16) b.size ∗ plistO (b.addr + 8#64) rest

end Silmaril.Libc.X86Alloc
