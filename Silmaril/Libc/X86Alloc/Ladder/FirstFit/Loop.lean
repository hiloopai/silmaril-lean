module

public import Silmaril.Libc.X86Alloc.Ladder.FirstFit.Defs
public import Silmaril.Libc.X86Alloc.HdrSeg.Defs

/-!
# Rung 05 (first-fit): the malloc loop invariant (scaffold for the open functional row)

`malloc` walks the free list from `freelist` looking for the first block of at least `need =
roundUp 16 n` payload bytes, splitting it when 32 or more bytes would remain. The loop head is
`0x401352`. This module states the loop invariant and the measure the proof uses with
`Silmaril.Raw.Libc.X86Alloc.Loop.SPEC.loop`; discharging the per-block body steps
(`Silmaril.Raw.Libc.X86Alloc.Whole.c_whole` for the register arithmetic, `plist_hdrSeg` to
close the walk) is still open.

* `Walk need passed cur rest`: the memory at the loop head after walking `passed` (all of payload
  size `< need`) to the block at `cur`, with `rest` the blocks from `cur` on: the open segment
  `plist freelistAddr passed cur`, the tail `hdrSeg rest cur`, and the pure facts (`rsi =
  lastSlot`, every passed block too small). The measure is `rest.length`.

`freelistAddr = 0x4030a0`. The payload returned is `cur + 16`; the split point is `cur + 16 +
need`.
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.FirstFit

open Silmaril.X86 (Word)
open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc

/-- The free-list global. -/
abbrev freelistAddr : Nat := 0x4030a0

/-- The memory at the malloc loop head (`0x401352`): the walked-over segment, the block at `cur`
and its tail, with every walked block too small for `need`. -/
def Walk (need : Nat) (passed : List Block) (cur : Word) (rest : List Block) : SProp :=
  ⌜(∀ b ∈ passed, b.size < need) ∧ cur ≠ 0⌝ ∗
    plist (BitVec.ofNat 64 freelistAddr) passed cur ∗ hdrSeg rest cur

/-- The loop measure: the number of blocks still to inspect. -/
def walkMeasure (rest : List Block) : Nat := rest.length

end Silmaril.Libc.X86Alloc.Ladder.FirstFit
