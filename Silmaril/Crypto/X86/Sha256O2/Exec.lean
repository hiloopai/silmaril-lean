module

public import Silmaril.Crypto.X86.Sha256O2
public import Silmaril.Crypto.X86.Sha256O2.Decode
public import Silmaril.Crypto.X86.Sha256O2.Listing
public import Silmaril.X86.Ext.Loop
public import Silmaril.Crypto.SHA256.Rounds
public import Silmaril.Crypto.SHA256.Schedule

/-!
# Symbolically executing the clang `-O2` image

The bridge between `Silmaril.X86.Ext.SymExec`/`Store`/`Loop` (generic, Track
2c) and `Silmaril.Crypto.X86.Sha256O2` (this image). It is the `-O2` sibling
of `Silmaril/Crypto/X86/Sha256O0/Exec.lean` and follows its shape: read that
file first.

## What is different at `-O2`

The `-O0` prologue is `push %rbp; mov %rsp,%rbp; sub $0xe0,%rsp`, so there is
one push and the frame pointer does the rest. Here there are **six** pushes
and no frame pointer:

```
  0x00:  55              push %rbp      -- an ordinary callee-saved GPR here
  0x01:  41 57           push %r15
  0x03:  41 56           push %r14
  0x05:  41 55           push %r13
  0x07:  41 54           push %r12
  0x09:  53              push %rbx
  0x0a:  48 81 ec a8..   sub  $0xa8,%rsp
```

Six near-identical steps is exactly the case for a lemma rather than six
proofs, so `stepOpt_push` below does the push once, generically, and
`prologue_pushes` chains it six times. `stepOpt_push` mentions nothing about
SHA-256 — only `Loaded`, `decode` and `Instr.push` — and is stated over an
arbitrary `base`/`bytes`; see the note at the end about where it belongs.

## The frame

`frameSize = 216` and `sysv64.redZone = 128`, so the callee owns
`[rspEntry − 344, rspEntry)` and `frameExtent = 344`. `SysVEntry.frameMapped`
gives one permission over that whole span and `frame_writable`/`frame_readable`
cut any slot out of it, via `Memory.Permitted.sub`. Because
`Stored.permitted_iff` says a store never changes what is mapped, these are
proved once against the entry memory and transported along the run.

Note the arithmetic is tight here in a way it is not at `-O0`: the six pushes
reach down to `rspEntry − 48`, the `sub` puts `%rsp` at `rspEntry − 216`, and
the body's lowest access is at `rspEntry − 344`, which is the floor exactly.
See `Sha256O2/Image.lean`.

## What belongs in an invariant, and what does not

**Anything disjoint from the modifies set does not need to be in the invariant
at all.** If a fact is about memory the function provably never writes, it can
be *recovered* at any point in the run from the footprint, rather than carried
from iteration to iteration.

Two uses of the rule here, both of which removed a field that would otherwise
have been threaded through every structure in the chain:

* `retAddr_preserved` — the return address at `[rspEntry]` is outside the
  footprint, so the epilogue reconstructs it instead of the body carrying it.
* `blockBytes_preserved` — `block[]` is disjoint from both halves of the
  modifies set, so L1's pinned block word is recovered at each iteration from
  `L1Inv.frame` alone. Without this, `L1Inv` would need a field pinning
  `block[]`'s bytes, and `bs` would have to be threaded through the weak chain
  as well, which is exactly the kind of change that makes a strengthening
  expensive.

The rule is worth stating because the instinct is the opposite: when a proof
needs a fact at iteration `i`, the reflex is to put it in the invariant. Ask
first whether the function can even write the memory it is about. If it
cannot, the footprint already proves it, and the invariant stays smaller — and
a smaller invariant is what keeps `preserve` cheap.

The dual also holds and is used throughout: **a step or loop that writes
nothing needs neither a permission nor a disjointness fact.** L3 writes no
memory at all, which is why `L3Inv` has no `frame` field and no slot rule.

## `rw` and the width boundary

A fact that cost this file three sightings before it was understood, and that
explains all of them:

> **`rw` leaves `rotateLeft E 26 = rotateLeft E 26` unclosed** when the two
> sides differ only in an implicit width. `rw`'s closing reflexivity check runs
> at **reducible** transparency, and `Sz.d.bits` is not reducible, so it does
> not unfold there. A trailing `rfl` — which runs at default transparency —
> closes every such goal.

The symptom is a goal that is *printed identically on both sides* and still
reported as unsolved, which reads as a pretty-printer artifact or a real
mismatch rather than as a transparency setting. It is neither.

The structural response is `read32` below: cross the width boundary **once, at
the read**, rather than ascribing at each use. Ascribing at the use fixes the
specification side and breaks the machine side; ascribing the entry values does
the reverse. One crossing at a chosen boundary is the rule; the read is the
cheapest boundary in this file.

## Reading the image

`Sha256O2.image` is `raw` with four relocated bytes at `relocOffset = 0xb7`.
Only one instruction of the 133 reads those bytes, so for everything else the
image is the *literal* `raw`, and `image_slice` says so. That makes the
`decode` side conditions of `step_of_loaded` facts about a slice of a numeral
list, not of a term depending on the layout.

**Decode facts come from the transcription.** Each `*_decode_*` theorem below
is `decode_raw (by decide +kernel)` (`Sha256O2/Listing.lean`): a lookup of the
instruction in the kernel-checked listing `Lifted.Sha256ClangO2.listing`, which
`tools/x86-lift` produced and `transcript_verify` checks against `Ext.decode`
once for the whole function. The decoder is no longer re-run per occurrence.
`Listing.image_decode` also gives the whole loaded image's listing at every
layout, relocated `lea` included.

**What is borrowed.** `Ext.spliceAt` and its two slice halves, `Loaded.of_stored`,
`stepOpt_push` and the `reaches_loop_of_trace` rule are all Track 2c's; this
module keeps only `stepOpt_pop` and `popWord_of_holdsLE`, which are generic in
the same way and should follow them into `Ext/Store.lean`.
-/

@[expose] public section

namespace Silmaril.Crypto.X86.Sha256O2

open Silmaril.Process (Memory Region Byte Access)
open Silmaril.X86 (Word Reg State MState sysv64)
open Silmaril.X86.Ext (Loaded Stored Reaches Runs Returns HoldsLE Instr step stepOpt
  step_of_loaded stepOpt_of_loaded step_returned_of_loaded stepOpt_push decode decode_length
  exec spliceAt)
open Silmaril.Machine.LittleEndian (encodeWords)

/-! ## The image is the literal bytes, away from the relocation -/

/-- `Image.patch32` is Track 2c's `Ext.spliceAt` at a four-byte patch: the
`disp32` field written as a list. Definitional, so the two slice lemmas below
are their lemmas with the constants filled in. -/
theorem patch32_eq_spliceAt (bytes : List Byte) (offset : Nat) (value : BitVec 32) :
    patch32 bytes offset value =
      Silmaril.X86.Ext.spliceAt bytes offset
        [value.setWidth 8, (value >>> 8).setWidth 8,
         (value >>> 16).setWidth 8, (value >>> 24).setWidth 8] := rfl

/-- The image as a splice of `raw`. -/
theorem image_eq_spliceAt (textBase rodataBase : Word) :
    image textBase rodataBase =
      Silmaril.X86.Ext.spliceAt raw relocOffset
        (let v := (rodataBase - textBase - BitVec.ofNat 64 (relocOffset + 4)).setWidth 32
         [v.setWidth 8, (v >>> 8).setWidth 8, (v >>> 16).setWidth 8, (v >>> 24).setWidth 8]) :=
  rfl

/-- A slice of the image below the relocation site is a slice of `raw`. This
is what turns the `decode` obligation of `Ext.step_of_loaded` into a closed
goal that `decide` settles. -/
theorem image_slice (textBase rodataBase : Word) {offset len : Nat}
    (below : offset + len ≤ relocOffset) :
    ((image textBase rodataBase).drop offset).take len = (raw.drop offset).take len := by
  rw [image_eq_spliceAt]
  exact Silmaril.X86.Ext.spliceAt_slice_below _ _
    (by rw [raw_length]; simp [size, relocOffset]) below

/-- A slice of the image at or above the end of the relocated field is a slice
of `raw`. The epilogue sits at function offset `0x1b9`, far above
`relocOffset = 0xb7`, so this half is needed as often as the other. -/
theorem image_slice_above (textBase rodataBase : Word) {offset len : Nat}
    (above : relocOffset + 4 ≤ offset) :
    ((image textBase rodataBase).drop offset).take len = (raw.drop offset).take len := by
  rw [image_eq_spliceAt]
  exact Silmaril.X86.Ext.spliceAt_slice_above _ _
    (by rw [raw_length]; simp [size, relocOffset]) above

/-! ## Entry consequences -/

variable {L : Layout} {state block rspEntry : Word} {m : MState}

/-- The image is loaded as code, in the form `Ext.step_of_loaded` wants. -/
theorem SysVEntry.loaded (h : SysVEntry L state block rspEntry frameSize m) :
    Loaded m.memory L.textBase (image L.textBase L.rodataBase) := by
  rw [Loaded, image_length]
  exact h.code

/-- The frame floor, as a number: `rspEntry − 216 − 128`. -/
theorem frameFloor_eq (sp : Nat) : sysv64.frameFloor sp frameSize = sp - 344 := by
  show sp - frameSize - 128 = sp - 344
  simp only [frameSize]
  omega

/-- The frame extent, as a number: the 216-byte frame plus the 128-byte red
zone. Unlike `-O0`, the image uses every byte of this. -/
theorem frameExtent_eq : sysv64.frameExtent frameSize = 344 := rfl

/-- Every byte of the frame and red zone is writable. The six prologue pushes,
the `a…h` spill slots and all 64 words of `w[]` are instances. -/
theorem SysVEntry.frame_writable (h : SysVEntry L state block rspEntry frameSize m)
    {address len : Nat} (pos : 0 < len) (lower : rspEntry.toNat - 344 ≤ address)
    (upper : address + len ≤ rspEntry.toNat) :
    m.memory.Permitted .write address len := by
  have hfits := h.frameFits
  rw [frameExtent_eq] at hfits
  refine Silmaril.X86.Ext.Memory.Permitted.sub h.frameMapped.2 pos ?_ ?_
  · rw [frameFloor_eq]; omega
  · rw [frameFloor_eq, frameExtent_eq]; omega

/-- Every byte of the frame and red zone is readable. -/
theorem SysVEntry.frame_readable (h : SysVEntry L state block rspEntry frameSize m)
    {address len : Nat} (pos : 0 < len) (lower : rspEntry.toNat - 344 ≤ address)
    (upper : address + len ≤ rspEntry.toNat) :
    m.memory.Permitted .read address len := by
  have hfits := h.frameFits
  rw [frameExtent_eq] at hfits
  refine Silmaril.X86.Ext.Memory.Permitted.sub h.frameMapped.1 pos ?_ ?_
  · rw [frameFloor_eq]; omega
  · rw [frameFloor_eq, frameExtent_eq]; omega

/-- The frame is inside the footprint: every store the function makes is a
step of the modifies-set claim. -/
theorem frame_in_footprint (hfits : sysv64.frameExtent frameSize ≤ rspEntry.toNat)
    {address : Nat} (lower : rspEntry.toNat - 344 ≤ address) (upper : address < rspEntry.toNat) :
    Footprint state rspEntry frameSize address := by
  rw [frameExtent_eq] at hfits
  refine Or.inr ?_
  simp only [frameRegion, Region.Contains, frameFloor_eq, frameExtent_eq]
  omega


/-! ## Carrying `Loaded` across a store

Every instruction of the prologue writes to the stack, so the `Loaded`
hypothesis that `step_of_loaded` needs has to survive six stores. It does, by
Track 2c's `Ext.Loaded.of_stored`, because the code region and the frame are
disjoint — a `SysVEntry` precondition. -/

/-- The code and the callee's stack are disjoint, as `SysVEntry.disjoint`
requires of every pair. -/
theorem SysVEntry.code_disjoint_frame (h : SysVEntry L state block rspEntry frameSize m) :
    Region.Disjoint (codeRegion L) (frameRegion rspEntry frameSize) := by
  have hp := h.disjoint
  simp only [regions, List.pairwise_cons, List.mem_cons] at hp
  have := hp.2.2.1
  exact this _ (by simp)

/-- The concrete form the push steps need: a write anywhere in the frame is
disjoint from the image. -/
theorem SysVEntry.store_disjoint_code (h : SysVEntry L state block rspEntry frameSize m)
    {address len : Nat} (lower : rspEntry.toNat - 344 ≤ address)
    (upper : address + len ≤ rspEntry.toNat) :
    L.textBase.toNat + size ≤ address ∨ address + len ≤ L.textBase.toNat := by
  have hd := h.code_disjoint_frame
  have hfits := h.frameFits
  rw [frameExtent_eq] at hfits
  simp only [codeRegion, frameRegion, Region.Disjoint, frameFloor_eq, frameExtent_eq] at hd
  omega

/-! ## The prologue

Six pushes and a `sub`. `PrologueState` is the invariant carried across them:
where RIP and RSP are, that no other register has changed, that the image is
still loaded, and that everything written so far is inside the footprint.
`prologue_step` advances it by one push; `prologue_pushes` applies that six
times and `prologue` adds the `sub`. -/

/-- `state[]` and the code are disjoint. -/
theorem SysVEntry.state_disjoint_code (h : SysVEntry L state block rspEntry frameSize m) :
    Region.Disjoint (stateRegion state) (codeRegion L) := by
  have hp := h.disjoint
  simp only [regions, List.pairwise_cons, List.mem_cons] at hp
  exact hp.1 _ (by simp)

/-- `state[]` and the callee's stack are disjoint. -/
theorem SysVEntry.state_disjoint_frame (h : SysVEntry L state block rspEntry frameSize m) :
    Region.Disjoint (stateRegion state) (frameRegion rspEntry frameSize) := by
  have hp := h.disjoint
  simp only [regions, List.pairwise_cons, List.mem_cons] at hp
  exact hp.1 _ (by simp)

/-- `state[]` and `block[]` are disjoint. The caller may not alias them. -/
theorem SysVEntry.state_disjoint_block (h : SysVEntry L state block rspEntry frameSize m) :
    Region.Disjoint (stateRegion state) (blockRegion block) := by
  have hp := h.disjoint
  simp only [regions, List.pairwise_cons, List.mem_cons] at hp
  exact hp.1 _ (by simp)

/-- `block[]` and the callee's stack are disjoint, as `SysVEntry.disjoint`
requires of every pair. -/
theorem SysVEntry.block_disjoint_frame (h : SysVEntry L state block rspEntry frameSize m) :
    Region.Disjoint (blockRegion block) (frameRegion rspEntry frameSize) := by
  have hp := h.disjoint
  simp only [regions, List.pairwise_cons, List.mem_cons] at hp
  exact hp.2.1 _ (by simp)

/-- **`block[]`'s bytes survive the body.** `block[]` is disjoint from both
halves of the modifies set, so the sixty-four bytes the contract read at entry
are still there at every point inside the function.

This is what lets the pinned block word be recovered at each iteration of L1
from the footprint alone, rather than carried as an extra field of the
invariant. -/
theorem blockBytes_preserved (h : SysVEntry L state block rspEntry frameSize m)
    {before after : Memory} {bs : List Silmaril.Process.Byte}
    (hw : Memory.WritesWithin before after (Footprint state rspEntry frameSize))
    (hr : before.readBytes block.toNat 64 = some bs) :
    after.readBytes block.toNat 64 = some bs := by
  have hfits := h.frameFits
  rw [frameExtent_eq] at hfits
  have hsb := h.state_disjoint_block
  have hbf := h.block_disjoint_frame
  simp only [stateRegion, blockRegion, Region.Disjoint] at hsb
  simp only [blockRegion, frameRegion, Region.Disjoint, frameFloor_eq, frameExtent_eq] at hbf
  rw [Silmaril.Process.Memory.WritesWithin.readBytes hw ?_]
  · exact hr
  · intro o ho
    rintro (⟨hl, hrr⟩ | ⟨hl, hrr⟩)
    · simp only [stateRegion] at hl hrr; omega
    · simp only [frameRegion, frameFloor_eq, frameExtent_eq] at hl hrr; omega

set_option maxRecDepth 8000 in

/-- The eight-byte little-endian slot bytes are what a `push` writes. -/
theorem leBytes_eight_eq_encodeWords (v : Word) :
    Silmaril.X86.Ext.leBytes v 8 = encodeWords [v] := by
  rw [Silmaril.X86.encodeWords_singleton]
  simp [Silmaril.X86.Ext.leBytes, List.ofFn_succ]

/-- The six callee-saved registers in push order: `savedReg i` was pushed at
`rspEntry − 8 * (i + 1)`. The pops run through this backwards. -/
def savedReg : Nat → Reg
  | 0 => .rbp
  | 1 => .r15
  | 2 => .r14
  | 3 => .r13
  | 4 => .r12
  | _ => .rbx

/-- None of them is the stack pointer. -/
theorem savedReg_ne_rsp : ∀ i, i < 6 → savedReg i ≠ Reg.rsp := by decide

/-- **Byte `i` of the little-endian word at `4 * t`.** The bridge from the
spec's `leWordAt`, which is an `|||` of shifted bytes, to the byte list a
memory read actually returns. Proved the same way as `byteSwap32_leWordAt`:
bit extensionality, a case on which lane `i` names, and the fact that a
`Byte` has no bits at index eight or above. -/
theorem wordByte_leWordAt (bs : List Silmaril.Process.Byte) (t i : Nat) (hi : i < 4) :
    Silmaril.Machine.LittleEndian.wordByte ((leWordAt bs t).setWidth 64) i
      = byteAt bs (4 * t + i) := by
  have hge : ∀ (b : Silmaril.Process.Byte) (k : Nat), 8 ≤ k → b.getLsbD k = false :=
    fun b k hk => BitVec.getLsbD_of_ge b k hk
  have hcase : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro j
  simp only [Silmaril.Machine.LittleEndian.wordByte, leWordAt,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  rcases hcase with rfl | rfl | rfl | rfl <;> intro hj
  · simp only [show 8 * 0 + j = j by omega, show 4 * t + 0 = 4 * t by omega,
      decide_eq_true (by omega : j < 8), decide_eq_true (by omega : j < 64),
      decide_eq_true (by omega : j < 32), decide_eq_true (by omega : j < 16),
      decide_eq_true (by omega : j < 24),
      Bool.and_false, Bool.false_and, Bool.or_false,
      Bool.true_and, Bool.not_true]
  · simp only [show 8 * 1 + j = 8 + j by omega, show 8 + j - 8 = j by omega,
      decide_eq_true (by omega : j < 8), decide_eq_true (by omega : 8 + j < 64),
      decide_eq_true (by omega : 8 + j < 32), decide_eq_false (by omega : ¬(8 + j < 8)),
      decide_eq_true (by omega : 8 + j < 16), decide_eq_true (by omega : 8 + j < 24),
      decide_eq_true (by omega : j < 32),
      hge (byteAt bs (4 * t)) (8 + j) (by omega),
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.not_true, Bool.not_false]
  · simp only [show 8 * 2 + j = 16 + j by omega, show 16 + j - 16 = j by omega,
      show 16 + j - 8 = 8 + j by omega,
      decide_eq_true (by omega : j < 8), decide_eq_true (by omega : 16 + j < 64),
      decide_eq_true (by omega : 16 + j < 32), decide_eq_false (by omega : ¬(16 + j < 8)),
      decide_eq_false (by omega : ¬(16 + j < 16)), decide_eq_true (by omega : 16 + j < 24),
      decide_eq_true (by omega : j < 32),
      hge (byteAt bs (4 * t)) (16 + j) (by omega),
      hge (byteAt bs (4 * t + 1)) (8 + j) (by omega),
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.not_true, Bool.not_false]
  · simp only [show 8 * 3 + j = 24 + j by omega, show 24 + j - 24 = j by omega,
      show 24 + j - 16 = 8 + j by omega, show 24 + j - 8 = 16 + j by omega,
      decide_eq_true (by omega : j < 8), decide_eq_true (by omega : 24 + j < 64),
      decide_eq_true (by omega : 24 + j < 32), decide_eq_false (by omega : ¬(24 + j < 8)),
      decide_eq_false (by omega : ¬(24 + j < 16)), decide_eq_false (by omega : ¬(24 + j < 24)),
      decide_eq_true (by omega : j < 32),
      hge (byteAt bs (4 * t)) (24 + j) (by omega),
      hge (byteAt bs (4 * t + 1)) (16 + j) (by omega),
      hge (byteAt bs (4 * t + 2)) (8 + j) (by omega),
      Bool.and_false, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.not_false]

/-- **A four-byte sub-range of a byte list, spelled out.** The contract hands
over `block[]` as one 64-byte read; every load is four bytes at `block + 4t`.
This is the list half of closing that gap, `Memory.readBytes_sub_range` being
the memory half. -/
theorem take_drop_four (bs : List Silmaril.Process.Byte) (n : Nat) (h : n + 4 ≤ bs.length) :
    (bs.drop n).take 4
      = [byteAt bs n, byteAt bs (n + 1), byteAt bs (n + 2), byteAt bs (n + 3)] := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_drop, byteAt, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge k 4 with hk | hk
  · have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;>
      simp [List.getElem?_eq_getElem (show n < bs.length by omega),
        List.getElem?_eq_getElem (show n + 1 < bs.length by omega),
        List.getElem?_eq_getElem (show n + 2 < bs.length by omega),
        List.getElem?_eq_getElem (show n + 3 < bs.length by omega)]
  · have hnk : ¬(k < 4) := by omega
    rw [show (if k < 4 then bs[n + k]? else none) = none from by simp [hnk]]
    exact (List.getElem?_eq_none (by simp; omega)).symm

/-- **The block word at `t` is in memory, little-endian.** The four bytes at
`block + 4 * t` are the low four bytes of `leWordAt bs t`, so a `uint32` load
there yields exactly the spec's little-endian word — which `bswap` then turns
into `beWordAt`, by `byteSwap32_leWordAt`.

Together those two are the whole value story of L1. Note that this needs
`Memory.readBytes_sub_range`'s `offset < length` hypothesis rather than the
`0 < len` one might first write: at `len = 0` with `address + offset` at the
address limit the naive statement is false, because `checkSpan`'s
`address < addressLimit` is strict. -/
theorem holdsLE_leWord {memory : Memory} {base len : Nat}
    {bs : List Silmaril.Process.Byte}
    (read : memory.readBytes base len = some bs) {t : Nat} (ht : 4 * t + 4 ≤ len) :
    Silmaril.X86.Ext.HoldsLE memory (base + 4 * t) 4 ((leWordAt bs t).setWidth 64) := by
  have hlen : bs.length = len := Silmaril.Process.Memory.readWith_length read
  show memory.readBytes (base + 4 * t) 4
      = some (Silmaril.X86.Ext.leBytes ((leWordAt bs t).setWidth 64) 4)
  rw [Silmaril.Process.Memory.readBytes_sub_range read (by omega) (by omega),
    take_drop_four bs (4 * t) (by omega)]
  simp only [Silmaril.X86.Ext.leBytes, List.ofFn_succ, List.ofFn_zero,
    Fin.val_zero, Fin.val_succ, Nat.zero_add,
    wordByte_leWordAt bs t 0 (by omega), wordByte_leWordAt bs t 1 (by omega),
    wordByte_leWordAt bs t 2 (by omega), wordByte_leWordAt bs t 3 (by omega),
    Nat.add_zero]

/-- The block word at `t`, at `block[]`'s fixed length. -/
theorem holdsLE_blockWord {memory : Memory} {base : Nat}
    {bs : List Silmaril.Process.Byte}
    (read : memory.readBytes base 64 = some bs) {t : Nat} (ht : t < 16) :
    Silmaril.X86.Ext.HoldsLE memory (base + 4 * t) 4 ((leWordAt bs t).setWidth 64) :=
  holdsLE_leWord read (by omega)

/-- **`K[t]` by value, free from the contract.** `SysVEntry.kTable` pins the
`.rodata` *contents*, not merely its backing, so the constant the round needs
is already known — no `readBytes → HoldsLE` bridge and no obligation on the
caller. This is the second time that choice has paid; see the module doc on
capability versus fact. -/
theorem holdsLE_kWord (h : SysVEntry L state block rspEntry frameSize m)
    {t : Nat} (ht : 4 * t + 4 ≤ 256) :
    Silmaril.X86.Ext.HoldsLE m.memory (L.rodataBase.toNat + 4 * t) 4
      ((leWordAt kBytes t).setWidth 64) :=
  holdsLE_leWord h.kTable ht

set_option maxRecDepth 40000 in
/-- **`K[t]` as the specification names it.** The indexed form of
`kBytes_eq_spec`: the object's table entry `t` is `Ks.getD t 0`. Machine
checked against the ingested bytes, so the link from `.rodata` to FIPS is a
computation, not an assumption. -/
theorem leWordAt_kBytes : ∀ t, t < 64 → leWordAt kBytes t = SHA256.Kernel.Ks.getD t 0 := by
  decide

/-- A four-byte slot holds only the low thirty-two bits, so widening a 32-bit
word into a slot and reading it back at 32 bits is the identity. This is the
round trip every `K[t]` and `w[t]` makes between the specification's `Word` and
the machine's slot. -/
theorem trunc32 (v : SHA256.Kernel.Word) :
    (BitVec.ofNat 64 ((v.setWidth 64).toNat % 2 ^ (8 * 4))).setWidth 32 = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `trunc32` at the width the machine actually writes. The two differ only in
how the width is spelled — `Sz.d.bits` against the literal `32` — but `simp`
matches syntactically, so the shape the step lemmas produce needs its own name.
This is the same boundary `read32` crosses, met once more at the slot. -/
theorem trunc32' (v : SHA256.Kernel.Word) :
    (BitVec.ofNat 64 ((v.setWidth 64).toNat % 2 ^ (8 * 4))).setWidth
      Silmaril.X86.Ext.Sz.d.bits = v :=
  trunc32 v

/-- **Reassembling a word from the four bytes a slot stores.** The inverse of
`wordByte`, and what turns the feed-forward's eight slot facts back into the
specification's eight words. -/
theorem leWord_of_wordBytes (v : SHA256.Kernel.Word) :
    ((Silmaril.Machine.LittleEndian.wordByte (v.setWidth 64) 0).setWidth 32 |||
      ((Silmaril.Machine.LittleEndian.wordByte (v.setWidth 64) 1).setWidth 32 <<< 8) |||
      ((Silmaril.Machine.LittleEndian.wordByte (v.setWidth 64) 2).setWidth 32 <<< 16) |||
      ((Silmaril.Machine.LittleEndian.wordByte (v.setWidth 64) 3).setWidth 32 <<< 24)) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [Silmaril.Machine.LittleEndian.wordByte, BitVec.getLsbD_or,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  intro hi
  rcases Nat.lt_or_ge i 8 with h | h
  · simp only [decide_eq_true (by omega : i < 32), decide_eq_true (by omega : i < 8), decide_eq_true (by omega : i < 16), decide_eq_true (by omega : i < 24), decide_eq_true (by omega : i < 64), show 8 * 0 + i = i by omega,
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.true_and, Bool.not_true]
  · rcases Nat.lt_or_ge i 16 with h2 | h2
    · simp only [decide_eq_true (by omega : i < 32), decide_eq_true (by omega : i < 64), decide_eq_true (by omega : i - 8 < 8), decide_eq_true (by omega : i < 16), decide_eq_true (by omega : i < 24), decide_eq_true (by omega : i - 8 < 32), decide_eq_false (by omega : ¬(i < 8)), show 8 * 1 + (i - 8) = i by omega,
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.not_true, Bool.not_false]
    · rcases Nat.lt_or_ge i 24 with h3 | h3
      · simp only [decide_eq_true (by omega : i < 32), decide_eq_true (by omega : i < 64), decide_eq_true (by omega : i - 16 < 8), decide_eq_true (by omega : i < 24), decide_eq_true (by omega : i - 16 < 32), decide_eq_true (by omega : i - 8 < 32), decide_eq_false (by omega : ¬(i < 8)), decide_eq_false (by omega : ¬(i < 16)), decide_eq_false (by omega : ¬(i - 8 < 8)), show 8 * 2 + (i - 16) = i by omega,
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.not_true, Bool.not_false]
      · simp only [decide_eq_true (by omega : i < 32), decide_eq_true (by omega : i < 64), decide_eq_true (by omega : i - 24 < 8), decide_eq_true (by omega : i - 24 < 32), decide_eq_true (by omega : i - 16 < 32), decide_eq_true (by omega : i - 8 < 32), decide_eq_false (by omega : ¬(i < 8)), decide_eq_false (by omega : ¬(i < 16)), decide_eq_false (by omega : ¬(i < 24)), decide_eq_false (by omega : ¬(i - 8 < 8)), decide_eq_false (by omega : ¬(i - 16 < 8)), show 8 * 3 + (i - 24) = i by omega,
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.not_false]

/-- **The feed-forward's write-back, widened.** Eight four-byte slot facts
become the single thirty-two-byte read `StateHolds` names. -/
theorem stateHolds_of_words {memory : Silmaril.Process.Memory} {st : Silmaril.X86.Word}
    {w : Nat → SHA256.Kernel.Word}
    (hw : ∀ j, j < 8 → Silmaril.X86.Ext.HoldsLE memory (st.toNat + 4 * j) 4
      ((w j).setWidth 64)) :
    StateHolds memory st ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩ := by
  refine ⟨(List.range 8).flatMap (fun i => Silmaril.X86.Ext.leBytes ((w i).setWidth 64) 4),
    ?_, ?_⟩
  · have hr := Silmaril.Process.Memory.readBytes_run (memory := memory) (width := 4) 7 st.toNat
      (fun i => Silmaril.X86.Ext.leBytes ((w i).setWidth 64) 4) (fun i hi => hw i (by omega))
    simpa using hr
  · simp [show List.range 8 = [0,1,2,3,4,5,6,7] from rfl, stateOf, leWordAt, byteAt,
      Silmaril.X86.Ext.leBytes, List.ofFn_succ, leWord_of_wordBytes]


/-- The state partway through the prologue: `k` bytes pushed, sitting at
function offset `off`. -/
structure PrologueState (L : Layout) (state block rspEntry : Word) (entry : MState)
    (sv : Nat → SHA256.Kernel.Word) (k off : Nat) (mid : MState) : Prop where
  /-- RIP is at function offset `off`. -/
  rip : mid.core.rip = L.textBase + BitVec.ofNat 64 off
  /-- `k` bytes have been pushed. -/
  rsp : mid.core.read .rsp = rspEntry - BitVec.ofNat 64 k
  /-- Nothing but `%rsp` has been written. -/
  regs : ∀ r, r ≠ Reg.rsp → mid.core.read r = entry.core.read r
  /-- The image is still loaded: the pushes are disjoint from the code. -/
  loaded : Loaded mid.memory L.textBase (image L.textBase L.rodataBase)
  /-- Everything written so far is inside the modifies set. -/
  frame : Memory.WritesWithin entry.memory mid.memory (Footprint state rspEntry frameSize)
  /-- `state[]` still reads: the pushes go to the frame, which is disjoint.
  Written out rather than via `StateWordsHold`, which is declared later. -/
  stwords : ∀ j, j < 8 →
    Silmaril.X86.Ext.HoldsLE mid.memory (state.toNat + 4 * j) 4 ((sv j).setWidth 64)
  /-- `block[]` still reads, for the same reason. -/
  blwords : ∀ j, j < 16 →
    ∃ v : Word, Silmaril.X86.Ext.HoldsLE mid.memory (block.toNat + 4 * j) 4 v
  /-- The slots the pushes have written so far hold **the entry values of the
  registers they saved**. At `k = 48` that is all six, which is what the
  epilogue needs to re-establish `sysv64.Preserved`.

  This is the *pinned* instantiation of the slot rule. Liveness alone needs
  only the existential form — some eight bytes are there, so the `pop` cannot
  fault — and that is what `SavedSlotsHold` says. `Post.saved` needs to know
  *which* bytes, so it is the same rule read at a particular assignment of
  values. Nothing between here and the epilogue reads these slots, so only
  this field carries them. -/
  pushed : ∀ j, j < 6 → 8 * (j + 1) ≤ k →
    Silmaril.X86.Ext.HoldsLE mid.memory (rspEntry.toNat - 8 * (j + 1)) 8
      (entry.core.read (savedReg j))
  /-- The return address is untouched: it is outside the footprint. -/
  retAddr : Silmaril.X86.Ext.HoldsLE mid.memory rspEntry.toNat 8 L.exit
  /-- Pushes move `%rsp` in multiples of eight, which is what makes `pushed`
  a prefix rather than an arbitrary set. -/
  kmul : k % 8 = 0

/-- At entry, nothing has been pushed and nothing has been written. -/
theorem prologueState_entry (h : SysVEntry L state block rspEntry frameSize m)
    {sb : List Silmaril.Process.Byte} (hsb : m.memory.readBytes state.toNat 32 = some sb) :
    PrologueState L state block rspEntry m (fun j => leWordAt sb j) 0 0 m where
  rip := by rw [h.rip]; simp
  rsp := by rw [h.rsp]; simp
  regs := fun _ _ => rfl
  loaded := h.loaded
  frame := Memory.WritesWithin.refl _ _
  stwords := fun j hj => holdsLE_leWord hsb (by omega)
  blwords := fun j hj => by
    obtain ⟨bytes, hb⟩ := h.blockReads
    exact ⟨_, Silmaril.X86.Ext.holdsLE_of_readBytes
      (Silmaril.X86.Ext.readWith_sub (access := .read) hb (offset := 4 * j) (len := 4)
        (by omega) (by omega)) (by omega)⟩
  pushed := fun _ _ hk => absurd hk (by omega)
  retAddr := h.returnAddress
  kmul := rfl

/-- One prologue push. The bound `k + 8 ≤ 48` keeps the write inside the six
push slots, which is what makes it both permitted and inside the footprint. -/
theorem prologue_step (h : SysVEntry L state block rspEntry frameSize m)
    {sv : Nat → SHA256.Kernel.Word} {k off len : Nat} {r : Reg} {mid : MState}
    (hs : PrologueState L state block rspEntry m sv k off mid)
    (hk : k + 8 ≤ 48) (hbelow : off + len ≤ relocOffset)
    (hdec : decode ((raw.drop off).take len) = some (.push r, len))
    (hreg : savedReg (k / 8) = r) :
    ∃ mid', stepOpt L.exit mid = some mid' ∧
      PrologueState L state block rspEntry m sv (k + 8) (off + len) mid' := by
  have hfits := h.frameFits
  rw [frameExtent_eq] at hfits
  -- the new stack pointer, as a value and as a number
  have hsp : mid.core.read .rsp - 8#64 = rspEntry - BitVec.ofNat 64 (k + 8) := by
    rw [hs.rsp, sub_sub, Silmaril.X86.Ext.ofNat_add_ofNat]
  have hspNat : (mid.core.read .rsp - 8#64).toNat = rspEntry.toNat - (k + 8) := by
    rw [hsp]
    exact Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := k + 8) (by omega) (by omega)
  have hlow : rspEntry.toNat - 344 ≤ rspEntry.toNat - (k + 8) := by omega
  have hhigh : rspEntry.toNat - (k + 8) + 8 ≤ rspEntry.toNat := by omega
  -- the write is permitted, transported from the entry memory
  have hperm : mid.memory.Permitted .write (mid.core.read .rsp - 8#64).toNat 8 := by
    rw [hspNat, Silmaril.Process.Memory.WritesWithin.permitted_iff hs.frame]
    exact h.frame_writable (by omega) hlow hhigh
  have hsize : off + len ≤ size := by
    simp only [relocOffset] at hbelow; simp only [size]; omega
  obtain ⟨after, hstep, hstored⟩ :=
    stepOpt_push (exit := L.exit) hs.loaded hs.rip (by rw [image_length]; exact hsize)
      (by rw [image_slice _ _ hbelow]; exact hdec) hperm
  obtain ⟨hrip, hregs, _hflags, hstored⟩ := hstored
  refine ⟨_, hstep, ?_⟩
  have hbytes : (encodeWords [mid.core.read r]).length = 8 :=
    Silmaril.X86.length_encodeWords_singleton _
  refine {
    rip := hrip
    rsp := by rw [hregs.target]; exact hsp
    regs := fun q hq => by rw [hregs.other q hq]; exact hs.regs q hq
    loaded := Silmaril.X86.Ext.Loaded.of_stored hs.loaded hstored
      (by rw [image_length, hbytes, hspNat]; exact h.store_disjoint_code hlow hhigh)
    stwords := fun j hj => by
      refine Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hstored (hs.stwords j hj) ?_
      rw [hbytes, hspNat]
      have hd := h.state_disjoint_frame
      simp only [stateRegion, frameRegion, Region.Disjoint, frameFloor_eq,
        frameExtent_eq] at hd
      omega
    blwords := fun j hj => by
      obtain ⟨v, hv⟩ := hs.blwords j hj
      refine ⟨v, Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hstored hv ?_⟩
      rw [hbytes, hspNat]
      have hd := h.block_disjoint_frame
      simp only [blockRegion, frameRegion, Region.Disjoint, frameFloor_eq,
        frameExtent_eq] at hd
      omega
    kmul := by have := hs.kmul; omega
    pushed := fun j hj hk8 => by
      have hkm := hs.kmul
      have hcase : 8 * (j + 1) ≤ k ∨ 8 * (j + 1) = k + 8 := by omega
      rcases hcase with hle | heq
      · exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hstored (hs.pushed j hj hle)
          (by rw [hbytes, hspNat]; omega)
      · -- this push is the one that fills slot `j`, so `r` is `savedReg j`
        have hjr : savedReg j = r := by rw [show j = k / 8 by omega]; exact hreg
        have hrv : mid.core.read r = m.core.read (savedReg j) := by
          rw [hjr]; exact hs.regs r (hjr ▸ savedReg_ne_rsp j hj)
        rw [heq, ← hrv]
        have hst2 : Stored mid.memory after.memory (rspEntry.toNat - (k + 8))
            (Silmaril.X86.Ext.leBytes (mid.core.read r) 8) := by
          rw [leBytes_eight_eq_encodeWords, ← hspNat]
          exact hstored
        refine Silmaril.X86.Ext.HoldsLE.of_stored_self hst2 ?_
        rw [Silmaril.Process.Memory.WritesWithin.permitted_iff hs.frame]
        exact h.frame_readable (by omega) (by omega) (by omega)
    retAddr := by
      refine Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hstored hs.retAddr ?_
      rw [hbytes, hspNat]
      omega
    frame := Silmaril.Process.Memory.WritesWithin.step hs.frame hstored ?_ }
  intro offset hoff
  rw [hbytes] at hoff
  rw [hspNat]
  exact frame_in_footprint (by rw [frameExtent_eq]; omega) (by omega) (by omega)

/-- **The six callee-saved pushes.** From the entry state the machine retires
`push %rbp; push %r15; push %r14; push %r13; push %r12; push %rbx`, arriving at
function offset `0x0a` with `%rsp = rspEntry − 48`, every other register
untouched, the image still loaded, and everything written inside the
footprint. -/
theorem prologue_pushes (h : SysVEntry L state block rspEntry frameSize m)
    {sb : List Silmaril.Process.Byte} (hsb : m.memory.readBytes state.toNat 32 = some sb) :
    ∃ mid, Reaches L.exit m mid ∧
      PrologueState L state block rspEntry m (fun j => leWordAt sb j) 48 10 mid := by
  obtain ⟨m1, s1, p1⟩ :=
    prologue_step (r := .rbp) (len := 1) h (prologueState_entry h hsb) (by omega)
      (by decide) (by decide) (by decide)
  obtain ⟨m2, s2, p2⟩ :=
    prologue_step (r := .r15) (len := 2) h p1 (by omega) (by decide) (by decide) (by decide)
  obtain ⟨m3, s3, p3⟩ :=
    prologue_step (r := .r14) (len := 2) h p2 (by omega) (by decide) (by decide) (by decide)
  obtain ⟨m4, s4, p4⟩ :=
    prologue_step (r := .r13) (len := 2) h p3 (by omega) (by decide) (by decide) (by decide)
  obtain ⟨m5, s5, p5⟩ :=
    prologue_step (r := .r12) (len := 2) h p4 (by omega) (by decide) (by decide) (by decide)
  obtain ⟨m6, s6, p6⟩ :=
    prologue_step (r := .rbx) (len := 1) h p5 (by omega) (by decide) (by decide) (by decide)
  exact ⟨m6, Reaches.cons s1 (Reaches.cons s2 (Reaches.cons s3
    (Reaches.cons s4 (Reaches.cons s5 (Reaches.one s6))))), p6⟩

/-- **`0x0a: 48 81 ec a8 00 00 00` — `sub $0xa8,%rsp`.** The frame is opened.
The destination is a register, so no memory is read or written and no
permission is needed; only `%rsp` and the flags change, and the flags are not
part of `PrologueState`.

Note this lemma does **not** take a `SysVEntry`: a register-destination ALU
op needs no permission and no disjointness, so the frame hypotheses are not
used. -/
theorem prologue_sub {sv : Nat → SHA256.Kernel.Word} {mid : MState}
    (hs : PrologueState L state block rspEntry m sv 48 10 mid) :
    ∃ mid', stepOpt L.exit mid = some mid' ∧
      PrologueState L state block rspEntry m sv 216 17 mid' := by
  have hdec : decode ((raw.drop 10).take 7)
      = some (.aluI .q .sub (.reg .rsp) 0x000000a8#32, 7) := decode_raw (by decide +kernel)
  refine ⟨_, stepOpt_of_loaded (offset := 10) (len := 7)
    (instr := .aluI .q .sub (.reg .rsp) 0x000000a8#32)
    hs.loaded hs.rip (by rw [image_length]; decide)
    (by rw [image_slice _ _ (by decide : 10 + 7 ≤ relocOffset)]; exact hdec)
    (by simp) rfl, ?_⟩
  have hilen : (Instr.aluI Silmaril.X86.Ext.Sz.q Silmaril.X86.AluOp.sub
      (Silmaril.X86.Ext.RM.reg Reg.rsp) 0x000000a8#32).length = 7 :=
    ((decode_length hdec).1).symm
  have himm : ((0x000000a8#32 : BitVec 32).signExtend 64) = 168#64 := by decide
  refine { rip := ?_, rsp := ?_, regs := ?_, loaded := hs.loaded, frame := hs.frame, stwords := hs.stwords, blwords := hs.blwords, pushed := fun j hj _ => hs.pushed j hj (by omega), retAddr := hs.retAddr, kmul := by have := hs.kmul; omega }
  · show mid.core.rip + BitVec.ofNat 64 _ = _
    rw [hilen, hs.rip, add_assoc, Silmaril.X86.Ext.ofNat_add_ofNat]
  · show mid.core.read Reg.rsp - (0x000000a8#32 : BitVec 32).signExtend 64
        = rspEntry - BitVec.ofNat 64 216
    rw [himm, hs.rsp, sub_sub, Silmaril.X86.Ext.ofNat_add_ofNat]
  · intro q hq
    show (Silmaril.X86.Ext.Sz.q.write mid.core Reg.rsp _).read q = _
    rw [Silmaril.X86.Ext.Sz.read_write_other _ _ _ _ _ hq]
    exact hs.regs q hq

/-- **The whole prologue.** Six pushes and the `sub`: from the entry state the
machine reaches function offset `0x11` with `%rsp = rspEntry − 216`, which is
`rspEntry − frameSize`. -/
theorem prologue (h : SysVEntry L state block rspEntry frameSize m)
    {sb : List Silmaril.Process.Byte} (hsb : m.memory.readBytes state.toNat 32 = some sb) :
    ∃ mid, Reaches L.exit m mid ∧
      PrologueState L state block rspEntry m (fun j => leWordAt sb j) frameSize 17 mid := by
  obtain ⟨mid, hreach, hstate⟩ := prologue_pushes h hsb
  obtain ⟨mid', hstep, hstate'⟩ := prologue_sub hstate
  exact ⟨mid', hreach.trans (Reaches.one hstep), by simpa [frameSize] using hstate'⟩

/-! ## One `pop`, and the `ret`

The epilogue is `add $0xa8,%rsp`, six pops and `ret`. As with the pushes, the
six pops differ only in offset, length and register, so the step is proved
once. A `pop` reads a slot and leaves memory alone, so what it needs is a
`HoldsLE` fact rather than a write permission.

**Note for Track 2c.** `leBytes_eight_eq_encodeWords`, `popWord_of_holdsLE`
and `stepOpt_pop` are generic in exactly the way `Ext.stepOpt_push` is, and are
the last things here that belong beside it rather than in this file. -/

/-- A `pop` from a slot that holds `v` yields `v`. -/
theorem popWord_of_holdsLE {s : State} {memory : Memory} {v : Word}
    (h : HoldsLE memory (s.read .rsp).toNat 8 v) :
    Silmaril.X86.popWord s memory = some (v, s.write .rsp (s.read .rsp + 8#64)) := by
  rw [Silmaril.X86.popWord]
  rw [show memory.readBytes (s.read .rsp).toNat 8 = some (Silmaril.X86.Ext.leBytes v 8) from h]
  rw [leBytes_eight_eq_encodeWords]
  simp

/-- A `pop r` from a loaded image, when the slot at `%rsp` holds `v`. Memory is
unchanged. -/
theorem stepOpt_pop {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {r : Reg} {v : Word}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.pop r, len))
    (slot : HoldsLE mm.memory (mm.core.read .rsp).toNat 8 v) :
    stepOpt exit mm =
      some ⟨{ (mm.core.write .rsp (mm.core.read .rsp + 8#64)).write r v
                with rip := base + BitVec.ofNat 64 (offset + len) },
            mm.memory⟩ := by
  have hlen : (Instr.pop r).length = len := ((decode_length decoded).1).symm
  refine stepOpt_of_loaded loaded at_offset fits decoded (by simp) ?_
  simp only [exec, hlen, popWord_of_holdsLE slot, Option.map_some,
    Silmaril.X86.Ext.retire, at_offset]
  rw [add_assoc, Silmaril.X86.Ext.ofNat_add_ofNat]

/-! ## The epilogue

`add $0xa8,%rsp`, six pops and `ret`. This is where `Post.rsp` and
`Post.saved` come from, and it needs none of the mathematics of SHA-256: only
that the six slots the prologue wrote are still intact when control arrives at
`0x1b9`. That hypothesis is `EpilogueState.slots`, and establishing it is the
body's job, not the epilogue's. -/


/-- Subtracting `k` from the stack pointer and adding eight back. -/
theorem sub_add_eight (x : Word) {k : Nat} (hk : 8 ≤ k) :
    x - BitVec.ofNat 64 k + 8#64 = x - BitVec.ofNat 64 (k - 8) := by
  have h : BitVec.ofNat 64 (k - 8) + 8#64 = BitVec.ofNat 64 k := by
    rw [show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, Silmaril.X86.Ext.ofNat_add_ofNat]
    congr 1
    omega
  rw [← h, sub_add_eq_sub_sub]
  simp

/-- Control has reached the epilogue at function offset `0x1b9`, with the six
callee-saved slots and the return address intact. -/
structure EpilogueState (L : Layout) (state rspEntry : Word) (entry mid : MState) : Prop where
  /-- At `add $0xa8,%rsp`. -/
  rip : mid.core.rip = L.textBase + BitVec.ofNat 64 441
  /-- The frame is still open. -/
  rsp : mid.core.read .rsp = rspEntry - BitVec.ofNat 64 216
  /-- The six slots the prologue wrote still hold the entry values. The body
  never writes above `rspEntry − 56`, so this survives it. -/
  slots : ∀ i, i < 6 →
    HoldsLE mid.memory (rspEntry.toNat - 8 * (i + 1)) 8 (entry.core.read (savedReg i))
  /-- The return address is still at `[rspEntry]`, outside the footprint. -/
  retAddr : HoldsLE mid.memory rspEntry.toNat 8 L.exit
  /-- The image is still loaded. -/
  loaded : Loaded mid.memory L.textBase (image L.textBase L.rodataBase)

/-- One epilogue `pop`, with the stack arithmetic packaged. -/
theorem epilogue_pop {mid : MState} {off len k : Nat} {r : Reg} {v : Word}
    (loaded : Loaded mid.memory L.textBase (image L.textBase L.rodataBase))
    (at_offset : mid.core.rip = L.textBase + BitVec.ofNat 64 off)
    (hrsp : mid.core.read .rsp = rspEntry - BitVec.ofNat 64 k)
    (hk : 8 ≤ k) (hfits : k ≤ rspEntry.toNat)
    (hslot : HoldsLE mid.memory (rspEntry.toNat - k) 8 v)
    (habove : relocOffset + 4 ≤ off) (hsize : off + len ≤ size)
    (hdec : decode ((raw.drop off).take len) = some (.pop r, len)) :
    stepOpt L.exit mid =
      some ⟨{ (mid.core.write .rsp (rspEntry - BitVec.ofNat 64 (k - 8))).write r v
                with rip := L.textBase + BitVec.ofNat 64 (off + len) }, mid.memory⟩ := by
  have hrspNat : (mid.core.read .rsp).toNat = rspEntry.toNat - k := by
    rw [hrsp]
    exact Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := k) hfits (by omega)
  have := stepOpt_pop (exit := L.exit) loaded at_offset
    (by rw [image_length]; exact hsize)
    (by rw [image_slice_above _ _ habove]; exact hdec)
    (v := v) (by rw [hrspNat]; exact hslot)
  rw [this, hrsp, sub_add_eight _ hk]

/-- The six saved registers are distinct, so popping one does not disturb
another. -/
theorem savedReg_ne : ∀ i, i < 6 → ∀ j, j < 6 → i ≠ j → savedReg i ≠ savedReg j := by decide

/-- Partway through the pops: at function offset `off` with `%rsp = rspEntry −
k`. Memory is untouched by the epilogue, and every saved register whose slot
lies at or above `rspEntry − k` has been restored. -/
structure PopState (L : Layout) (rspEntry : Word) (entry mid cur : MState)
    (off k : Nat) : Prop where
  /-- RIP is at function offset `off`. -/
  rip : cur.core.rip = L.textBase + BitVec.ofNat 64 off
  /-- `%rsp` has risen to `rspEntry − k`. -/
  rsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 k
  /-- The epilogue writes no memory. -/
  mem : cur.memory = mid.memory
  /-- Every register already popped holds its entry value. -/
  popped : ∀ i, i < 6 → 8 * (i + 1) > k →
    cur.core.read (savedReg i) = entry.core.read (savedReg i)

/-- One epilogue `pop`, advancing `PopState`. -/
theorem pop_step (h : SysVEntry L state block rspEntry frameSize m)
    {mid cur : MState} (hs : EpilogueState L state rspEntry m mid)
    {off len k i : Nat} (hp : PopState L rspEntry m mid cur off k)
    (hi : i < 6) (hik : 8 * (i + 1) = k)
    (habove : relocOffset + 4 ≤ off) (hsize : off + len ≤ size)
    (hdec : decode ((raw.drop off).take len) = some (.pop (savedReg i), len)) :
    ∃ cur', stepOpt L.exit cur = some cur' ∧
      PopState L rspEntry m mid cur' (off + len) (k - 8) := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hslot : HoldsLE cur.memory (rspEntry.toNat - k) 8 (m.core.read (savedReg i)) := by
    rw [hp.mem, ← hik]; exact hs.slots i hi
  refine ⟨_, epilogue_pop (hp.mem ▸ hs.loaded) hp.rip hp.rsp (by omega) (by omega)
    hslot habove hsize hdec, ?_⟩
  refine { rip := rfl, rsp := ?_, mem := hp.mem, popped := ?_ }
  · show ((cur.core.write Reg.rsp (rspEntry - BitVec.ofNat 64 (k - 8))).write
        (savedReg i) (m.core.read (savedReg i))).read Reg.rsp = _
    rw [Silmaril.X86.State.read_write_other _ _ _ _ (Ne.symm (savedReg_ne_rsp i hi)),
      Silmaril.X86.State.read_write_same]
  · intro j hj hgt
    show ((cur.core.write Reg.rsp (rspEntry - BitVec.ofNat 64 (k - 8))).write
        (savedReg i) (m.core.read (savedReg i))).read (savedReg j) = _
    by_cases hij : j = i
    · subst hij
      rw [Silmaril.X86.State.read_write_same]
    · rw [Silmaril.X86.State.read_write_other _ _ _ _ (savedReg_ne j hj i hi hij),
        Silmaril.X86.State.read_write_other _ _ _ _ (savedReg_ne_rsp j hj)]
      exact hp.popped j hj (by omega)

/-- Adding back less than was subtracted. -/
theorem sub_add_ofNat (x : Word) {a b : Nat} (hb : b ≤ a) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a - b) := by
  have h : BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b = BitVec.ofNat 64 a := by
    rw [Silmaril.X86.Ext.ofNat_add_ofNat]; congr 1; omega
  rw [← h, sub_add_eq_sub_sub]
  simp

/-- **`0x1b9: 48 81 c4 a8 00 00 00` — `add $0xa8,%rsp`.** The frame is closed:
`%rsp` rises from `rspEntry − 216` to `rspEntry − 48`, the top of the six push
slots. Like the prologue's `sub`, this touches no memory. -/
theorem epilogue_add {mid : MState} (hs : EpilogueState L state rspEntry m mid) :
    ∃ cur, stepOpt L.exit mid = some cur ∧ PopState L rspEntry m mid cur 448 48 := by
  have hdec : decode ((raw.drop 441).take 7)
      = some (.aluI .q .add (.reg .rsp) 0x000000a8#32, 7) := decode_raw (by decide +kernel)
  have himm : ((0x000000a8#32 : BitVec 32).signExtend 64) = BitVec.ofNat 64 168 := by decide
  refine ⟨_, stepOpt_of_loaded (offset := 441) (len := 7)
    (instr := .aluI .q .add (.reg .rsp) 0x000000a8#32)
    hs.loaded hs.rip (by rw [image_length]; decide)
    (by rw [image_slice_above _ _ (by decide : relocOffset + 4 ≤ 441)]; exact hdec)
    (by simp) rfl, ?_⟩
  have hilen : (Instr.aluI Silmaril.X86.Ext.Sz.q Silmaril.X86.AluOp.add
      (Silmaril.X86.Ext.RM.reg Reg.rsp) 0x000000a8#32).length = 7 :=
    ((decode_length hdec).1).symm
  refine { rip := ?_, rsp := ?_, mem := rfl, popped := ?_ }
  · show mid.core.rip + BitVec.ofNat 64 _ = _
    rw [hilen, hs.rip, add_assoc, Silmaril.X86.Ext.ofNat_add_ofNat]
  · show mid.core.read Reg.rsp + (0x000000a8#32 : BitVec 32).signExtend 64
        = rspEntry - BitVec.ofNat 64 48
    rw [himm, hs.rsp, sub_add_ofNat _ (by omega)]
  · intro i hi hgt; omega

/-- **The six pops.** `pop %rbx; pop %r12; pop %r13; pop %r14; pop %r15;
pop %rbp`, restoring each callee-saved register from the slot the matching
prologue push wrote. -/
theorem epilogue_pops (h : SysVEntry L state block rspEntry frameSize m)
    {mid cur : MState} (hs : EpilogueState L state rspEntry m mid)
    (hp : PopState L rspEntry m mid cur 448 48) :
    ∃ cur', Reaches L.exit cur cur' ∧ PopState L rspEntry m mid cur' 458 0 := by
  obtain ⟨c1, t1, q1⟩ := pop_step (i := 5) (len := 1) h hs hp (by omega) (by omega)
    (by decide) (by decide) (by decide)
  obtain ⟨c2, t2, q2⟩ := pop_step (i := 4) (len := 2) h hs q1 (by omega) (by omega)
    (by decide) (by decide) (by decide)
  obtain ⟨c3, t3, q3⟩ := pop_step (i := 3) (len := 2) h hs q2 (by omega) (by omega)
    (by decide) (by decide) (by decide)
  obtain ⟨c4, t4, q4⟩ := pop_step (i := 2) (len := 2) h hs q3 (by omega) (by omega)
    (by decide) (by decide) (by decide)
  obtain ⟨c5, t5, q5⟩ := pop_step (i := 1) (len := 2) h hs q4 (by omega) (by omega)
    (by decide) (by decide) (by decide)
  obtain ⟨c6, t6, q6⟩ := pop_step (i := 0) (len := 1) h hs q5 (by omega) (by omega)
    (by decide) (by decide) (by decide)
  exact ⟨c6, Reaches.cons t1 (Reaches.cons t2 (Reaches.cons t3
    (Reaches.cons t4 (Reaches.cons t5 (Reaches.one t6))))), q6⟩

/-- Every System V callee-saved register is one of the six this prologue
pushed. -/
theorem calleeSaved_eq_savedReg :
    ∀ r ∈ sysv64.calleeSaved, ∃ i, i < 6 ∧ savedReg i = r := by decide

/-- **The whole epilogue.** From `0x1b9`, the machine runs
`add $0xa8,%rsp`, the six pops and `ret`, and returns to `L.exit`.

This discharges `Post.rsp` and `Post.saved` outright, and leaves memory
untouched, so whatever footprint claim held on arrival still holds. It assumes
only `EpilogueState` — in particular that the six slots the prologue wrote are
intact — which is the body's obligation, not the epilogue's. -/
theorem epilogue (h : SysVEntry L state block rspEntry frameSize m)
    {mid : MState} (hs : EpilogueState L state rspEntry m mid) :
    ∃ final : MState, Returns L.exit mid final ∧
      final.core.read .rsp = rspEntry + 8#64 ∧
      sysv64.Preserved m.core.read final.core.read ∧
      final.memory = mid.memory := by
  obtain ⟨c0, t0, q0⟩ := epilogue_add hs
  obtain ⟨c6, r6, q6⟩ := epilogue_pops h hs q0
  have hrsp : c6.core.read .rsp = rspEntry := by rw [q6.rsp]; simp
  have hslot : HoldsLE c6.memory (c6.core.read .rsp).toNat 8 L.exit := by
    rw [hrsp, q6.mem]; exact hs.retAddr
  have hdec : decode ((raw.drop 458).take 1) = some (Instr.ret, 1) :=
    decode_raw (by decide +kernel)
  have hexec : exec .ret c6.core c6.memory
      = .ok { (c6.core.write .rsp (c6.core.read .rsp + 8#64)) with rip := L.exit }
          c6.memory := by
    simp only [exec, popWord_of_holdsLE hslot]
  have hstep : step L.exit c6
      = .returned ⟨{ (c6.core.write .rsp (c6.core.read .rsp + 8#64)) with rip := L.exit },
          c6.memory⟩ :=
    step_returned_of_loaded (offset := 458) (len := 1) (q6.mem ▸ hs.loaded) q6.rip
      (by rw [image_length]; decide)
      (by rw [image_slice_above _ _ (by decide : relocOffset + 4 ≤ 458)]; exact hdec)
      hexec rfl
  refine ⟨_, Returns.of_reaches (Reaches.cons t0 r6) hstep, ?_, ?_, q6.mem⟩
  · show (c6.core.write Reg.rsp (c6.core.read Reg.rsp + 8#64)).read Reg.rsp = _
    rw [Silmaril.X86.State.read_write_same, hrsp]
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := calleeSaved_eq_savedReg r hr
    show (c6.core.write Reg.rsp (c6.core.read Reg.rsp + 8#64)).read (savedReg i) = _
    rw [Silmaril.X86.State.read_write_other _ _ _ _ (savedReg_ne_rsp i hi)]
    exact q6.popped i hi (by omega)

/-! ## The data invariant: what L1 computes

L1's body is `mov (%rsi,%rax,4),%ecx; bswap %ecx; mov %ecx,-0x60(%rsp,%rax,4)`.
The load takes the four bytes of `block[]` at `4t` **little-endian**, because
that is how x86 loads a `uint32`; `bswap` reverses them; so the slot `w[t]`
ends up holding the **big-endian** word at `4t`, which is exactly the spec's
`beWordAt`.

That sentence is the whole of L1's mathematics, and this is it as a lemma. It
needs no bit-blasting: both sides are built from the same four bytes, and the
proof is bit extensionality plus the fact that a `Byte` has no bits at index
eight or above. -/

/-- **`bswap` of a little-endian load is the big-endian word.** The link
between what the instruction does and what the specification says. -/
theorem byteSwap32_leWordAt (bs : List Silmaril.Process.Byte) (t : Nat) :
    Silmaril.X86.Ext.byteSwap32 (leWordAt bs t) = beWordAt bs t := by
  have hge : ∀ (b : Silmaril.Process.Byte) (k : Nat), 8 ≤ k → b.getLsbD k = false :=
    fun b k hk => BitVec.getLsbD_of_ge b k hk
  simp only [Silmaril.X86.Ext.byteSwap32, leWordAt, beWordAt]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  split_ifs with h1 h2 h3 <;> intro hi
  · simp only [show 24 + i - 24 = i by omega,
      decide_eq_true (by omega : 24 + i < 32), decide_eq_false (by omega : ¬(24 + i < 24)),
      decide_eq_true (by omega : i < 24), decide_eq_true (by omega : i < 16),
      decide_eq_true (by omega : i < 32), decide_eq_true (by omega : i < 8),
      hge (byteAt bs (4 * t)) (24 + i) (by omega),
      hge (byteAt bs (4 * t + 1)) (24 + i - 8) (by omega),
      hge (byteAt bs (4 * t + 2)) (24 + i - 16) (by omega),
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.not_true, Bool.not_false]
  · simp only [show 16 + (i - 8) - 16 = i - 8 by omega,
      decide_eq_true (by omega : 16 + (i - 8) < 32),
      decide_eq_false (by omega : ¬(16 + (i - 8) < 16)),
      decide_eq_true (by omega : 16 + (i - 8) < 24),
      decide_eq_true (by omega : i < 24), decide_eq_true (by omega : i < 16),
      decide_eq_true (by omega : i - 8 < 32), decide_eq_true (by omega : i < 32),
      decide_eq_false (by omega : ¬(i < 8)), decide_eq_true (by omega : i - 8 < 8),
      hge (byteAt bs (4 * t)) (16 + (i - 8)) (by omega),
      hge (byteAt bs (4 * t + 1)) (16 + (i - 8) - 8) (by omega),
      hge (byteAt bs (4 * t + 3)) i (by omega),
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.not_true, Bool.not_false]
  · simp only [show i - 8 - 8 = i - 16 by omega, show 8 + (i - 16) - 8 = i - 16 by omega,
      decide_eq_true (by omega : 8 + (i - 16) < 32),
      decide_eq_false (by omega : ¬(8 + (i - 16) < 8)),
      decide_eq_true (by omega : 8 + (i - 16) < 16),
      decide_eq_true (by omega : 8 + (i - 16) < 24),
      decide_eq_true (by omega : i < 24), decide_eq_false (by omega : ¬(i < 16)),
      decide_eq_true (by omega : i - 16 < 32), decide_eq_true (by omega : i - 16 < 8),
      decide_eq_true (by omega : i < 32),
      decide_eq_false (by omega : ¬(i < 8)), decide_eq_true (by omega : i - 8 < 32),
      hge (byteAt bs (4 * t)) (8 + (i - 16)) (by omega),
      hge (byteAt bs (4 * t + 2)) (i - 8) (by omega),
      hge (byteAt bs (4 * t + 3)) i (by omega),
      Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.and_true, Bool.true_and, Bool.not_true, Bool.not_false]
  · simp only [show i - 8 - 8 - 8 = i - 24 by omega, show 0 + (i - 24) = i - 24 by omega,
      decide_eq_false (by omega : ¬(i < 24)), decide_eq_false (by omega : ¬(i < 16)),
      decide_eq_true (by omega : i - 24 < 32), decide_eq_true (by omega : i - 24 < 8),
      decide_eq_true (by omega : i - 24 < 16), decide_eq_true (by omega : i - 24 < 24),
      decide_eq_true (by omega : i < 32),
      hge (byteAt bs (4 * t + 1)) (i - 16) (by omega),
      hge (byteAt bs (4 * t + 2)) (i - 8) (by omega),
      hge (byteAt bs (4 * t + 3)) i (by omega),
      Bool.and_false, Bool.false_and, Bool.or_false,
      Bool.and_true, Bool.true_and, Bool.not_true, Bool.not_false]

/-! ## L1: `w[t] = bswap(block[t])` for `t = 0 … 15`

Six instructions at function offsets 32, 35, 37, 41, 44, 48, with a `jne`
backedge to 32 and a fallthrough to 50.

```
  32:  8b 0c 86        mov    (%rsi,%rax,4),%ecx
  35:  0f c9           bswap  %ecx
  37:  89 4c 84 a0     mov    %ecx,-0x60(%rsp,%rax,4)
  41:  48 ff c0        inc    %rax
  44:  48 83 f8 10     cmp    $0x10,%rax
  48:  75 ee           jne    32
```

Following Track 2c's `reaches_loop_of_trace`, the body is split in two: a
`trace` lemma that says what one iteration *does*, with hypotheses only about
what it needs to *execute*, and a `preserve` step that re-establishes the
invariant. The weak invariant below says nothing about what `w[]` holds, which
is all a liveness claim needs; strengthening it to the schedule reuses `trace`
unchanged. -/

/-- One `mov r, m` from a loaded image: a `sz.bytes`-wide load into a
register. Memory is unchanged.

**Note for Track 2c.** Generic in exactly the way `Ext.stepOpt_store_reg` is,
and belongs beside it — `-O0` loads far more often than it stores. -/
theorem stepOpt_load {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {sz : Silmaril.X86.Ext.Sz} {src : Silmaril.X86.Ext.Mem}
    {r : Reg} {v : Word}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.load sz r src, len))
    (hload : Silmaril.X86.Ext.loadN mm.memory
        (src.addr mm.core (base + BitVec.ofNat 64 (offset + len))) sz.bytes = some v) :
    stepOpt exit mm =
      some ⟨{ sz.write mm.core r (v.setWidth sz.bits)
              with rip := base + BitVec.ofNat 64 (offset + len) }, mm.memory⟩ := by
  have hl : (Instr.load sz r src).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded (by simp) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.readRM, hload, Option.map_some, Silmaril.X86.Ext.retire]

/-- Adding a small constant that cannot wrap. -/
theorem toNat_add_small {x : Word} {k : Nat} (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  have hk : (BitVec.ofNat 64 k).toNat = k := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, hk, Nat.mod_eq_of_lt h]

/-- Scaling the loop counter by four: the `*4` of `(%rsi,%rax,4)`. -/
theorem shiftLeft_two (i : Nat) (h : i < 2 ^ 60) :
    (BitVec.ofNat 64 i) <<< (2 : Nat) = BitVec.ofNat 64 (4 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- Small naturals are distinct as words exactly when they are distinct. -/
theorem ofNat_ne_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b) ↔ a ≠ b := by
  constructor
  · intro hne heq; exact hne (by rw [heq])
  · intro hne heq
    apply hne
    have h2 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at h2
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

/-- What one iteration of L1 does, said without reference to any invariant:
the counter advances, `%rsp` and `%rsi` are untouched, control goes to the
loop head or the fallthrough, and exactly the four bytes of `w[i]` are
written. Nothing here says *what* was written — that is the strengthening
step's business, and it reuses this lemma unchanged. -/
structure L1Effect (L : Layout) (rspEntry : Word) (i : Nat) (cur cur' : MState) : Prop where
  /-- Back to the loop head, or out to the fallthrough on the last iteration. -/
  rip : cur'.core.rip = L.textBase + BitVec.ofNat 64 (if i + 1 < 16 then 32 else 50)
  /-- The counter advanced. -/
  rax : cur'.core.read .rax = BitVec.ofNat 64 (i + 1)
  /-- The stack pointer is untouched. -/
  rsp : cur'.core.read .rsp = cur.core.read .rsp
  /-- The block pointer is untouched. -/
  rsi : cur'.core.read .rsi = cur.core.read .rsi
  /-- The output pointer is untouched. -/
  rdi : cur'.core.read .rdi = cur.core.read .rdi
  /-- Exactly the four bytes of `w[i]` were written, in the `leBytes` form
  `Ext.HoldsLE.of_stored_self` consumes. -/
  stored : ∃ v : Word, Stored cur.memory cur'.memory (rspEntry.toNat - 312 + 4 * i)
    (Silmaril.X86.Ext.leBytes v 4)

/-! ### The conditional branch

`jcc8` is the one instruction whose successor RIP depends on the flags, so it
gets two packaged lemmas rather than being unfolded at each use. Unfolding
`Ext.exec` inside a six-step trace is what makes the trace expensive; doing it
once here keeps each use cheap.

**Note for Track 2c.** Generic, and belongs beside `Ext.stepOpt_store_reg`. -/

set_option maxHeartbeats 8000000 in
/-- A `cmp imm8, reg` from a loaded image: flags only, no memory, no register
written. Packaged for the same reason the `jcc8` pair is — unfolding
`Ext.exec` inside a multi-step trace is what makes the trace expensive. -/
theorem stepOpt_cmp_reg {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {sz : Silmaril.X86.Ext.Sz} {r : Reg} {imm : BitVec 8}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len)
      = some (.aluI8 sz .cmp (.reg r) imm, len)) :
    stepOpt exit mm = some ⟨{ { mm.core with
        flags := Silmaril.X86.Ext.AluOp.flagsN .cmp (sz.read mm.core r)
          (imm.signExtend sz.bits) } with
        rip := base + BitVec.ofNat 64 (offset + len) }, mm.memory⟩ := by
  have hl : (Instr.aluI8 sz .cmp (.reg r) imm).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.retire,
    ite_true]

set_option maxHeartbeats 8000000 in
/-- A `jcc8` whose condition holds: RIP becomes the fallthrough plus the
sign-extended rel8. -/
theorem stepOpt_jcc8_taken {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jcc8 c rel, len))
    (hcond : c.eval mm.core.flags = some true) :
    stepOpt exit mm = some ⟨{ mm.core with
        rip := base + BitVec.ofNat 64 (offset + len) + rel.signExtend 64 }, mm.memory⟩ := by
  have hl : (Instr.jcc8 c rel).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hcond, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl]

set_option maxHeartbeats 8000000 in
/-- A `jcc8` whose condition fails: RIP becomes the fallthrough. -/
theorem stepOpt_jcc8_not_taken {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jcc8 c rel, len))
    (hcond : c.eval mm.core.flags = some false) :
    stepOpt exit mm =
      some ⟨{ mm.core with rip := base + BitVec.ofNat 64 (offset + len) }, mm.memory⟩ := by
  have hl : (Instr.jcc8 c rel).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hcond, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl]

/-! ### Opaque steps for the three forms Track 2c does not package

`Ext/SymExec.lean` and `Ext/Store.lean` package the loads, stores, ALU forms,
`cmp`, rel32 `jcc`, `push`, `pop` and `ret` in the opaque style. These three —
`bswap`, `inc` and the **rel8** `jcc8` — are what the `-O2` images add, and
they are wrapped here in exactly the same discipline, with
`Ext.opaque_writeReg_noFlags`, `Ext.opaque_writeReg` and `Ext.opaque_ripOnly`.

**Note for Track 2c.** All three are generic and belong beside the rest.
`jcc8` in particular is not a variant of `stepOpt_jcc`: that one takes a
`BitVec 32` rel, and every `-O2`/`-O3`/`-Os` loop backedge is rel8. -/

/-- `bswap r`, successor left opaque. No flags, no memory. -/
theorem stepOpt_bswap {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {sz : Silmaril.X86.Ext.Sz} {r : Reg}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.bswap sz r, len)) :
    ∃ next, stepOpt exit mm = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      Silmaril.X86.Ext.WritesReg mm.core next.core r
        ((Silmaril.X86.Ext.byteSwap sz (sz.read mm.core r)).setWidth 64) ∧
      next.core.flags = mm.core.flags ∧ next.memory = mm.memory := by
  refine Silmaril.X86.Ext.opaque_writeReg_noFlags ?_
  have hl : (Instr.bswap sz r).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write]

/-- `inc r`, successor left opaque. Writes the register and the flags. -/
theorem stepOpt_inc_reg {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {sz : Silmaril.X86.Ext.Sz} {r : Reg}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len)
      = some (.incdec sz false (.reg r), len)) :
    ∃ next, stepOpt exit mm = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      Silmaril.X86.Ext.WritesReg mm.core next.core r
        ((sz.read mm.core r + 1#sz.bits).setWidth 64) ∧
      next.core.flags =
        Silmaril.X86.Ext.incFlagsN (sz.read mm.core r) mm.core.flags ∧
      next.memory = mm.memory := by
  refine Silmaril.X86.Ext.opaque_writeReg ?_
  have hl : (Instr.incdec sz false (.reg r)).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM,
    Silmaril.X86.Ext.Sz.write, Option.map_some]
  rfl

/-- `mov r, r'` (register to register), successor left opaque. No flags, no
memory.

**Note for Track 2c.** `Ext` packages `mov` to and from memory but not the
register-to-register form, which `-O2` uses six times in L2 alone. -/
theorem stepOpt_mov_reg {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {sz : Silmaril.X86.Ext.Sz} {dst src : Reg}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.mov sz (.reg dst) src, len)) :
    ∃ next, stepOpt exit mm = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      Silmaril.X86.Ext.WritesReg mm.core next.core dst ((sz.read mm.core src).setWidth 64) ∧
      next.core.flags = mm.core.flags ∧ next.memory = mm.memory := by
  refine Silmaril.X86.Ext.opaque_writeReg_noFlags ?_
  have hl : (Instr.mov sz (.reg dst) src).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.Sz.write]

/-- `op r, m` — the direction-1 ALU form with a **memory** source, successor
left opaque. Writes the destination register and the flags.

**Note for Track 2c.** `Ext.stepOpt_aluR_reg` covers only a register source;
L2's `add -0x7c(%rsp,%rax,4),%r8d` needs this one. -/
theorem stepOpt_aluR_mem {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {sz : Silmaril.X86.Ext.Sz} {op : Silmaril.X86.AluOp}
    {dst : Reg} {src : Silmaril.X86.Ext.Mem}
    {address width : Nat} {value : Word}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluR sz op dst (.mem src), len))
    (not_cmp : op ≠ .cmp)
    (eff : (src.addr mm.core (base + BitVec.ofNat 64 (offset + len))).toNat = address)
    (width_eq : sz.bytes = width)
    (held : Silmaril.X86.Ext.HoldsLE mm.memory address width value) :
    ∃ next, stepOpt exit mm = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      Silmaril.X86.Ext.WritesReg mm.core next.core dst
        ((Silmaril.X86.Ext.AluOp.resultN op (sz.read mm.core dst)
          ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits)).setWidth 64) ∧
      next.core.flags = Silmaril.X86.Ext.AluOp.flagsN op (sz.read mm.core dst)
        ((BitVec.ofNat 64 (value.toNat % 2 ^ (8 * width))).setWidth sz.bits) ∧
      next.memory = mm.memory := by
  subst width_eq
  subst eff
  refine Silmaril.X86.Ext.opaque_writeReg ?_
  have hl : (Instr.aluR sz op dst (.mem src)).length = len := (decode_length decoded).1.symm
  have hload : Silmaril.X86.Ext.loadN mm.memory
      (src.addr mm.core (base + BitVec.ofNat 64 (offset + len))) sz.bytes
      = some (BitVec.ofNat 64 (value.toNat % 2 ^ (8 * sz.bytes))) :=
    Silmaril.X86.Ext.loadN_of_holdsLE held
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.readRM,
    hload, Option.map_some, Silmaril.X86.Ext.Sz.write]
  simp [not_cmp]

/-- A **rel8** conditional branch, successor left opaque. `Ext.stepOpt_jcc`
takes a `BitVec 32` rel; every `-O2`/`-O3`/`-Os` loop backedge is rel8, so
this is a different form and not an instance of it. -/
theorem stepOpt_jcc8 {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8} {taken : Bool}
    {target : Word}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.jcc8 c rel, len))
    (cond : c.eval mm.core.flags = some taken)
    (target_eq : (if taken then base + BitVec.ofNat 64 (offset + len) + rel.signExtend 64
      else base + BitVec.ofNat 64 (offset + len)) = target) :
    ∃ next, stepOpt exit mm = some next ∧
      next.core.rip = target ∧
      Silmaril.X86.Ext.SameRegs mm.core next.core ∧
      next.core.flags = mm.core.flags ∧ next.memory = mm.memory := by
  cases taken with
  | true =>
    subst target_eq
    exact Silmaril.X86.Ext.opaque_ripOnly
      (stepOpt_jcc8_taken loaded at_offset fits decoded cond)
  | false =>
    subst target_eq
    exact Silmaril.X86.Ext.opaque_ripOnly
      (stepOpt_jcc8_not_taken loaded at_offset fits decoded cond)

/-- A `NOP` of any length, successor left opaque: RIP only. -/
theorem stepOpt_nop {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {k : Fin 15}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.nop k, len)) :
    ∃ next, stepOpt exit mm = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      Silmaril.X86.Ext.SameRegs mm.core next.core ∧
      next.core.flags = mm.core.flags ∧ next.memory = mm.memory := by
  refine Silmaril.X86.Ext.opaque_ripOnly ?_
  have hl : (Instr.nop k).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.retire]

/-- `mov $imm32, r32` (`B8+r id`), successor left opaque. Zero-extends. -/
theorem stepOpt_movI32 {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {r : Reg} {imm : BitVec 32}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.movI32 r imm, len)) :
    ∃ next, stepOpt exit mm = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      Silmaril.X86.Ext.WritesReg mm.core next.core r (imm.setWidth 64) ∧
      next.core.flags = mm.core.flags ∧ next.memory = mm.memory := by
  refine Silmaril.X86.Ext.opaque_writeReg_noFlags ?_
  have hl : (Instr.movI32 r imm).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write]
  rfl

/-- `lea r, m`, successor left opaque: the effective address, as a value. -/
theorem stepOpt_lea {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {r : Reg} {src : Silmaril.X86.Ext.Mem} {value : Word}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.lea .q r src, len))
    (eff : src.addr mm.core (base + BitVec.ofNat 64 (offset + len)) = value) :
    ∃ next, stepOpt exit mm = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      Silmaril.X86.Ext.WritesReg mm.core next.core r value ∧
      next.core.flags = mm.core.flags ∧ next.memory = mm.memory := by
  subst eff
  refine Silmaril.X86.Ext.opaque_writeReg_noFlags ?_
  have hl : (Instr.lea .q r src).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Sz.write]
  rfl

/-- The addressing mode of `mov (%rsi,%rax,4),%ecx`. -/
def l1LoadMem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsi, index := some { reg := .rax, scale := 2#2, ne_rsp := by decide },
    disp := 0x00000000#32, rip_no_index := by intro h; exact absurd h (by decide) }

/-- The addressing mode of `mov %ecx,-0x60(%rsp,%rax,4)`. -/
def l1StoreMem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := some { reg := .rax, scale := 2#2, ne_rsp := by decide },
    disp := 0xffffffa0#32, rip_no_index := by intro h; exact absurd h (by decide) }

/-- The effective address of the load: `block + 4i`. -/
theorem l1LoadMem_addr {cur : MState} {i : Nat} {blk : Word} (hi : i < 16)
    (hrax : cur.core.read .rax = BitVec.ofNat 64 i)
    (hrsi : cur.core.read .rsi = blk) (next : Word) :
    l1LoadMem.addr cur.core next = blk + BitVec.ofNat 64 (4 * i) := by
  simp only [l1LoadMem, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Base.value_reg,
    Option.map_some, Option.getD_some, Silmaril.X86.Ext.Index.value, hrax, hrsi]
  rw [show (2#2 : BitVec 2).toNat = 2 from rfl, shiftLeft_two i (by omega),
    show ((0x00000000#32 : BitVec 32).signExtend 64) = 0#64 from rfl]
  simp

/-- The effective address of the store: `rspEntry - 312 + 4i`, the slot of
`w[i]`. Note `-0x60(%rsp)` with `%rsp = rspEntry - 216` is `rspEntry - 312`. -/
theorem l1StoreMem_addr {cur : MState} {i : Nat} {rspEntry : Word} (hi : i < 16)
    (hfits : (344 : Nat) ≤ rspEntry.toNat)
    (hrax : cur.core.read .rax = BitVec.ofNat 64 i)
    (hrsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216) (next : Word) :
    (l1StoreMem.addr cur.core next).toNat = rspEntry.toNat - 312 + 4 * i := by
  have hbase : (rspEntry - BitVec.ofNat 64 216).toNat = rspEntry.toNat - 216 :=
    Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := 216) (by omega) (by omega)
  have hx : ((rspEntry - BitVec.ofNat 64 216) + BitVec.ofNat 64 (4 * i)).toNat
      = rspEntry.toNat - 216 + 4 * i := by
    rw [toNat_add_small (by rw [hbase]; have := rspEntry.isLt; omega), hbase]
  simp only [l1StoreMem, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Base.value_reg,
    Option.map_some, Option.getD_some, Silmaril.X86.Ext.Index.value, hrax, hrsp]
  rw [show (2#2 : BitVec 2).toNat = 2 from rfl, shiftLeft_two i (by omega),
    show ((0xffffffa0#32 : BitVec 32).signExtend 64) = BitVec.ofNat 64 (2 ^ 64 - 96) from rfl,
    Silmaril.X86.Ext.toNat_add_neg (by omega) (by rw [hx]; omega), hx]
  omega

/-! ### The six decode facts of L1

Each is a lookup in the transcription (`decode_raw`). They are
separate declarations so the kernel checks six small terms rather than one
large one inside `l1_trace`; inlining them makes the trace an order of
magnitude more expensive to check. -/

set_option maxRecDepth 8000 in
/-- `32: 8b 0c 86` — `mov (%rsi,%rax,4),%ecx`. -/
theorem l1_decode_load : decode ((raw.drop 32).take 3)
    = some (.load .d .rcx l1LoadMem, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `35: 0f c9` — `bswap %ecx`. -/
theorem l1_decode_bswap : decode ((raw.drop 35).take 2)
    = some (.bswap .d .rcx, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `37: 89 4c 84 a0` — `mov %ecx,-0x60(%rsp,%rax,4)`. -/
theorem l1_decode_store : decode ((raw.drop 37).take 4)
    = some (.mov .d (.mem l1StoreMem) .rcx, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `41: 48 ff c0` — `inc %rax`. -/
theorem l1_decode_inc : decode ((raw.drop 41).take 3)
    = some (.incdec .q false (.reg .rax), 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `44: 48 83 f8 10` — `cmp $0x10,%rax`. -/
theorem l1_decode_cmp : decode ((raw.drop 44).take 4)
    = some (.aluI8 .q .cmp (.reg .rax) 0x10#8, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `48: 75 ee` — `jne 32`, the backedge. -/
theorem l1_decode_jne : decode ((raw.drop 48).take 2)
    = some (.jcc8 .ne 0xee#8, 2) :=
  decode_raw (by decide +kernel)

/-- The per-step bundle the L1 trace carries: where RIP and the three live
registers are, and that the image is still loaded. Memory effects are tracked
separately, since only the store has one. -/
structure L1At (L : Layout) (rspEntry st blk : Word) (img : List Byte) (off : Nat)
    (rax : Word) (cur : MState) : Prop where
  /-- RIP is at function offset `off`. -/
  rip : cur.core.rip = L.textBase + BitVec.ofNat 64 off
  /-- The counter. -/
  rax : cur.core.read .rax = rax
  /-- The frame is open. -/
  rsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216
  /-- The block pointer. -/
  rsi : cur.core.read .rsi = blk
  /-- The output pointer, which nothing in the function writes. -/
  rdi : cur.core.read .rdi = st
  /-- The image is still loaded. The byte list is a *parameter*: keeping the
  459-byte literal out of the trace is what makes the proof term small enough
  for the kernel. See the module doc. -/
  loaded : Loaded cur.memory L.textBase img

set_option maxRecDepth 8000 in
/-- The `jne` backedge target: the fallthrough at function offset 50 plus the
sign-extended rel8 `0xee` (−18) is the loop head at 32. -/
theorem l1_backedge (textBase : Word) :
    textBase + BitVec.ofNat 64 (48 + 2) + (0xee#8 : BitVec 8).signExtend 64
      = textBase + BitVec.ofNat 64 32 := by
  rw [show ((0xee#8 : BitVec 8).signExtend 64) = BitVec.ofNat 64 (2 ^ 64 - 18) from rfl,
    add_assoc, Silmaril.X86.Ext.ofNat_add_ofNat]
  congr 1

set_option maxRecDepth 8000 in
/-- The loop counter, as a word, is `16` exactly when it is `16` as a number. -/
theorem l1_counter_ne {i : Nat} (hi : i < 16) :
    (BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 16) ↔ (i + 1 ≠ 16) :=
  ofNat_ne_ofNat (by omega) (by omega)

/-- **The L1 trace, first half:** the four instructions that move data — the
`mov` from `block`, the `bswap`, the `mov` to `w[i]`, and the `inc`.

Every step goes through an opaque-successor lemma, so no conclusion contains
another's state term. `img` is a parameter for the reason in the module doc.

The load's precondition is a `HoldsLE`, which is what `Ext.stepOpt_load`
consumes. Deriving one from `SysVEntry.blockMapped`'s `readBytes … = some
bytes` needs a `readBytes → HoldsLE` bridge that neither track has; see the
module doc. -/
theorem l1_trace_data (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} {i : Nat} {img : List Byte} (hi : i < 16)
    (himg : img.length = size)
    (d32 : decode ((img.drop 32).take 3) = some (.load .d .rcx l1LoadMem, 3))
    (d35 : decode ((img.drop 35).take 2) = some (.bswap .d .rcx, 2))
    (d37 : decode ((img.drop 37).take 4) = some (.mov .d (.mem l1StoreMem) .rcx, 4))
    (d41 : decode ((img.drop 41).take 3) = some (.incdec .q false (.reg .rax), 3))
    (hat : L1At L rspEntry state block img 32 (BitVec.ofNat 64 i) cur)
    {v : Word} (hv : Silmaril.X86.Ext.HoldsLE cur.memory (block.toNat + 4 * i) 4 v)
    (hwrite : cur.memory.Permitted .write (rspEntry.toNat - 312 + 4 * i) 4) :
    ∃ c4, Reaches L.exit cur c4 ∧ L1At L rspEntry state block img 44 (BitVec.ofNat 64 (i + 1)) c4 ∧
      Stored cur.memory c4.memory (rspEntry.toNat - 312 + 4 * i)
        (Silmaril.X86.Ext.leBytes
          ((Silmaril.X86.Ext.byteSwap32 (v.setWidth 32)).setWidth 64) 4) := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hwrap : block.toNat + 64 ≤ Silmaril.Process.addressLimit := by
    have := h.noWrap (blockRegion block) (by simp [regions])
    simpa [blockRegion] using this
  have hloadAddr : (l1LoadMem.addr cur.core
      (L.textBase + BitVec.ofNat 64 (32 + 3))).toNat = block.toNat + 4 * i := by
    rw [l1LoadMem_addr hi hat.rax hat.rsi]
    refine toNat_add_small ?_
    rw [Silmaril.Process.addressLimit] at hwrap; omega
  -- 32: mov (%rsi,%rax,4),%ecx
  obtain ⟨c1, t1, h1rip, h1regs, _h1flags, h1mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 32) (len := 3)
      hat.loaded hat.rip (by rw [himg]; decide) d32 hloadAddr rfl hv rfl
  -- 35: bswap %ecx
  obtain ⟨c2, t2, h2rip, h2regs, _h2flags, h2mem⟩ :=
    stepOpt_bswap (exit := L.exit) (offset := 35) (len := 2)
      (h1mem ▸ hat.loaded) h1rip (by rw [himg]; decide) d35
  -- 37: mov %ecx,-0x60(%rsp,%rax,4)
  have hstoreAddr : (l1StoreMem.addr c2.core
      (L.textBase + BitVec.ofNat 64 (37 + 4))).toNat = rspEntry.toNat - 312 + 4 * i := by
    refine l1StoreMem_addr hi hfits ?_ ?_ _
    · rw [h2regs.other _ (by decide), h1regs.other _ (by decide)]; exact hat.rax
    · rw [h2regs.other _ (by decide), h1regs.other _ (by decide)]; exact hat.rsp
  obtain ⟨c3, t3, h3rip, h3regs, _h3flags, h3stored⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 37) (len := 4)
      (width := 4)
      (h2mem ▸ h1mem ▸ hat.loaded) h2rip (by rw [himg]; decide) d37
      hstoreAddr rfl rfl (by rw [h2mem, h1mem]; exact hwrite)
  have hbslen : (Silmaril.X86.Ext.leBytes
      ((Silmaril.X86.Ext.Sz.d.read c2.core Reg.rcx).setWidth 64) 4).length = 4 :=
    Silmaril.X86.Ext.length_leBytes _ _
  -- 41: inc %rax
  obtain ⟨c4, t4, h4rip, h4regs, _h4flags, h4mem⟩ :=
    stepOpt_inc_reg (exit := L.exit) (offset := 41) (len := 3)
      (Silmaril.X86.Ext.Loaded.of_stored (h2mem ▸ h1mem ▸ hat.loaded) h3stored
        (by rw [hbslen, himg]
            exact h.store_disjoint_code (by omega) (by omega)))
      h3rip (by rw [himg]; decide) d41
  refine ⟨c4, Reaches.cons t1 (Reaches.cons t2 (Reaches.cons t3 (Reaches.one t4))), ?_, ?_⟩
  · refine { rip := h4rip, rax := ?_, rsp := ?_, rsi := ?_, rdi := ?_, loaded := ?_ }
    · have hr : Silmaril.X86.Ext.Sz.q.read c3.core Reg.rax = BitVec.ofNat 64 i := by
        rw [Silmaril.X86.Ext.Sz.read_q, h3regs _, h2regs.other _ (by decide),
          h1regs.other _ (by decide)]
        exact hat.rax
      rw [h4regs.target, hr]
      exact Silmaril.X86.Ext.ofNat_add_ofNat i 1
    · rw [h4regs.other _ (by decide), h3regs _, h2regs.other _ (by decide),
        h1regs.other _ (by decide)]; exact hat.rsp
    · rw [h4regs.other _ (by decide), h3regs _, h2regs.other _ (by decide),
        h1regs.other _ (by decide)]; exact hat.rsi
    · rw [h4regs.other _ (by decide), h3regs _, h2regs.other _ (by decide),
        h1regs.other _ (by decide)]; exact hat.rdi
    · rw [h4mem]
      exact Silmaril.X86.Ext.Loaded.of_stored (h2mem ▸ h1mem ▸ hat.loaded) h3stored
        (by rw [hbslen, himg]
            exact h.store_disjoint_code (by omega) (by omega))
  · have hval : (Silmaril.X86.Ext.Sz.d.read c2.core Reg.rcx).setWidth 64
        = (Silmaril.X86.Ext.byteSwap32 (v.setWidth 32)).setWidth 64 := by
      have e2 := h2regs.target
      have e1 := h1regs.target
      simp only [Silmaril.X86.Ext.Sz.read] at e2 e1 ⊢
      rw [e2, e1]
      show BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
            (Silmaril.X86.Ext.byteSwap32 (BitVec.setWidth 32 (BitVec.setWidth 64
              (BitVec.setWidth 32 (BitVec.ofNat 64 (v.toNat % 2 ^ 32))))))))
          = BitVec.setWidth 64 (Silmaril.X86.Ext.byteSwap32 (BitVec.setWidth 32 v))
      have hv32 : BitVec.setWidth 32 (BitVec.ofNat 64 (v.toNat % 2 ^ 32))
          = BitVec.setWidth 32 v := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        omega
      rw [hv32, BitVec.setWidth_setWidth_of_le _ (by omega : (32:Nat) ≤ 64),
        BitVec.setWidth_eq, BitVec.setWidth_setWidth_of_le _ (by omega : (32:Nat) ≤ 64),
        BitVec.setWidth_eq]
    rw [← hval, h4mem, ← h1mem, ← h2mem]
    exact h3stored

/-- The second half of the L1 trace: `cmp $0x10,%rax` and the `jne` backedge.

Both steps go through Track 2c's opaque-successor lemmas, so neither
conclusion contains the other's state term. -/
theorem l1_trace_branch {c4 : MState} {i : Nat} {img : List Byte} (hi : i < 16)
    (himg : img.length = size)
    (d44 : decode ((img.drop 44).take 4) = some (.aluI8 .q .cmp (.reg .rax) 0x10#8, 4))
    (d48 : decode ((img.drop 48).take 2) = some (.jcc8 .ne 0xee#8, 2))
    (a4 : L1At L rspEntry state block img 44 (BitVec.ofNat 64 (i + 1)) c4) :
    ∃ c6, Reaches L.exit c4 c6 ∧
      c6.core.rip = L.textBase + BitVec.ofNat 64 (if i + 1 < 16 then 32 else 50) ∧
      c6.core.read .rax = BitVec.ofNat 64 (i + 1) ∧
      c6.core.read .rsp = c4.core.read .rsp ∧
      c6.core.read .rsi = c4.core.read .rsi ∧
      c6.core.read .rdi = c4.core.read .rdi ∧
      c6.memory = c4.memory := by
  obtain ⟨c5, t5, h5rip, h5regs, h5flags, h5mem⟩ :=
    Silmaril.X86.Ext.stepOpt_cmpI8_reg (exit := L.exit) (offset := 44) (len := 4)
      a4.loaded a4.rip (by rw [himg]; decide) d44
  have hcond : Silmaril.X86.Ext.Cond.ne.eval c5.core.flags
      = some (decide (BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 16)) := by
    rw [h5flags]
    have : Silmaril.X86.Ext.Sz.q.read c4.core Reg.rax = BitVec.ofNat 64 (i + 1) := by
      rw [Silmaril.X86.Ext.Sz.read_q]; exact a4.rax
    rw [this, show ((0x10#8 : BitVec 8).signExtend Silmaril.X86.Ext.Sz.q.bits)
      = BitVec.ofNat 64 16 from rfl]
    exact Silmaril.X86.Ext.eval_ne_cmp _ _
  have hdec : decide (BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 16)
      = decide (i + 1 ≠ 16) := by
    simp only [l1_counter_ne hi]
  have htarget : (if decide (i + 1 ≠ 16) = true then
        L.textBase + BitVec.ofNat 64 (48 + 2) + (0xee#8 : BitVec 8).signExtend 64
      else L.textBase + BitVec.ofNat 64 (48 + 2))
      = L.textBase + BitVec.ofNat 64 (if i + 1 < 16 then 32 else 50) := by
    by_cases hlast : i + 1 = 16
    · rw [show (decide (i + 1 ≠ 16)) = false from by simp [hlast]]
      rw [show (if i + 1 < 16 then (32 : Nat) else 50) = 50 from by simp [hlast]]
      rfl
    · rw [show (decide (i + 1 ≠ 16)) = true from by simp [hlast]]
      simp only [reduceIte]
      rw [show (if i + 1 < 16 then (32 : Nat) else 50) = 32 from
        ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      exact l1_backedge L.textBase
  obtain ⟨c6, t6, h6rip, h6regs, h6flags, h6mem⟩ :=
    stepOpt_jcc8 (exit := L.exit) (offset := 48) (len := 2)
      (h5mem ▸ a4.loaded) h5rip (by rw [himg]; decide) d48
      (by rw [hcond, hdec]) htarget
  exact ⟨c6, Reaches.cons t5 (Reaches.one t6), h6rip,
    by rw [h6regs, h5regs]; exact a4.rax,
    by rw [h6regs, h5regs], by rw [h6regs, h5regs], by rw [h6regs, h5regs],
    by rw [h6mem, h5mem]⟩

/-- **The L1 trace.** One iteration of the message-load loop, stated without
reference to any invariant: it needs only that the image is loaded, where RIP
and the three live registers are, that `block[4i .. 4i+4)` reads, and that
`w[i]`'s slot is writable. The weak and strong invariants both consume this
lemma unchanged — that is the point of the split described in the module
doc. -/
theorem l1_trace (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} {i : Nat} (hi : i < 16)
    (hat : L1At L rspEntry state block (image L.textBase L.rodataBase) 32 (BitVec.ofNat 64 i) cur)
    (hread : ∃ v, Silmaril.X86.Ext.HoldsLE cur.memory (block.toNat + 4 * i) 4 v)
    (hwrite : cur.memory.Permitted .write (rspEntry.toNat - 312 + 4 * i) 4) :
    ∃ cur', Reaches L.exit cur cur' ∧ L1Effect L rspEntry i cur cur' := by
  have hsl : ∀ o l : Nat, o + l ≤ relocOffset →
      ((image L.textBase L.rodataBase).drop o).take l = (raw.drop o).take l :=
    fun o l hb => image_slice _ _ hb
  obtain ⟨v, hv⟩ := hread
  obtain ⟨c4, r4, a4, hst⟩ := l1_trace_data h hi (image_length L.textBase L.rodataBase)
    (by rw [hsl 32 3 (by decide)]; exact l1_decode_load)
    (by rw [hsl 35 2 (by decide)]; exact l1_decode_bswap)
    (by rw [hsl 37 4 (by decide)]; exact l1_decode_store)
    (by rw [hsl 41 3 (by decide)]; exact l1_decode_inc) hat hv hwrite
  obtain ⟨c6, r6, h6rip, h6rax, h6rsp, h6rsi, h6rdi, h6mem⟩ := l1_trace_branch hi (image_length L.textBase L.rodataBase)
    (by rw [hsl 44 4 (by decide)]; exact l1_decode_cmp)
    (by rw [hsl 48 2 (by decide)]; exact l1_decode_jne) a4
  refine ⟨c6, r4.trans r6, ?_⟩
  refine { rip := h6rip, rax := h6rax, rsp := ?_, rsi := ?_, rdi := ?_, stored :=
    ⟨(Silmaril.X86.Ext.byteSwap32 (v.setWidth 32)).setWidth 64, ?_⟩ }
  · rw [h6rsp, a4.rsp]; exact hat.rsp.symm
  · rw [h6rsi, a4.rsi]; exact hat.rsi.symm
  · rw [h6rdi, a4.rdi]; exact hat.rdi.symm
  · rw [h6mem]; exact hst

/-! ## The weak L1 invariant, and the loop

`L1Inv` is the **weak** invariant: where RIP, the counter and the two pointers
are, that the image is still loaded, that everything written so far is inside
the footprint, and that `block[]` still reads. It says nothing about what
`w[]` holds. That is all a liveness claim needs, and strengthening it to the
schedule will reuse `l1_trace` unchanged.

Note the `rip` component is a *function of the index*: at `i < 16` control is
at the loop head `32`, and at `i = 16` it is at the fallthrough `50`, because
this loop is bottom-tested with a `jne` backedge. A top-tested loop (clang
`-O0`) is at the head for every `i` including `i = N`; writing the invariant
with a constant `rip` only looks like the general shape. -/

/-- Each of the sixteen message words of `block[]` is a readable four-byte
slot. This is the `HoldsLE` form `Ext.stepOpt_load` consumes.

**It does not follow from `BlockReads`**, and that is a gap rather than an
oversight: `BlockReads` gives `readBytes … = some bytes`, every load lemma
wants `HoldsLE`, and the bridge — "a byte list of length `k ≤ 8` is `leBytes`
of some word" — exists in neither track. See the module doc. -/
def BlockWordsHold (memory : Memory) (block : Word) : Prop :=
  ∀ j, j < 16 → ∃ v, Silmaril.X86.Ext.HoldsLE memory (block.toNat + 4 * j) 4 v

/-- `BlockWordsHold` from the contract's `BlockReads`, through Track 2c's
`Ext.holdsLE_of_readBytes`: a `readBytes` precondition yields the `HoldsLE`
slot fact every load lemma consumes, because `leBytes` inverts `leValue` for
any access of at most eight bytes. No precondition strengthening is needed. -/
theorem blockWordsHold_of_reads {memory : Memory} {blk : Word}
    (h : BlockReads memory blk) : BlockWordsHold memory blk := by
  intro j hj
  obtain ⟨bytes, hb⟩ := h
  exact ⟨_, Silmaril.X86.Ext.holdsLE_of_readBytes
    (Silmaril.X86.Ext.readWith_sub (access := .read) hb (offset := 4 * j) (len := 4)
      (by omega) (by omega)) (by omega)⟩

/-- The four bytes of message word `i` load. -/
theorem loadN_block_word (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} (hreads : BlockReads cur.memory block) {i : Nat} (hi : i < 16) :
    ∃ v, Silmaril.X86.Ext.loadN cur.memory (block + BitVec.ofNat 64 (4 * i)) 4 = some v := by
  obtain ⟨bytes, hb⟩ := hreads
  have hwrap : block.toNat + 64 ≤ Silmaril.Process.addressLimit := by
    have := h.noWrap (blockRegion block) (by simp [regions])
    simpa [blockRegion] using this
  have haddr : (block + BitVec.ofNat 64 (4 * i)).toNat = block.toNat + 4 * i := by
    refine toNat_add_small ?_
    rw [Silmaril.Process.addressLimit] at hwrap
    omega
  have := Silmaril.X86.Ext.readWith_sub (access := .read) hb (offset := 4 * i) (len := 4)
    (by omega) (by omega)
  exact ⟨BitVec.ofNat 64 (Silmaril.X86.Ext.leValue ((bytes.drop (4 * i)).take 4)), by
    rw [Silmaril.X86.Ext.loadN, haddr]
    rw [show cur.memory.readBytes (block.toNat + 4 * i) 4 = _ from this]
    rfl⟩

/-- The first `t` words of `w[]` are **backed**: each reads.

`w[j]` lives at `rspEntry − 312 + 4j`, since `%rsp` in the body is
`rspEntry − 216` and the array base is `-0x60(%rsp)`.

This is the part of the weak invariant that is *not* optional. L2 reads
`w[t-15]`, `w[t-7]` and `w[t-2]`, and an unbacked frame byte faults exactly as
an unbacked `block` byte does, so a liveness claim for L2 needs every word L1
and the earlier L2 iterations wrote to read back. It says nothing about *what*
they hold — that is the strengthening. -/
def WWordsRead (memory : Memory) (rspEntry : Word) (t : Nat) : Prop :=
  ∀ j, j < t → ∃ v : Word,
    Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 312 + 4 * j) 4 v

/-- Writing word `t` extends the backed prefix from `t` to `t + 1`. The
earlier words are untouched because the slots are disjoint; the new one reads
because a store reads back.

Takes no `SysVEntry`: it is a fact about a store into a slot, not about this
function's entry state. -/
theorem WWordsRead.succ {before after : Memory} {t : Nat} (ht : t < 64)
    (hw : WWordsRead before rspEntry t) {v : Word}
    (hst : Stored before after (rspEntry.toNat - 312 + 4 * t)
      (Silmaril.X86.Ext.leBytes v 4))
    (hperm : before.Permitted .read (rspEntry.toNat - 312 + 4 * t) 4) :
    WWordsRead after rspEntry (t + 1) := by
  have hlen : (Silmaril.X86.Ext.leBytes v 4).length = 4 :=
    Silmaril.X86.Ext.length_leBytes _ _
  intro j hj
  rcases Nat.lt_or_ge j t with hlt | hge
  · obtain ⟨w, hb⟩ := hw j hlt
    exact ⟨w, Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst hb (by rw [hlen]; omega)⟩
  · have hjt : j = t := by omega
    subst hjt
    exact ⟨v, Silmaril.X86.Ext.HoldsLE.of_stored_self hst hperm⟩

/-- **The `w[]` slot rule, pinned.** The schedule slot `j` holds `val j`.

The same rule as `WWordsRead` at a particular assignment of values, exactly as
`SavedSlotsAt` is to `SavedSlotsHold`. Liveness needs only that the slot is
backed, so that the later load cannot fault; `Post.compressed` needs to know
*which* word is in it. `WWordsAt.succ` and `WWordsRead.succ` have the same
proof because extending the backed prefix is an argument about disjointness
and says nothing about the values. -/
def WWordsAt (memory : Memory) (rspEntry : Word) (val : Nat → Word) (t : Nat) : Prop :=
  ∀ j, j < t → Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 312 + 4 * j) 4 (val j)

/-- **`state[]`'s eight words, pinned.** The caller's bytes, carried from the
prologue to the point the feed-forward reads them. `SysVEntry` cannot supply
this: it pins `state[]` by backing only, because `state[]` is an *output* and
its entry contents are an input to the specification rather than a precondition
on the image. -/
def StateWordsAt (memory : Memory) (st : Word) (sv : Nat → SHA256.Kernel.Word) : Prop :=
  ∀ j, j < 8 → Silmaril.X86.Ext.HoldsLE memory (st.toNat + 4 * j) 4 ((sv j).setWidth 64)

/-- Pinned implies backed. The only direction anything needs. -/
theorem WWordsAt.weaken {memory : Memory} {val : Nat → Word} {t : Nat}
    (hw : WWordsAt memory rspEntry val t) : WWordsRead memory rspEntry t :=
  fun j hj => ⟨val j, hw j hj⟩

/-- Writing word `t` extends the pinned prefix from `t` to `t + 1`. -/
theorem WWordsAt.succ {before after : Memory} {val : Nat → Word} {t : Nat} (ht : t < 64)
    (hw : WWordsAt before rspEntry val t)
    (hst : Stored before after (rspEntry.toNat - 312 + 4 * t)
      (Silmaril.X86.Ext.leBytes (val t) 4))
    (hperm : before.Permitted .read (rspEntry.toNat - 312 + 4 * t) 4) :
    WWordsAt after rspEntry val (t + 1) := by
  have hlen : (Silmaril.X86.Ext.leBytes (val t) 4).length = 4 :=
    Silmaril.X86.Ext.length_leBytes _ _
  intro j hj
  rcases Nat.lt_or_ge j t with hlt | hge
  · exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst (hw j hlt) (by rw [hlen]; omega)
  · have hjt : j = t := by omega
    subst hjt
    exact Silmaril.X86.Ext.HoldsLE.of_stored_self hst hperm

/-- The six callee-saved slots the prologue wrote are **backed**: each reads.

Nothing between the prologue and the epilogue touches `[rspEntry − 48,
rspEntry)` — the body works entirely below `rspEntry − 56` — so these slots
appear nowhere in any loop body's reasoning. That is precisely why they must
be carried explicitly: only the `pop`s notice, at the very last steps of the
function, and a liveness proof that omitted them would fail there with
everything else already done.

The *value* is irrelevant: `pop` into a callee-saved register cannot fault
whatever it reads, so liveness needs the slot to read at all, not to hold
anything in particular. Hence the bare existential. (Restoring the *right*
values is `Post.saved`, and that is `EpilogueState.slots`, which is a
different and stronger fact.) -/
def SavedSlotsAt (memory : Memory) (rspEntry : Word) (val : Nat → Word) : Prop :=
  ∀ j, j < 6 →
    Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 8 * (j + 1)) 8 (val j)

/-- The **weak instantiation**: some eight bytes are there, values unspecified.

`SavedSlotsAt` and `SavedSlotsHold` are deliberately one rule read at two
instantiations rather than two rules. Liveness needs only that the slot is
backed, so that the `pop` cannot fault, and that is this form. `Post.saved`
needs to know *which* bytes, and reads the same rule at
`fun j => entry.core.read (savedReg j)`. The preservation argument —
`SavedSlotsAt.store` — is about disjointness and never mentions the values, so
it is proved once and serves both. -/
def SavedSlotsHold (memory : Memory) (rspEntry : Word) : Prop :=
  ∀ j, j < 6 → ∃ v : Word,
    Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 8 * (j + 1)) 8 v

/-- Pinned implies existential. The only direction anything needs. -/
theorem SavedSlotsAt.weaken {memory : Memory} {rspEntry : Word} {val : Nat → Word}
    (hs : SavedSlotsAt memory rspEntry val) : SavedSlotsHold memory rspEntry :=
  fun j hj => ⟨val j, hs j hj⟩

/-- A store anywhere in the body leaves the six saved slots alone: the body
never writes at or above `rspEntry − 56`, and the slots start at
`rspEntry − 48`.

Note that `val` is untouched: this is why the weak and the pinned invariant
can share a preservation lemma. -/
theorem SavedSlotsAt.store {before after : Memory} {addr : Nat} {bs : List Byte}
    {val : Nat → Word}
    (hs : SavedSlotsAt before rspEntry val)
    (hst : Stored before after addr bs)
    (hlen : bs.length = 4)
    (hfits : (344 : Nat) ≤ rspEntry.toNat)
    (hhigh : addr + 4 ≤ rspEntry.toNat - 56) :
    SavedSlotsAt after rspEntry val :=
  fun j hj =>
    Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst (hs j hj) (by rw [hlen]; omega)

/-- A write inside `state[]` misses the code. -/
theorem SysVEntry.stateStore_disjoint_code (h : SysVEntry L state block rspEntry frameSize m)
    {address len : Nat} (lo : state.toNat ≤ address) (hi : address + len ≤ state.toNat + 32) :
    L.textBase.toNat + size ≤ address ∨ address + len ≤ L.textBase.toNat := by
  have hd := h.state_disjoint_code
  simp only [stateRegion, codeRegion, Region.Disjoint] at hd
  omega

/-- The eight words of `state[]` read. Like `block[]` and unlike the `K`
table, `SysVEntry` pins only backing here, so this is a hypothesis of the
blocks that read it rather than something derived. -/
def StateWordsHold (memory : Memory) (st : Word) : Prop :=
  ∀ j, j < 8 → ∃ v : Word, Silmaril.X86.Ext.HoldsLE memory (st.toNat + 4 * j) 4 v

/-- `StateWordsHold` from the contract's `StateReads`, through the same
bridge. -/
theorem stateWordsHold_of_reads {memory : Memory} {st : Word}
    (h : StateReads memory st) : StateWordsHold memory st := by
  intro j hj
  obtain ⟨bytes, hb⟩ := h
  exact ⟨_, Silmaril.X86.Ext.holdsLE_of_readBytes
    (Silmaril.X86.Ext.readWith_sub (access := .read) hb (offset := 4 * j) (len := 4)
      (by omega) (by omega)) (by omega)⟩

/-- The **weak** L1 invariant after `i` iterations. -/
structure L1Inv (L : Layout) (state block rspEntry : Word) (entry : MState)
    (i : Nat) (cur : MState) : Prop where
  /-- The counter has not run past the trip count. -/
  bound : i ≤ 16
  /-- RIP, the counter, the two pointers and the loaded image. `rip` is a
  function of `i` because the loop is bottom-tested. -/
  at_ : L1At L rspEntry state block (image L.textBase L.rodataBase)
          (if i < 16 then 32 else 50) (BitVec.ofNat 64 i) cur
  /-- Everything written so far is inside the modifies set. -/
  frame : Memory.WritesWithin entry.memory cur.memory (Footprint state rspEntry frameSize)
  /-- `block[]`'s words still read: the loop never writes to it. -/
  reads : BlockWordsHold cur.memory block
  /-- The `i` words written so far read back. L2 needs this, so L1's weak
  invariant has to establish it: the two loops' weak invariants compose, they
  are not independent. -/
  words : WWordsRead cur.memory rspEntry i
  /-- The six callee-saved slots still read. Nothing in L1 touches them; only
  the epilogue's `pop`s will. -/
  saved : SavedSlotsAt cur.memory rspEntry (fun j => entry.core.read (savedReg j))
  /-- `state[]` still reads: block `150 … 224` needs it, and L1 writes only
  `w[]`, which is disjoint. -/
  stwords : StateWordsHold cur.memory state

/-- A write anywhere in the frame is disjoint from `block[]`. -/
theorem SysVEntry.store_disjoint_block (h : SysVEntry L state block rspEntry frameSize m)
    {address len : Nat} (lower : rspEntry.toNat - 344 ≤ address)
    (upper : address + len ≤ rspEntry.toNat) :
    block.toNat + 64 ≤ address ∨ address + len ≤ block.toNat := by
  have hd := h.block_disjoint_frame
  have hfits := h.frameFits
  rw [frameExtent_eq] at hfits
  simp only [blockRegion, frameRegion, Region.Disjoint, frameFloor_eq, frameExtent_eq] at hd
  omega

/-- **Invariant preservation for L1.** The second half of Track 2c's
`reaches_loop_of_trace` split: it consumes `L1Effect` and says nothing about
how the iteration ran. Strengthening the invariant to the schedule extends
this lemma and leaves `l1_trace` untouched. -/
theorem l1_preserve (h : SysVEntry L state block rspEntry frameSize m)
    {i : Nat} (hi : i < 16) {cur cur' : MState}
    (inv : L1Inv L state block rspEntry m i cur)
    (eff : L1Effect L rspEntry i cur cur') :
    L1Inv L state block rspEntry m (i + 1) cur' := by
  obtain ⟨sv, hst⟩ := eff.stored
  have hbs : (Silmaril.X86.Ext.leBytes sv 4).length = 4 :=
    Silmaril.X86.Ext.length_leBytes _ _
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hlow : rspEntry.toNat - 344 ≤ rspEntry.toNat - 312 + 4 * i := by omega
  have hhigh : rspEntry.toNat - 312 + 4 * i + 4 ≤ rspEntry.toNat := by omega
  refine { bound := by omega, at_ := ?_, frame := ?_, reads := ?_, words := ?_, saved := ?_, stwords := ?_ }
  · exact { rip := eff.rip
            rax := eff.rax
            rsp := by rw [eff.rsp]; exact inv.at_.rsp
            rsi := by rw [eff.rsi]; exact inv.at_.rsi
            rdi := by rw [eff.rdi]; exact inv.at_.rdi
            loaded := Silmaril.X86.Ext.Loaded.of_stored inv.at_.loaded hst
              (by rw [hbs, image_length]; exact h.store_disjoint_code hlow hhigh) }
  · exact Silmaril.Process.Memory.WritesWithin.step inv.frame hst (by
      intro offset hoff
      rw [hbs] at hoff
      exact frame_in_footprint (by rw [frameExtent_eq]; omega) (by omega) (by omega))
  · intro j hj
    obtain ⟨v, hv⟩ := inv.reads j hj
    refine ⟨v, Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst hv ?_⟩
    rw [hbs]
    have := h.store_disjoint_block (address := rspEntry.toNat - 312 + 4 * i) (len := 4)
      hlow hhigh
    omega
  · refine WWordsRead.succ (by omega) inv.words hst ?_
    rw [Silmaril.Process.Memory.WritesWithin.permitted_iff inv.frame]
    exact h.frame_readable (by omega) hlow hhigh
  · exact SavedSlotsAt.store inv.saved hst hbs hfits (by omega)
  · have hd2 := h.state_disjoint_frame
    simp only [stateRegion, frameRegion, Region.Disjoint, frameFloor_eq, frameExtent_eq] at hd2
    intro j hj
    obtain ⟨w, hw⟩ := inv.stwords j hj
    exact ⟨w, Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst hw (by rw [hbs]; omega)⟩

/-- **L1 closes, weakly.** From the loop head with the counter at zero, the
machine reaches the fallthrough at function offset 50 with the counter at 16,
the image still loaded, `block[]` intact and everything written inside the
footprint.

This is `reaches_loop_of_trace` at the weak invariant. Nothing here says what
`w[]` holds; that is the strengthening, and it reuses `l1_trace_data` — which
now pins the stored value — and extends `l1_preserve`.

Proved, with no `sorry`: `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`. -/
theorem l1_loop (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} (start : L1Inv L state block rspEntry m 0 cur) :
    ∃ fin, Reaches L.exit cur fin ∧ L1Inv L state block rspEntry m 16 fin := by
  refine Silmaril.X86.Ext.reaches_loop_of_trace
    (I := L1Inv L state block rspEntry m)
    (Q := L1Inv L state block rspEntry m 16)
    (Pre := fun i c => L1At L rspEntry state block (image L.textBase L.rodataBase) 32
        (BitVec.ofNat 64 i) c ∧ BlockWordsHold c.memory block ∧
        c.memory.Permitted .write (rspEntry.toNat - 312 + 4 * i) 4)
    (Effect := fun i c c' => L1Effect L rspEntry i c c')
    (N := 16) ?_ ?_ ?_ ?_ start
  · -- entry: the invariant supplies what the trace needs
    intro i hi c inv
    have hfits : (344 : Nat) ≤ rspEntry.toNat := by
      have := h.frameFits; rwa [frameExtent_eq] at this
    refine ⟨?_, inv.reads, ?_⟩
    · have := inv.at_
      rwa [show (if i < 16 then (32 : Nat) else 50) = 32 from
        ite_eq_left_of_eq_true _ _ (eq_true hi)] at this
    · rw [Silmaril.Process.Memory.WritesWithin.permitted_iff inv.frame]
      exact h.frame_writable (by omega) (by omega) (by omega)
  · -- trace
    intro i hi c pre
    exact l1_trace h hi pre.1 (pre.2.1 i hi) pre.2.2
  · -- preserve
    intro i hi c c' inv eff
    exact l1_preserve h hi inv eff
  · -- exit: nothing left to run
    intro c inv
    exact ⟨c, Silmaril.X86.Ext.Reaches.of_runs (Silmaril.X86.Ext.Runs.nil c), inv⟩

/-! ### L1, strongly: `w[t]` is the big-endian block word

The weak chain above is reused wholesale. `l1_trace_data` already pins the
value it stores, so the only new work is to say what that value *is* in the
spec's vocabulary, and to carry it across the loop.

Following Track 2c's `Keeps` pattern, the strengthening is **conjoined to the
invariant** rather than added as a field of it. That keeps `L1Inv`,
`L1Effect`, `l1_preserve` and `l1_loop` untouched, and the expensive six-step
trace is proved once and used at both strengths. -/

/-- The pinned trace: from a block word known to be `leWordAt bs i`, the
iteration stores `beWordAt bs i`.

This is `byteSwap32_leWordAt` applied at the one place it is needed. The
`setWidth` shuffle is the load's zero-extension to 64 bits and back. -/
theorem l1_trace_at (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} {i : Nat} {bs : List Silmaril.Process.Byte} (hi : i < 16)
    (hat : L1At L rspEntry state block (image L.textBase L.rodataBase) 32
      (BitVec.ofNat 64 i) cur)
    (hread : Silmaril.X86.Ext.HoldsLE cur.memory (block.toNat + 4 * i) 4
      ((leWordAt bs i).setWidth 64))
    (hwrite : cur.memory.Permitted .write (rspEntry.toNat - 312 + 4 * i) 4) :
    ∃ cur', Reaches L.exit cur cur' ∧ L1Effect L rspEntry i cur cur' ∧
      Stored cur.memory cur'.memory (rspEntry.toNat - 312 + 4 * i)
        (Silmaril.X86.Ext.leBytes ((beWordAt bs i).setWidth 64) 4) := by
  have hsl : ∀ o l : Nat, o + l ≤ relocOffset →
      ((image L.textBase L.rodataBase).drop o).take l = (raw.drop o).take l :=
    fun o l hb => image_slice _ _ hb
  obtain ⟨c4, r4, a4, hst⟩ := l1_trace_data h hi (image_length L.textBase L.rodataBase)
    (by rw [hsl 32 3 (by decide)]; exact l1_decode_load)
    (by rw [hsl 35 2 (by decide)]; exact l1_decode_bswap)
    (by rw [hsl 37 4 (by decide)]; exact l1_decode_store)
    (by rw [hsl 41 3 (by decide)]; exact l1_decode_inc) hat hread hwrite
  obtain ⟨c6, r6, h6rip, h6rax, h6rsp, h6rsi, h6rdi, h6mem⟩ :=
    l1_trace_branch hi (image_length L.textBase L.rodataBase)
      (by rw [hsl 44 4 (by decide)]; exact l1_decode_cmp)
      (by rw [hsl 48 2 (by decide)]; exact l1_decode_jne) a4
  have hval : (Silmaril.X86.Ext.byteSwap32
      (((leWordAt bs i).setWidth 64).setWidth 32)).setWidth 64
      = (beWordAt bs i).setWidth 64 := by
    rw [BitVec.setWidth_setWidth_of_le _ (by omega : (32 : Nat) ≤ 64), BitVec.setWidth_eq,
      byteSwap32_leWordAt]
  rw [hval] at hst
  refine ⟨c6, r4.trans r6, ?_, ?_⟩
  · refine { rip := h6rip, rax := h6rax, rsp := ?_, rsi := ?_, rdi := ?_, stored :=
      ⟨(beWordAt bs i).setWidth 64, ?_⟩ }
    · rw [h6rsp, a4.rsp]; exact hat.rsp.symm
    · rw [h6rsi, a4.rsi]; exact hat.rsi.symm
    · rw [h6rdi, a4.rdi]; exact hat.rdi.symm
    · rw [h6mem]; exact hst
  · rw [h6mem]; exact hst

/-- The pinned half of preservation: one more schedule word is pinned. The
weak half is `l1_preserve`, unchanged. -/
theorem l1_preserve_at (h : SysVEntry L state block rspEntry frameSize m)
    {i : Nat} (hi : i < 16) {cur cur' : MState} {bs : List Silmaril.Process.Byte}
    (inv : L1Inv L state block rspEntry m i cur)
    (hw : WWordsAt cur.memory rspEntry (fun j => (beWordAt bs j).setWidth 64) i)
    (hst : Stored cur.memory cur'.memory (rspEntry.toNat - 312 + 4 * i)
      (Silmaril.X86.Ext.leBytes ((beWordAt bs i).setWidth 64) 4)) :
    WWordsAt cur'.memory rspEntry (fun j => (beWordAt bs j).setWidth 64) (i + 1) := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  refine WWordsAt.succ (by omega) hw hst ?_
  rw [Silmaril.Process.Memory.WritesWithin.permitted_iff inv.frame]
  exact h.frame_readable (by omega) (by omega) (by omega)

/-- **L1 closes, strongly.** On exit the sixteen schedule slots hold the
sixteen big-endian words of `block[]` — which is exactly what `compressBlock`
feeds to `SHA256.Kernel.compress`.

The block word needed at each iteration is recovered from the footprint by
`blockBytes_preserved` rather than carried, so the invariant gains one
conjunct and no field. -/
theorem l1_loop_at (h : SysVEntry L state block rspEntry frameSize m)
    {bs : List Silmaril.Process.Byte}
    (hbs : m.memory.readBytes block.toNat 64 = some bs)
    {sv : Nat → SHA256.Kernel.Word} {cur : MState}
    (start : L1Inv L state block rspEntry m 0 cur) (hsw : StateWordsAt cur.memory state sv) :
    ∃ fin, Reaches L.exit cur fin ∧ L1Inv L state block rspEntry m 16 fin ∧
      WWordsAt fin.memory rspEntry (fun j => (beWordAt bs j).setWidth 64) 16 ∧
      StateWordsAt fin.memory state sv := by
  refine Silmaril.X86.Ext.reaches_loop_of_trace
    (I := fun i c => L1Inv L state block rspEntry m i c ∧
      WWordsAt c.memory rspEntry (fun j => (beWordAt bs j).setWidth 64) i ∧
      StateWordsAt c.memory state sv)
    (Q := fun c => L1Inv L state block rspEntry m 16 c ∧
      WWordsAt c.memory rspEntry (fun j => (beWordAt bs j).setWidth 64) 16 ∧
      StateWordsAt c.memory state sv)
    (Pre := fun i c => L1At L rspEntry state block (image L.textBase L.rodataBase) 32
        (BitVec.ofNat 64 i) c ∧
        Silmaril.X86.Ext.HoldsLE c.memory (block.toNat + 4 * i) 4
          ((leWordAt bs i).setWidth 64) ∧
        c.memory.Permitted .write (rspEntry.toNat - 312 + 4 * i) 4)
    (Effect := fun i c c' => L1Effect L rspEntry i c c' ∧
      Stored c.memory c'.memory (rspEntry.toNat - 312 + 4 * i)
        (Silmaril.X86.Ext.leBytes ((beWordAt bs i).setWidth 64) 4))
    (N := 16) ?_ ?_ ?_ ?_ ⟨start, fun j hj => absurd hj (Nat.not_lt_zero j), hsw⟩
  · intro i hi c inv
    have hfits : (344 : Nat) ≤ rspEntry.toNat := by
      have := h.frameFits; rwa [frameExtent_eq] at this
    refine ⟨?_, ?_, ?_⟩
    · have := inv.1.at_
      rwa [show (if i < 16 then (32 : Nat) else 50) = 32 from
        ite_eq_left_of_eq_true _ _ (eq_true hi)] at this
    · exact holdsLE_blockWord (blockBytes_preserved h inv.1.frame hbs) hi
    · rw [Silmaril.Process.Memory.WritesWithin.permitted_iff inv.1.frame]
      exact h.frame_writable (by omega) (by omega) (by omega)
  · intro i hi c pre
    obtain ⟨c', r, eff, hst⟩ := l1_trace_at h hi pre.1 pre.2.1 pre.2.2
    exact ⟨c', r, eff, hst⟩
  · intro i hi c c' inv eff
    refine ⟨l1_preserve h hi inv.1 eff.1, l1_preserve_at h hi inv.1 inv.2.1 eff.2, ?_⟩
    obtain ⟨sval, hst⟩ := eff.1.stored
    have hbs2 : (Silmaril.X86.Ext.leBytes sval 4).length = 4 :=
      Silmaril.X86.Ext.length_leBytes _ _
    have hd2 := h.state_disjoint_frame
    simp only [stateRegion, frameRegion, Region.Disjoint, frameFloor_eq, frameExtent_eq] at hd2
    have hfits : (344 : Nat) ≤ rspEntry.toNat := by
      have := h.frameFits; rwa [frameExtent_eq] at this
    intro j hj
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst (inv.2.2 j hj) (by rw [hbs2]; omega)
  · intro c inv
    exact ⟨c, Silmaril.X86.Ext.Reaches.of_runs (Silmaril.X86.Ext.Runs.nil c), inv⟩

/-! ### L2's four `%rsp`-indexed slots

All four are `disp(%rsp,%rax,4)` with `%rax = t`; the displacement selects
which word. With `%rsp = rspEntry - 216` and `w[j]` at `rspEntry - 312 + 4j`,
a displacement of `-(96 + 4k)` names `w[t - k]`. -/

/-- `-0x9c(%rsp,%rax,4)` = `w[t-15]`. -/
def l2W15Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := some { reg := .rax, scale := 2#2, ne_rsp := by decide },
    disp := 0xffffff64#32, rip_no_index := by intro hc; exact absurd hc (by decide) }

/-- `-0x68(%rsp,%rax,4)` = `w[t-2]`. -/
def l2W2Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := some { reg := .rax, scale := 2#2, ne_rsp := by decide },
    disp := 0xffffff98#32, rip_no_index := by intro hc; exact absurd hc (by decide) }

/-- `-0x7c(%rsp,%rax,4)` = `w[t-7]`. -/
def l2W7Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := some { reg := .rax, scale := 2#2, ne_rsp := by decide },
    disp := 0xffffff84#32, rip_no_index := by intro hc; exact absurd hc (by decide) }

/-- `-0x60(%rsp,%rax,4)` = `w[t]`. -/
def l2WtMem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := some { reg := .rax, scale := 2#2, ne_rsp := by decide },
    disp := 0xffffffa0#32, rip_no_index := by intro hc; exact absurd hc (by decide) }

/-- The effective address of one of L2's four slots. `k` is the lag: `0` for
`w[t]`, `2`, `7` or `15` for the three it reads. -/
theorem l2Slot_addr {cur : MState} {mm : Silmaril.X86.Ext.Mem} {t k : Nat}
    (hk : k ≤ t) (ht : t < 64) (hfits : (344 : Nat) ≤ rspEntry.toNat)
    (hdisp : (mm.disp.signExtend 64) = BitVec.ofNat 64 (2 ^ 64 - (96 + 4 * k)))
    (hbase : mm.base = .reg .rsp)
    (hindex : mm.index = some { reg := .rax, scale := 2#2, ne_rsp := by decide })
    (hrax : cur.core.read .rax = BitVec.ofNat 64 t)
    (hrsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216)
    (next : Word) :
    (mm.addr cur.core next).toNat = rspEntry.toNat - 312 + 4 * (t - k) := by
  have hlt := rspEntry.isLt
  have hbaseNat : (rspEntry - BitVec.ofNat 64 216).toNat = rspEntry.toNat - 216 :=
    Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := 216) (by omega) (by omega)
  simp only [Silmaril.X86.Ext.Mem.addr, hbase, hindex, Silmaril.X86.Ext.Base.value_reg,
    Option.map_some, Option.getD_some, Silmaril.X86.Ext.Index.value, hrax, hrsp, hdisp]
  rw [show (2#2 : BitVec 2).toNat = 2 from rfl, shiftLeft_two t (by omega)]
  -- the whole sum, reduced modulo 2^64 once, so no intermediate can overflow
  have hsum : ((rspEntry - BitVec.ofNat 64 216) + BitVec.ofNat 64 (4 * t)
        + BitVec.ofNat 64 (2 ^ 64 - (96 + 4 * k))).toNat
      = (rspEntry.toNat - 216 + 4 * t + (2 ^ 64 - (96 + 4 * k))) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hbaseNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 4 * t < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 2 ^ 64 - (96 + 4 * k) < 2 ^ 64 by omega)]
    rw [Nat.mod_add_mod]
  rw [hsum]
  omega

/-! ### The twenty-five decode facts of L2 -/

set_option maxRecDepth 8000 in
/-- `64`, 7 bytes. -/
theorem l2_decode_64 : decode ((raw.drop 64).take 7)
    = some (.load .d .rcx l2W15Mem, 7) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `71`, 4 bytes. -/
theorem l2_decode_71 : decode ((raw.drop 71).take 4)
    = some (.load .d .rsi l2W2Mem, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `75`, 3 bytes. -/
theorem l2_decode_75 : decode ((raw.drop 75).take 3)
    = some (.mov .d (.reg .r8) .rcx, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `78`, 4 bytes. -/
theorem l2_decode_78 : decode ((raw.drop 78).take 4)
    = some (.shift .d .rol (.reg .r8) (.imm 0x19#8), 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `82`, 3 bytes. -/
theorem l2_decode_82 : decode ((raw.drop 82).take 3)
    = some (.mov .d (.reg .r9) .rcx, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `85`, 4 bytes. -/
theorem l2_decode_85 : decode ((raw.drop 85).take 4)
    = some (.shift .d .rol (.reg .r9) (.imm 0x0e#8), 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `89`, 3 bytes. -/
theorem l2_decode_89 : decode ((raw.drop 89).take 3)
    = some (.alu .d .xor (.reg .r9) .r8, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `92`, 3 bytes. -/
theorem l2_decode_92 : decode ((raw.drop 92).take 3)
    = some (.mov .d (.reg .r8) .rcx, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `95`, 4 bytes. -/
theorem l2_decode_95 : decode ((raw.drop 95).take 4)
    = some (.shift .d .shr (.reg .r8) (.imm 0x03#8), 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `99`, 3 bytes. -/
theorem l2_decode_99 : decode ((raw.drop 99).take 3)
    = some (.alu .d .xor (.reg .r8) .r9, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `102`, 3 bytes. -/
theorem l2_decode_102 : decode ((raw.drop 102).take 3)
    = some (.alu .d .add (.reg .r8) .rdx, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `105`, 2 bytes. -/
theorem l2_decode_105 : decode ((raw.drop 105).take 2)
    = some (.mov .d (.reg .rdx) .rsi, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `107`, 3 bytes. -/
theorem l2_decode_107 : decode ((raw.drop 107).take 3)
    = some (.shift .d .rol (.reg .rdx) (.imm 0x0f#8), 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `110`, 3 bytes. -/
theorem l2_decode_110 : decode ((raw.drop 110).take 3)
    = some (.mov .d (.reg .r9) .rsi, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `113`, 4 bytes. -/
theorem l2_decode_113 : decode ((raw.drop 113).take 4)
    = some (.shift .d .rol (.reg .r9) (.imm 0x0d#8), 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `117`, 3 bytes. -/
theorem l2_decode_117 : decode ((raw.drop 117).take 3)
    = some (.alu .d .xor (.reg .r9) .rdx, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `120`, 3 bytes. -/
theorem l2_decode_120 : decode ((raw.drop 120).take 3)
    = some (.shift .d .shr (.reg .rsi) (.imm 0x0a#8), 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `123`, 3 bytes. -/
theorem l2_decode_123 : decode ((raw.drop 123).take 3)
    = some (.alu .d .xor (.reg .rsi) .r9, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `126`, 5 bytes. -/
theorem l2_decode_126 : decode ((raw.drop 126).take 5)
    = some (.aluR .d .add .r8 (.mem l2W7Mem), 5) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `131`, 3 bytes. -/
theorem l2_decode_131 : decode ((raw.drop 131).take 3)
    = some (.alu .d .add (.reg .r8) .rsi, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `134`, 5 bytes. -/
theorem l2_decode_134 : decode ((raw.drop 134).take 5)
    = some (.mov .d (.mem l2WtMem) .r8, 5) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `139`, 3 bytes. -/
theorem l2_decode_139 : decode ((raw.drop 139).take 3)
    = some (.incdec .q false (.reg .rax), 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `142`, 2 bytes. -/
theorem l2_decode_142 : decode ((raw.drop 142).take 2)
    = some (.mov .d (.reg .rdx) .rcx, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `144`, 4 bytes. -/
theorem l2_decode_144 : decode ((raw.drop 144).take 4)
    = some (.aluI8 .q .cmp (.reg .rax) 0x40#8, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `148`, 2 bytes. -/
theorem l2_decode_148 : decode ((raw.drop 148).take 2)
    = some (.jcc8 .ne 0xaa#8, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `17: 31 c0` — `xor %eax,%eax`. -/
theorem blockA0_decode_17 : decode ((raw.drop 17).take 2)
    = some (.alu .d .xor (.reg .rax) .rax, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `19`: the thirteen-byte NOP, four `66` prefixes and a `2E` override. -/
theorem blockA0_decode_19 : decode ((raw.drop 19).take 13)
    = some (.nop 12, 13) :=
  decode_raw (by decide +kernel)

/-! ## The straight-line blocks between the loops

Four of them: `17…32` after the prologue, `50…64` between L1 and L2,
`150…224` between L2 and L3, and `374…441` before the epilogue. Together they
are 39 instructions and they are what stands between the five proved pieces
and `Live`. -/

set_option maxRecDepth 8000 in
/-- `17: xor %eax,%eax` and the 13-byte NOP: the counter is zeroed and control
arrives at L1's head. -/
theorem blockA0 {sv : Nat → SHA256.Kernel.Word} {cur : MState}
    (hargs : cur.core.read .rsi = block) (hrdi : cur.core.read .rdi = state)
    (hs : PrologueState L state block rspEntry m sv frameSize 17 cur) :
    ∃ cur', Reaches L.exit cur cur' ∧
      L1At L rspEntry state block (image L.textBase L.rodataBase) 32 (BitVec.ofNat 64 0) cur' ∧
      cur'.memory = cur.memory := by
  obtain ⟨c1, s1, h1rip, h1w, _, h1mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 17) (len := 2)
      hs.loaded hs.rip (by rw [image_length]; decide)
      (by rw [image_slice _ _ (by decide : 17 + 2 ≤ relocOffset)]; exact blockA0_decode_17)
      (by decide) rfl
  obtain ⟨c2, s2, h2rip, h2regs, _, h2mem⟩ :=
    stepOpt_nop (exit := L.exit) (offset := 19) (len := 13)
      (h1mem ▸ hs.loaded) h1rip (by rw [image_length]; decide)
      (by rw [image_slice _ _ (by decide : 19 + 13 ≤ relocOffset)]; exact blockA0_decode_19)
  refine ⟨c2, Reaches.cons s1 (Reaches.one s2), ⟨h2rip, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [h2mem, h1mem]⟩
  · rw [h2regs _, h1w.target]
    show (Silmaril.X86.Ext.AluOp.resultN Silmaril.X86.AluOp.xor
      (Silmaril.X86.Ext.Sz.d.read cur.core Reg.rax)
      (Silmaril.X86.Ext.Sz.d.read cur.core Reg.rax)).setWidth 64 = _
    show ((Silmaril.X86.Ext.Sz.d.read cur.core Reg.rax) ^^^
      (Silmaril.X86.Ext.Sz.d.read cur.core Reg.rax)).setWidth 64 = _
    rw [BitVec.xor_self]
    rfl
  · rw [h2regs _, h1w.other _ (by decide)]; exact hs.rsp
  · rw [h2regs _, h1w.other _ (by decide)]; exact hargs
  · rw [h2regs _, h1w.other _ (by decide)]; exact hrdi
  · rw [h2mem, h1mem]; exact hs.loaded

/-- `-0x60(%rsp)` with no index: the `w[0]` preload. -/
def blockAW0Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := Option.none, disp := 0xffffffa0#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }

set_option maxRecDepth 8000 in
/-- `50: b8 10 00 00 00` — `mov $0x10,%eax`. -/
theorem blockA_decode_50 : decode ((raw.drop 50).take 5)
    = some (.movI32 .rax 0x00000010#32, 5) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `55: 8b 54 24 a0` — `mov -0x60(%rsp),%edx`, the `w[0]` preload. -/
theorem blockA_decode_55 : decode ((raw.drop 55).take 4)
    = some (.load .d .rdx blockAW0Mem, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `59: 0f 1f 44 00 00` — the five-byte NOP. -/
theorem blockA_decode_59 : decode ((raw.drop 59).take 5)
    = some (.nop 4, 5) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- The effective address of `-off(%rsp)` with no index: the spill slots
`a…h` at `-0x80 … -0x64(%rsp)` and the `w[0]` preload at `-0x60(%rsp)` are all
of this shape. -/
theorem rspOnly_addr {cur : MState} {mm : Silmaril.X86.Ext.Mem} {off : Nat}
    (hfits : (344 : Nat) ≤ rspEntry.toNat) (hle : off ≤ 128)
    (hbase : mm.base = .reg .rsp) (hindex : mm.index = Option.none)
    (hdisp : mm.disp.signExtend 64 = BitVec.ofNat 64 (2 ^ 64 - off))
    (hpos : 0 < off)
    (hrsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216) (next : Word) :
    (mm.addr cur.core next).toNat = rspEntry.toNat - 216 - off := by
  have hlt := rspEntry.isLt
  have hbaseNat : (rspEntry - BitVec.ofNat 64 216).toNat = rspEntry.toNat - 216 :=
    Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := 216) (by omega) (by omega)
  simp only [Silmaril.X86.Ext.Mem.addr, hbase, hindex, Silmaril.X86.Ext.Base.value_reg,
    Option.map_none, Option.getD_none, hrsp, hdisp, BitVec.add_zero]
  rw [BitVec.toNat_add, hbaseNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 64 - off < 2 ^ 64 by omega)]
  omega

/-- **`rol j` is `ror (32 - j)`.** The compiled code rotates left; the
specification rotates right. `BitVec.rotateLeft_def` and `rotateRight_def`
expand to the same two shifts in the opposite order, so the whole crossing is
`|||` commutativity. -/
theorem rotateLeft_eq_rotateRight (x : SHA256.Kernel.Word) {j : Nat}
    (h0 : 0 < j) (h32 : j < 32) :
    x.rotateLeft j = x.rotateRight (32 - j) := by
  rw [BitVec.rotateLeft_def, BitVec.rotateRight_def,
    Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt (show 32 - j < 32 by omega),
    show 32 - (32 - j) = j by omega]
  exact BitVec.or_comm _ _

/-! ### Reading a 32-bit register across a step

L3's forty-six register writes each arrive as a `WritesReg`, whose value is
stated at 64 bits as `(v : BitVec 32).setWidth 64` because that is how x86
writes a 32-bit register. Every operand is then read back at 32 bits. These
two lemmas do that round trip once, so the round-state chain below is a
sequence of rewrites rather than a sequence of `setWidth` shuffles. -/

/-- **A 32-bit register read, at the specification's width.**

`Sz.d.read` has type `BitVec Sz.d.bits`. That is *definitionally* `BitVec 32`,
but `Sz.bits` is not reducible, so instance resolution will not see through it:
`h + Sigma1 e` fails to elaborate when `h` comes from a register and
`Sigma1 e` from the specification.

Putting the coercion at the **read** — rather than ascribing at each use — is
what lets the round state speak the specification's vocabulary throughout.
Ascribing at the use fixes the specification side and breaks the machine side;
ascribing the entry values does the reverse. Normalising at the boundary is the
third option, and it is the one that works. This is the third time this file has
met the `Sz.d.bits` versus `32` boundary, which is why it gets a name rather
than another local `show`. -/
def read32 (s : Silmaril.X86.State) (r : Reg) : SHA256.Kernel.Word :=
  (s.read r).setWidth 32

/-- `read32` is the machine's own 32-bit read; the two differ only in how their
type is spelled. -/
theorem read32_eq (s : Silmaril.X86.State) (r : Reg) :
    read32 s r = Silmaril.X86.Ext.Sz.d.read s r := rfl

/-- The written register, read back at 32 bits. -/
theorem read_d_of_writes {before after : Silmaril.X86.State} {dst : Reg} {v : BitVec 32}
    (h : Silmaril.X86.Ext.WritesReg before after dst (v.setWidth 64)) :
    read32 after dst = v := by
  show (after.read dst).setWidth 32 = v
  rw [h.target, BitVec.setWidth_setWidth_of_le _ (by omega : (32 : Nat) ≤ 64),
    BitVec.setWidth_eq]

/-- A step that writes no register leaves every 32-bit read alone. -/
theorem read32_of_sameRegs {before after : Silmaril.X86.State}
    (h : Silmaril.X86.Ext.SameRegs before after) (r : Reg) :
    read32 after r = read32 before r := by
  show (after.read r).setWidth 32 = (before.read r).setWidth 32
  rw [h r]

/-- Any other register, read back at 32 bits, is unchanged. -/
theorem read_d_of_other {before after : Silmaril.X86.State} {dst r : Reg} {v : Word}
    (h : Silmaril.X86.Ext.WritesReg before after dst v) (hne : r ≠ dst) :
    read32 after r = read32 before r := by
  show (after.read r).setWidth 32 = (before.read r).setWidth 32
  rw [h.other r hne]

/-- **One schedule iteration, in the specification's vocabulary.** The word
stored, and the register carried to the next iteration.

The carried term is written as `read32 cur.core .rdx` rather than as `W i`: the
trace does not know what the carried register holds, and does not need to. The
loop supplies that. -/
def ScheduleOut (rspEntry : Word) (W : Nat → SHA256.Kernel.Word) (i : Nat)
    (cur cur' : MState) : Prop :=
  read32 cur'.core .rdx = W (16 + i - 15) ∧
    Stored cur.memory cur'.memory (rspEntry.toNat - 312 + 4 * (16 + i))
      (Silmaril.X86.Ext.leBytes
        ((SHA256.Kernel.sigma1 (W (16 + i - 2)) + W (16 + i - 7)
          + SHA256.Kernel.sigma0 (W (16 + i - 15)) + read32 cur.core .rdx).setWidth 64) 4)

/-- **The round state, in the registers.** Oriented with the specification's
state on the left, so that rewriting with it puts the machine's registers where
`roundStep` expects them — which is what keeps `Prod.mk.injEq` out of the
induction entirely. -/
def RoundState (st : SHA256.Kernel.State) (cur : MState) : Prop :=
  st = (read32 cur.core .r12, read32 cur.core .r8, read32 cur.core .rdx,
        read32 cur.core .r11, read32 cur.core .r13, read32 cur.core .rsi,
        read32 cur.core .rbp, read32 cur.core .r14)

/-! ### L2's mathematics: two sigmas and a reassociation

Three small identities, the same shape as L3's four. Note these are the
*lowercase* schedule sigmas, not the round's `Sigma0`/`Sigma1`: different
rotate amounts, and a `shr` where the round has a third rotate. -/

/-- `sigma0` as the object computes it: `rol 25`, `rol 14`, `xor`, `shr 3`,
`xor`. -/
theorem sigma0_eq_object (x : SHA256.Kernel.Word) :
    ((x >>> 3) ^^^ ((x.rotateLeft 14) ^^^ (x.rotateLeft 25))) = SHA256.Kernel.sigma0 x := by
  rw [rotateLeft_eq_rotateRight x (by omega) (by omega),
    rotateLeft_eq_rotateRight x (by omega) (by omega)]
  simp only [show (32 : Nat) - 14 = 18 from rfl, show (32 : Nat) - 25 = 7 from rfl,
    SHA256.Kernel.sigma0]
  ac_rfl

/-- `sigma1` as the object computes it: `rol 15`, `rol 13`, `xor`, `shr 10`,
`xor`. -/
theorem sigma1_eq_object (x : SHA256.Kernel.Word) :
    ((x >>> 10) ^^^ ((x.rotateLeft 13) ^^^ (x.rotateLeft 15))) = SHA256.Kernel.sigma1 x := by
  rw [rotateLeft_eq_rotateRight x (by omega) (by omega),
    rotateLeft_eq_rotateRight x (by omega) (by omega)]
  simp only [show (32 : Nat) - 13 = 19 from rfl, show (32 : Nat) - 15 = 17 from rfl,
    SHA256.Kernel.sigma1]
  ac_rfl

/-- **The schedule sum, reassociated.** The object accumulates
`((sigma0 (w[t-15]) + w[t-16]) + w[t-7]) + sigma1 (w[t-2])`; FIPS and
`messageSchedule_succ` write `sigma1 (w[t-2]) + w[t-7] + sigma0 (w[t-15]) +
w[t-16]`. The same four terms in a different order.

Worth recording that this is a **third** order: the `-O0` image accumulates
`w[t-16] + sigma0 + w[t-7] + sigma1`, FIPS a fourth. Each compiler picks the
order its scheduler likes and none of them is the specification's, so the
reassociation is not an artifact of one image. It is one line here only
because `ac_rfl` is available in this import closure. -/
theorem schedule_sum_comm (a b c d : SHA256.Kernel.Word) :
    a + b + c + d = d + c + a + b := by ac_rfl

/-- The sixteen big-endian words of a block, as the specification spells them. -/
def blockMsg (bb : List Silmaril.Process.Byte) : List SHA256.Kernel.Word :=
  [beWordAt bb 0, beWordAt bb 1, beWordAt bb 2, beWordAt bb 3,
   beWordAt bb 4, beWordAt bb 5, beWordAt bb 6, beWordAt bb 7,
   beWordAt bb 8, beWordAt bb 9, beWordAt bb 10, beWordAt bb 11,
   beWordAt bb 12, beWordAt bb 13, beWordAt bb 14, beWordAt bb 15]

/-- This block's message schedule, as an indexed function. -/
def blockSchedule (bb : List Silmaril.Process.Byte) : Nat → SHA256.Kernel.Word :=
  fun j => (SHA256.Kernel.messageSchedule (blockMsg bb)).getD j 0

theorem blockSchedule_lt (bb : List Silmaril.Process.Byte) {j : Nat} (hj : j < 16) :
    blockSchedule bb j = beWordAt bb j := by
  rw [blockSchedule, SHA256.Kernel.messageSchedule_getD_of_lt _ hj,
    SHA256.Kernel.blockWords_eq_self (by rfl)]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
      j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- The definitional unfolding, kept as a lemma because `blockSchedule` is
sealed below. -/
theorem blockSchedule_def (bb : List Silmaril.Process.Byte) (j : Nat) :
    blockSchedule bb j = (SHA256.Kernel.messageSchedule (blockMsg bb)).getD j 0 := rfl

theorem blockSchedule_succ (bb : List Silmaril.Process.Byte) {j : Nat}
    (h16 : 16 ≤ j) (h64 : j < 64) :
    blockSchedule bb j = SHA256.Kernel.sigma1 (blockSchedule bb (j - 2)) + blockSchedule bb (j - 7)
      + SHA256.Kernel.sigma0 (blockSchedule bb (j - 15)) + blockSchedule bb (j - 16) :=
  SHA256.Kernel.messageSchedule_getD (blockMsg bb) h16 h64

-- **Sealed.** Unfolding `blockSchedule` forces `expandSchedule 48`, which whnf
-- will happily attempt, and which costs more than the entire rest of this file.
-- Everything downstream goes through `blockSchedule_def`, `blockSchedule_lt`
-- and `blockSchedule_succ`.
attribute [irreducible] blockSchedule

-- Likewise: `roundsUpTo f st 64` unfolds sixty-four levels deep, each level a
-- full symbolic `round`. Every use goes through `roundsUpTo_succ`,
-- `roundsUpTo_zero` or `roundsUpTo_64`, all of which are already proved.
attribute [local irreducible] SHA256.Kernel.roundsUpTo

/-! ## L2: the message schedule

```
  64:  mov -0x9c(%rsp,%rax,4),%ecx      w[t-15]
  71:  mov -0x68(%rsp,%rax,4),%esi      w[t-2]
  …    sigma0 on %ecx, sigma1 on %esi, via rol/shr/xor
 102:  add %edx,%r8d                    <- the carried w[t-16]
 126:  add -0x7c(%rsp,%rax,4),%r8d      w[t-7]
 134:  mov %r8d,-0x60(%rsp,%rax,4)      w[t]
 139:  inc %rax
 142:  mov %ecx,%edx                    <- carry w[t-15] for the next iteration
 144:  cmp $0x40,%rax
 148:  jne 64
```

Twenty-five instructions, `t = 16 … 63`, indexed here by `i = t − 16` so that
the trip count is `N = 48` as `reaches_loop_of_trace` wants.

**The software pipelining does not appear in the weak invariant.** `%edx`
holds `w[t-16]` at the loop head — preloaded with `w[0]` before the loop and
re-established by `mov %ecx,%edx` at offset 142, since `%ecx` is `w[t-15]`,
which is `w[(t+1)-16]` for the next iteration. That is the one genuinely new
thing about this loop, and it is *invisible* at the weak level: reading a
register cannot fault, so liveness never needs to know what `%edx` holds. The
carried register is a strengthening-only obligation.

**What L2 does need that L1 did not** is `WWordsRead`: it reads `w[t-15]`,
`w[t-7]` and `w[t-2]`, so every word L1 and the earlier iterations wrote must
read back. That is why `L1Inv` carries `WWordsRead` too — the two loops' weak
invariants compose, and L1's would otherwise be too weak to start L2.

Note also that `%rsi` is *scratch* here (it holds `w[t-2]`), so `block` is
dead after L1 and `L2At` does not mention it. -/

/-- Where L2 is: RIP, the counter, the stack pointer, the loaded image. No
`%rsi` — it is scratch in this loop — and no `%edx`, which the weak invariant
does not need. -/
structure L2At (L : Layout) (rspEntry st : Word) (img : List Byte) (off : Nat) (rax : Word)
    (cur : MState) : Prop where
  /-- RIP is at function offset `off`. -/
  rip : cur.core.rip = L.textBase + BitVec.ofNat 64 off
  /-- The counter. -/
  rax : cur.core.read .rax = rax
  /-- The frame is open. -/
  rsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216
  /-- The output pointer. -/
  rdi : cur.core.read .rdi = st
  /-- The image is still loaded; `img` is a parameter for the reason in the
  module doc. -/
  loaded : Loaded cur.memory L.textBase img

/-- What one iteration of L2 does, said without reference to any invariant. -/
structure L2Effect (L : Layout) (rspEntry : Word) (i : Nat) (cur cur' : MState) : Prop where
  /-- Back to the loop head, or out to the fallthrough on the last iteration. -/
  rip : cur'.core.rip = L.textBase + BitVec.ofNat 64 (if i + 1 < 48 then 64 else 150)
  /-- The counter advanced. -/
  rax : cur'.core.read .rax = BitVec.ofNat 64 (16 + i + 1)
  /-- The stack pointer is untouched. -/
  rsp : cur'.core.read .rsp = cur.core.read .rsp
  /-- The output pointer is untouched. -/
  rdi : cur'.core.read .rdi = cur.core.read .rdi
  /-- Exactly the four bytes of `w[16 + i]` were written. -/
  stored : ∃ v : Word, Stored cur.memory cur'.memory (rspEntry.toNat - 312 + 4 * (16 + i))
    (Silmaril.X86.Ext.leBytes v 4)

/-- The **weak** L2 invariant after `i` iterations, i.e. at `t = 16 + i`. -/
structure L2Inv (L : Layout) (state rspEntry : Word) (entry : MState)
    (i : Nat) (cur : MState) : Prop where
  /-- The counter has not run past the trip count. -/
  bound : i ≤ 48
  /-- RIP is a function of the index: the head at `i < 48`, the fallthrough at
  `i = 48`, because this loop is bottom-tested. -/
  at_ : L2At L rspEntry state (image L.textBase L.rodataBase)
          (if i < 48 then 64 else 150) (BitVec.ofNat 64 (16 + i)) cur
  /-- Everything written so far is inside the modifies set. -/
  frame : Memory.WritesWithin entry.memory cur.memory (Footprint state rspEntry frameSize)
  /-- The `16 + i` words written so far read back. -/
  words : WWordsRead cur.memory rspEntry (16 + i)
  /-- The six callee-saved slots still read. -/
  saved : SavedSlotsAt cur.memory rspEntry (fun j => entry.core.read (savedReg j))
  /-- `state[]` still reads. -/
  stwords : StateWordsHold cur.memory state

/-- Where the L2 trace is partway through: RIP, the counter, the frame
pointer, and that memory has not changed since `base`. The scratch registers
are not tracked — the weak invariant does not need them, and that includes the
carried `%edx`. -/
structure L2Mid (L : Layout) (rspEntry st : Word) (off t : Nat) (base cur : MState) : Prop where
  /-- RIP is at function offset `off`. -/
  rip : cur.core.rip = L.textBase + BitVec.ofNat 64 off
  /-- The counter. -/
  rax : cur.core.read .rax = BitVec.ofNat 64 t
  /-- The frame is open. -/
  rsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216
  /-- The output pointer. -/
  rdi : cur.core.read .rdi = st
  /-- Memory is untouched so far. -/
  mem : cur.memory = base.memory

/-- Advance `L2Mid` across a step that writes one scratch register and no
memory. Sixteen of L2's twenty-five instructions are of this shape. -/
theorem L2Mid.regStep {off len t : Nat} {base cur next : MState} {dst : Reg} {v : Word}
    (hs : L2Mid L rspEntry state off t base cur)
    (hrip : next.core.rip = L.textBase + BitVec.ofNat 64 (off + len))
    (hw : Silmaril.X86.Ext.WritesReg cur.core next.core dst v)
    (hmem : next.memory = cur.memory)
    (hd1 : Reg.rax ≠ dst) (hd2 : Reg.rsp ≠ dst) (hd3 : Reg.rdi ≠ dst) :
    L2Mid L rspEntry state (off + len) t base next where
  rip := hrip
  rax := by rw [hw.other _ hd1]; exact hs.rax
  rsp := by rw [hw.other _ hd2]; exact hs.rsp
  rdi := by rw [hw.other _ hd3]; exact hs.rdi
  mem := by rw [hmem]; exact hs.mem

set_option maxRecDepth 8000 in
/-- L2's `jne` backedge: the fallthrough at function offset 150 plus the
sign-extended rel8 `0xaa` (−86) is the loop head at 64. -/
theorem l2_backedge (textBase : Word) :
    textBase + BitVec.ofNat 64 (148 + 2) + (0xaa#8 : BitVec 8).signExtend 64
      = textBase + BitVec.ofNat 64 64 := by
  rw [show ((0xaa#8 : BitVec 8).signExtend 64) = BitVec.ofNat 64 (2 ^ 64 - 86) from rfl,
    add_assoc, Silmaril.X86.Ext.ofNat_add_ofNat]
  congr 1

set_option maxRecDepth 8000 in
/-- L2's counter, as a word, is `64` exactly when it is `64` as a number. -/
theorem l2_counter_ne {i : Nat} (hi : i < 48) :
    (BitVec.ofNat 64 (16 + i + 1) ≠ BitVec.ofNat 64 64) ↔ (16 + i + 1 ≠ 64) :=
  ofNat_ne_ofNat (by omega) (by omega)

set_option maxRecDepth 8000 in
/-- **The L2 trace**, over an abstract image. One iteration of the schedule
loop, stated without reference to any invariant.

Twenty-five steps, every one through an opaque-successor lemma, and `img` a
parameter rather than the 459-byte literal. Sixteen of the steps write one
scratch register and no memory, and go through `L2Mid.regStep`.

Sixteen of the steps write one scratch register and no memory and go through
`L2Mid.regStep`; the carried `%edx` is written at offset 142 and never
mentioned, because the weak invariant does not need it. -/
theorem l2_trace_img (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} {i : Nat} {img : List Byte} (hi : i < 48)
    (himg : img.length = size)
    (d64 : decode ((img.drop 64).take 7) = some (.load .d .rcx l2W15Mem, 7))
    (d71 : decode ((img.drop 71).take 4) = some (.load .d .rsi l2W2Mem, 4))
    (d75 : decode ((img.drop 75).take 3) = some (.mov .d (.reg .r8) .rcx, 3))
    (d78 : decode ((img.drop 78).take 4) = some (.shift .d .rol (.reg .r8) (.imm 0x19#8), 4))
    (d82 : decode ((img.drop 82).take 3) = some (.mov .d (.reg .r9) .rcx, 3))
    (d85 : decode ((img.drop 85).take 4) = some (.shift .d .rol (.reg .r9) (.imm 0x0e#8), 4))
    (d89 : decode ((img.drop 89).take 3) = some (.alu .d .xor (.reg .r9) .r8, 3))
    (d92 : decode ((img.drop 92).take 3) = some (.mov .d (.reg .r8) .rcx, 3))
    (d95 : decode ((img.drop 95).take 4) = some (.shift .d .shr (.reg .r8) (.imm 0x03#8), 4))
    (d99 : decode ((img.drop 99).take 3) = some (.alu .d .xor (.reg .r8) .r9, 3))
    (d102 : decode ((img.drop 102).take 3) = some (.alu .d .add (.reg .r8) .rdx, 3))
    (d105 : decode ((img.drop 105).take 2) = some (.mov .d (.reg .rdx) .rsi, 2))
    (d107 : decode ((img.drop 107).take 3) = some (.shift .d .rol (.reg .rdx) (.imm 0x0f#8), 3))
    (d110 : decode ((img.drop 110).take 3) = some (.mov .d (.reg .r9) .rsi, 3))
    (d113 : decode ((img.drop 113).take 4) = some (.shift .d .rol (.reg .r9) (.imm 0x0d#8), 4))
    (d117 : decode ((img.drop 117).take 3) = some (.alu .d .xor (.reg .r9) .rdx, 3))
    (d120 : decode ((img.drop 120).take 3) = some (.shift .d .shr (.reg .rsi) (.imm 0x0a#8), 3))
    (d123 : decode ((img.drop 123).take 3) = some (.alu .d .xor (.reg .rsi) .r9, 3))
    (d126 : decode ((img.drop 126).take 5) = some (.aluR .d .add .r8 (.mem l2W7Mem), 5))
    (d131 : decode ((img.drop 131).take 3) = some (.alu .d .add (.reg .r8) .rsi, 3))
    (d134 : decode ((img.drop 134).take 5) = some (.mov .d (.mem l2WtMem) .r8, 5))
    (d139 : decode ((img.drop 139).take 3) = some (.incdec .q false (.reg .rax), 3))
    (d142 : decode ((img.drop 142).take 2) = some (.mov .d (.reg .rdx) .rcx, 2))
    (d144 : decode ((img.drop 144).take 4) = some (.aluI8 .q .cmp (.reg .rax) 0x40#8, 4))
    (d148 : decode ((img.drop 148).take 2) = some (.jcc8 .ne 0xaa#8, 2))
    (hat : L2At L rspEntry state img 64 (BitVec.ofNat 64 (16 + i)) cur)
    {W : Nat → SHA256.Kernel.Word}
    (hwords : WWordsAt cur.memory rspEntry (fun j => (W j).setWidth 64) (16 + i))
    (hwrite : cur.memory.Permitted .write (rspEntry.toNat - 312 + 4 * (16 + i)) 4) :
    ∃ cur', Reaches L.exit cur cur' ∧ L2Effect L rspEntry i cur cur' ∧
      ScheduleOut rspEntry W i cur cur' := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hld : ∀ {c : MState}, c.memory = cur.memory → Loaded c.memory L.textBase img :=
    fun hm => hm ▸ hat.loaded
  have hv15 := hwords (16 + i - 15) (by omega)
  have hv2 := hwords (16 + i - 2) (by omega)
  have hv7 := hwords (16 + i - 7) (by omega)
  have a0 : L2Mid L rspEntry state 64 (16 + i) cur cur :=
    { rip := hat.rip, rax := hat.rax, rsp := hat.rsp, rdi := hat.rdi, mem := rfl }
  obtain ⟨c1, s1, h1rip, h1w, _, h1mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 64) (len := 7) (width := 4)
      (hld a0.mem) a0.rip (by rw [himg]; decide) d64
      (l2Slot_addr (mm := l2W15Mem) (k := 15) (t := 16 + i) (by omega) (by omega) hfits rfl rfl rfl a0.rax a0.rsp _) rfl hv15 rfl
  have a1 := a0.regStep h1rip h1w h1mem (by decide) (by decide) (by decide)
  obtain ⟨c2, s2, h2rip, h2w, _, h2mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 71) (len := 4) (width := 4)
      (hld a1.mem) a1.rip (by rw [himg]; decide) d71
      (l2Slot_addr (mm := l2W2Mem) (k := 2) (t := 16 + i) (by omega) (by omega) hfits rfl rfl rfl a1.rax a1.rsp _) rfl (by rw [a1.mem]; exact hv2) rfl
  have a2 := a1.regStep h2rip h2w h2mem (by decide) (by decide) (by decide)
  obtain ⟨c3, s3, h3rip, h3w, _, h3mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 75) (len := 3)
      (hld a2.mem) a2.rip (by rw [himg]; decide) d75
  have a3 := a2.regStep h3rip h3w h3mem (by decide) (by decide) (by decide)
  obtain ⟨c4, s4, h4rip, h4w, _, h4mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 78) (len := 4)
      (hld a3.mem) a3.rip (by rw [himg]; decide) d78 rfl
  have a4 := a3.regStep h4rip h4w h4mem (by decide) (by decide) (by decide)
  obtain ⟨c5, s5, h5rip, h5w, _, h5mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 82) (len := 3)
      (hld a4.mem) a4.rip (by rw [himg]; decide) d82
  have a5 := a4.regStep h5rip h5w h5mem (by decide) (by decide) (by decide)
  obtain ⟨c6, s6, h6rip, h6w, _, h6mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 85) (len := 4)
      (hld a5.mem) a5.rip (by rw [himg]; decide) d85 rfl
  have a6 := a5.regStep h6rip h6w h6mem (by decide) (by decide) (by decide)
  obtain ⟨c7, s7, h7rip, h7w, _, h7mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 89) (len := 3)
      (hld a6.mem) a6.rip (by rw [himg]; decide) d89 (by decide) rfl
  have a7 := a6.regStep h7rip h7w h7mem (by decide) (by decide) (by decide)
  obtain ⟨c8, s8, h8rip, h8w, _, h8mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 92) (len := 3)
      (hld a7.mem) a7.rip (by rw [himg]; decide) d92
  have a8 := a7.regStep h8rip h8w h8mem (by decide) (by decide) (by decide)
  obtain ⟨c9, s9, h9rip, h9w, _, h9mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 95) (len := 4)
      (hld a8.mem) a8.rip (by rw [himg]; decide) d95 rfl
  have a9 := a8.regStep h9rip h9w h9mem (by decide) (by decide) (by decide)
  obtain ⟨c10, s10, h10rip, h10w, _, h10mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 99) (len := 3)
      (hld a9.mem) a9.rip (by rw [himg]; decide) d99 (by decide) rfl
  have a10 := a9.regStep h10rip h10w h10mem (by decide) (by decide) (by decide)
  obtain ⟨c11, s11, h11rip, h11w, _, h11mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 102) (len := 3)
      (hld a10.mem) a10.rip (by rw [himg]; decide) d102 (by decide) rfl
  have a11 := a10.regStep h11rip h11w h11mem (by decide) (by decide) (by decide)
  obtain ⟨c12, s12, h12rip, h12w, _, h12mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 105) (len := 2)
      (hld a11.mem) a11.rip (by rw [himg]; decide) d105
  have a12 := a11.regStep h12rip h12w h12mem (by decide) (by decide) (by decide)
  obtain ⟨c13, s13, h13rip, h13w, _, h13mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 107) (len := 3)
      (hld a12.mem) a12.rip (by rw [himg]; decide) d107 rfl
  have a13 := a12.regStep h13rip h13w h13mem (by decide) (by decide) (by decide)
  obtain ⟨c14, s14, h14rip, h14w, _, h14mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 110) (len := 3)
      (hld a13.mem) a13.rip (by rw [himg]; decide) d110
  have a14 := a13.regStep h14rip h14w h14mem (by decide) (by decide) (by decide)
  obtain ⟨c15, s15, h15rip, h15w, _, h15mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 113) (len := 4)
      (hld a14.mem) a14.rip (by rw [himg]; decide) d113 rfl
  have a15 := a14.regStep h15rip h15w h15mem (by decide) (by decide) (by decide)
  obtain ⟨c16, s16, h16rip, h16w, _, h16mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 117) (len := 3)
      (hld a15.mem) a15.rip (by rw [himg]; decide) d117 (by decide) rfl
  have a16 := a15.regStep h16rip h16w h16mem (by decide) (by decide) (by decide)
  obtain ⟨c17, s17, h17rip, h17w, _, h17mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 120) (len := 3)
      (hld a16.mem) a16.rip (by rw [himg]; decide) d120 rfl
  have a17 := a16.regStep h17rip h17w h17mem (by decide) (by decide) (by decide)
  obtain ⟨c18, s18, h18rip, h18w, _, h18mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 123) (len := 3)
      (hld a17.mem) a17.rip (by rw [himg]; decide) d123 (by decide) rfl
  have a18 := a17.regStep h18rip h18w h18mem (by decide) (by decide) (by decide)
  obtain ⟨c19, s19, h19rip, h19w, _, h19mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 126) (len := 5) (width := 4)
      (hld a18.mem) a18.rip (by rw [himg]; decide) d126
      (by decide)
      (l2Slot_addr (mm := l2W7Mem) (k := 7) (t := 16 + i) (by omega) (by omega) hfits rfl rfl rfl a18.rax a18.rsp _) rfl (by rw [a18.mem]; exact hv7)
  have a19 := a18.regStep h19rip h19w h19mem (by decide) (by decide) (by decide)
  obtain ⟨c20, s20, h20rip, h20w, _, h20mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 131) (len := 3)
      (hld a19.mem) a19.rip (by rw [himg]; decide) d131 (by decide) rfl
  have a20 := a19.regStep h20rip h20w h20mem (by decide) (by decide) (by decide)
  -- 134: mov %r8d,-0x60(%rsp,%rax,4)   (the store of w[t])
  obtain ⟨c21, s21, h21rip, h21regs, _, h21stored⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 134) (len := 5) (width := 4)
      (hld a20.mem) a20.rip (by rw [himg]; decide) d134
      (l2Slot_addr (mm := l2WtMem) (k := 0) (t := 16 + i) (by omega) (by omega)
        hfits rfl rfl rfl a20.rax a20.rsp _) rfl rfl (by rw [a20.mem]; exact hwrite)
  have hstlen : (Silmaril.X86.Ext.leBytes
      ((Silmaril.X86.Ext.Sz.d.read c20.core Reg.r8).setWidth 64) 4).length = 4 :=
    Silmaril.X86.Ext.length_leBytes _ _
  have hld21 : Loaded c21.memory L.textBase img :=
    Silmaril.X86.Ext.Loaded.of_stored (hld a20.mem) h21stored
      (by rw [hstlen, himg]; exact h.store_disjoint_code (by omega) (by omega))
  have h21rax : c21.core.read .rax = BitVec.ofNat 64 (16 + i) := by
    rw [h21regs _]; exact a20.rax
  have h21rsp : c21.core.read .rsp = rspEntry - BitVec.ofNat 64 216 := by
    rw [h21regs _]; exact a20.rsp
  -- 139: inc %rax
  obtain ⟨c22, s22, h22rip, h22w, _, h22mem⟩ :=
    stepOpt_inc_reg (exit := L.exit) (offset := 139) (len := 3)
      hld21 h21rip (by rw [himg]; decide) d139
  have h22rax : c22.core.read .rax = BitVec.ofNat 64 (16 + i + 1) := by
    rw [h22w.target]
    have hr : Silmaril.X86.Ext.Sz.q.read c21.core Reg.rax = BitVec.ofNat 64 (16 + i) := by
      rw [Silmaril.X86.Ext.Sz.read_q]; exact h21rax
    rw [hr]; exact Silmaril.X86.Ext.ofNat_add_ofNat (16 + i) 1
  have h22rsp : c22.core.read .rsp = rspEntry - BitVec.ofNat 64 216 := by
    rw [h22w.other _ (by decide)]; exact h21rsp
  -- 142: mov %ecx,%edx   (carry w[t-15] into %edx for the next iteration)
  obtain ⟨c23, s23, h23rip, h23w, _, h23mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 142) (len := 2)
      (h22mem ▸ hld21) h22rip (by rw [himg]; decide) d142
  have h23rax : c23.core.read .rax = BitVec.ofNat 64 (16 + i + 1) := by
    rw [h23w.other _ (by decide)]; exact h22rax
  have h23rsp : c23.core.read .rsp = rspEntry - BitVec.ofNat 64 216 := by
    rw [h23w.other _ (by decide)]; exact h22rsp
  -- 144: cmp $0x40,%rax
  obtain ⟨c24, s24, h24rip, h24regs, h24flags, h24mem⟩ :=
    Silmaril.X86.Ext.stepOpt_cmpI8_reg (exit := L.exit) (offset := 144) (len := 4)
      (h23mem ▸ h22mem ▸ hld21) h23rip (by rw [himg]; decide) d144
  have hcond : Silmaril.X86.Ext.Cond.ne.eval c24.core.flags
      = some (decide (16 + i + 1 ≠ 64)) := by
    rw [h24flags]
    simp only [Silmaril.X86.Ext.Sz.read_q]
    show Silmaril.X86.Ext.Cond.ne.eval (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp
        (c23.core.read Reg.rax) ((0x40#8 : BitVec 8).signExtend 64)) = _
    rw [Silmaril.X86.Ext.eval_ne_cmp, h23rax,
      show ((0x40#8 : BitVec 8).signExtend 64) = BitVec.ofNat 64 64 from rfl]
    congr 1
    simp only [l2_counter_ne hi]
  -- 148: jne 64
  have htarget : (if decide (16 + i + 1 ≠ 64) = true then
        L.textBase + BitVec.ofNat 64 (148 + 2) + (0xaa#8 : BitVec 8).signExtend 64
      else L.textBase + BitVec.ofNat 64 (148 + 2))
      = L.textBase + BitVec.ofNat 64 (if i + 1 < 48 then 64 else 150) := by
    by_cases hlast : i + 1 = 48
    · rw [show (decide (16 + i + 1 ≠ 64)) = false from by simp; omega]
      rw [show (if i + 1 < 48 then (64 : Nat) else 150) = 150 from by simp [hlast]]
      rfl
    · rw [show (decide (16 + i + 1 ≠ 64)) = true from by simp; omega]
      rw [show (if i + 1 < 48 then (64 : Nat) else 150) = 64 from
        ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      exact l2_backedge L.textBase
  obtain ⟨c25, s25, h25rip, h25regs, _, h25mem⟩ :=
    stepOpt_jcc8 (exit := L.exit) (offset := 148) (len := 2)
      (h24mem ▸ h23mem ▸ h22mem ▸ hld21) h24rip (by rw [himg]; decide) d148 hcond htarget
  refine ⟨c25, Reaches.cons s1 (Reaches.cons s2 (Reaches.cons s3 (Reaches.cons s4 (Reaches.cons s5 (Reaches.cons s6 (Reaches.cons s7 (Reaches.cons s8 (Reaches.cons s9 (Reaches.cons s10 (Reaches.cons s11 (Reaches.cons s12 (Reaches.cons s13 (Reaches.cons s14 (Reaches.cons s15 (Reaches.cons s16 (Reaches.cons s17 (Reaches.cons s18 (Reaches.cons s19 (Reaches.cons s20 (Reaches.cons s21 (Reaches.cons s22 (Reaches.cons s23 (Reaches.cons s24 (Reaches.one s25)))))))))))))))))))))))), ?_, ?_⟩
  refine ⟨h25rip, ?_, ?_, ?_, ?_⟩
  · rw [h25regs _, h24regs _]; exact h23rax
  · rw [h25regs _, h24regs _, h23rsp, a0.rsp]
  · rw [h25regs _, h24regs _, h23w.other _ (by decide), h22w.other _ (by decide),
      h21regs _, a20.rdi]
    exact a0.rdi.symm
  · refine ⟨(Silmaril.X86.Ext.Sz.d.read c20.core Reg.r8).setWidth 64, ?_⟩
    rw [h25mem, h24mem, h23mem, h22mem, ← a20.mem]
    exact h21stored
  · -- the schedule word, and the register carried to the next iteration
    obtain ⟨D, hD⟩ : ∃ D, read32 cur.core Reg.rdx = D := ⟨_, rfl⟩
    have v1 : read32 c1.core Reg.rcx =
        W (16 + i - 15) := by
      rw [read_d_of_writes h1w]
      exact trunc32 _
    have v2 : read32 c2.core Reg.rsi =
        W (16 + i - 2) := by
      rw [read_d_of_writes h2w]
      exact trunc32 _
    have v3 : read32 c3.core Reg.r8 =
        W (16 + i - 15) := by
      rw [read_d_of_writes h3w]
      simp only [← read32_eq]
      rw [read_d_of_other (r := Reg.rcx) h2w (by decide), v1]
      try rfl
    have v4 : read32 c4.core Reg.r8 =
        (W (16 + i - 15)).rotateLeft 25 := by
      rw [read_d_of_writes h4w]
      simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x19#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 25 from rfl]
      rw [v3]
      try rfl
    have v5 : read32 c5.core Reg.r9 =
        W (16 + i - 15) := by
      rw [read_d_of_writes h5w]
      simp only [← read32_eq]
      rw [read_d_of_other (r := Reg.rcx) h4w (by decide), read_d_of_other (r := Reg.rcx) h3w (by decide), read_d_of_other (r := Reg.rcx) h2w (by decide), v1]
      try rfl
    have v6 : read32 c6.core Reg.r9 =
        (W (16 + i - 15)).rotateLeft 14 := by
      rw [read_d_of_writes h6w]
      simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x0e#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 14 from rfl]
      rw [v5]
      try rfl
    have v7 : read32 c7.core Reg.r9 =
        ((W (16 + i - 15)).rotateLeft 14) ^^^ ((W (16 + i - 15)).rotateLeft 25) := by
      rw [read_d_of_writes h7w]
      simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
      rw [v6, read_d_of_other (r := Reg.r8) h6w (by decide), read_d_of_other (r := Reg.r8) h5w (by decide), v4]
      try rfl
    have v8 : read32 c8.core Reg.r8 =
        W (16 + i - 15) := by
      rw [read_d_of_writes h8w]
      simp only [← read32_eq]
      rw [read_d_of_other (r := Reg.rcx) h7w (by decide), read_d_of_other (r := Reg.rcx) h6w (by decide), read_d_of_other (r := Reg.rcx) h5w (by decide), read_d_of_other (r := Reg.rcx) h4w (by decide), read_d_of_other (r := Reg.rcx) h3w (by decide), read_d_of_other (r := Reg.rcx) h2w (by decide), v1]
      try rfl
    have v9 : read32 c9.core Reg.r8 =
        (W (16 + i - 15)) >>> 3 := by
      rw [read_d_of_writes h9w]
      simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x03#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 3 from rfl]
      rw [v8]
      try rfl
    have v10 : read32 c10.core Reg.r8 =
        ((W (16 + i - 15)) >>> 3) ^^^ (((W (16 + i - 15)).rotateLeft 14) ^^^ ((W (16 + i - 15)).rotateLeft 25)) := by
      rw [read_d_of_writes h10w]
      simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
      rw [v9, read_d_of_other (r := Reg.r9) h9w (by decide), read_d_of_other (r := Reg.r9) h8w (by decide), v7]
      try rfl
    have v11 : read32 c11.core Reg.r8 =
        (((W (16 + i - 15)) >>> 3) ^^^ (((W (16 + i - 15)).rotateLeft 14) ^^^ ((W (16 + i - 15)).rotateLeft 25))) + (D) := by
      rw [read_d_of_writes h11w]
      simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
      rw [v10, read_d_of_other (r := Reg.rdx) h10w (by decide), read_d_of_other (r := Reg.rdx) h9w (by decide), read_d_of_other (r := Reg.rdx) h8w (by decide), read_d_of_other (r := Reg.rdx) h7w (by decide), read_d_of_other (r := Reg.rdx) h6w (by decide), read_d_of_other (r := Reg.rdx) h5w (by decide), read_d_of_other (r := Reg.rdx) h4w (by decide), read_d_of_other (r := Reg.rdx) h3w (by decide), read_d_of_other (r := Reg.rdx) h2w (by decide), read_d_of_other (r := Reg.rdx) h1w (by decide), hD]
      try rfl
    have v12 : read32 c12.core Reg.rdx =
        W (16 + i - 2) := by
      rw [read_d_of_writes h12w]
      simp only [← read32_eq]
      rw [read_d_of_other (r := Reg.rsi) h11w (by decide), read_d_of_other (r := Reg.rsi) h10w (by decide), read_d_of_other (r := Reg.rsi) h9w (by decide), read_d_of_other (r := Reg.rsi) h8w (by decide), read_d_of_other (r := Reg.rsi) h7w (by decide), read_d_of_other (r := Reg.rsi) h6w (by decide), read_d_of_other (r := Reg.rsi) h5w (by decide), read_d_of_other (r := Reg.rsi) h4w (by decide), read_d_of_other (r := Reg.rsi) h3w (by decide), v2]
      try rfl
    have v13 : read32 c13.core Reg.rdx =
        (W (16 + i - 2)).rotateLeft 15 := by
      rw [read_d_of_writes h13w]
      simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x0f#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 15 from rfl]
      rw [v12]
      try rfl
    have v14 : read32 c14.core Reg.r9 =
        W (16 + i - 2) := by
      rw [read_d_of_writes h14w]
      simp only [← read32_eq]
      rw [read_d_of_other (r := Reg.rsi) h13w (by decide), read_d_of_other (r := Reg.rsi) h12w (by decide), read_d_of_other (r := Reg.rsi) h11w (by decide), read_d_of_other (r := Reg.rsi) h10w (by decide), read_d_of_other (r := Reg.rsi) h9w (by decide), read_d_of_other (r := Reg.rsi) h8w (by decide), read_d_of_other (r := Reg.rsi) h7w (by decide), read_d_of_other (r := Reg.rsi) h6w (by decide), read_d_of_other (r := Reg.rsi) h5w (by decide), read_d_of_other (r := Reg.rsi) h4w (by decide), read_d_of_other (r := Reg.rsi) h3w (by decide), v2]
      try rfl
    have v15 : read32 c15.core Reg.r9 =
        (W (16 + i - 2)).rotateLeft 13 := by
      rw [read_d_of_writes h15w]
      simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x0d#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 13 from rfl]
      rw [v14]
      try rfl
    have v16 : read32 c16.core Reg.r9 =
        ((W (16 + i - 2)).rotateLeft 13) ^^^ ((W (16 + i - 2)).rotateLeft 15) := by
      rw [read_d_of_writes h16w]
      simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
      rw [v15, read_d_of_other (r := Reg.rdx) h15w (by decide), read_d_of_other (r := Reg.rdx) h14w (by decide), v13]
      try rfl
    have v17 : read32 c17.core Reg.rsi =
        (W (16 + i - 2)) >>> 10 := by
      rw [read_d_of_writes h17w]
      simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x0a#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 10 from rfl]
      rw [read_d_of_other (r := Reg.rsi) h16w (by decide), read_d_of_other (r := Reg.rsi) h15w (by decide), read_d_of_other (r := Reg.rsi) h14w (by decide), read_d_of_other (r := Reg.rsi) h13w (by decide), read_d_of_other (r := Reg.rsi) h12w (by decide), read_d_of_other (r := Reg.rsi) h11w (by decide), read_d_of_other (r := Reg.rsi) h10w (by decide), read_d_of_other (r := Reg.rsi) h9w (by decide), read_d_of_other (r := Reg.rsi) h8w (by decide), read_d_of_other (r := Reg.rsi) h7w (by decide), read_d_of_other (r := Reg.rsi) h6w (by decide), read_d_of_other (r := Reg.rsi) h5w (by decide), read_d_of_other (r := Reg.rsi) h4w (by decide), read_d_of_other (r := Reg.rsi) h3w (by decide), v2]
      try rfl
    have v18 : read32 c18.core Reg.rsi =
        ((W (16 + i - 2)) >>> 10) ^^^ (((W (16 + i - 2)).rotateLeft 13) ^^^ ((W (16 + i - 2)).rotateLeft 15)) := by
      rw [read_d_of_writes h18w]
      simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
      rw [v17, read_d_of_other (r := Reg.r9) h17w (by decide), v16]
      try rfl
    have v19 : read32 c19.core Reg.r8 =
        ((((W (16 + i - 15)) >>> 3) ^^^ (((W (16 + i - 15)).rotateLeft 14) ^^^ ((W (16 + i - 15)).rotateLeft 25))) + (D)) + (W (16 + i - 7)) := by
      rw [read_d_of_writes h19w]
      simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN, trunc32']
      rw [read_d_of_other (r := Reg.r8) h18w (by decide), read_d_of_other (r := Reg.r8) h17w (by decide), read_d_of_other (r := Reg.r8) h16w (by decide), read_d_of_other (r := Reg.r8) h15w (by decide), read_d_of_other (r := Reg.r8) h14w (by decide), read_d_of_other (r := Reg.r8) h13w (by decide), read_d_of_other (r := Reg.r8) h12w (by decide), v11]
      try rfl
    have v20 : read32 c20.core Reg.r8 =
        (((((W (16 + i - 15)) >>> 3) ^^^ (((W (16 + i - 15)).rotateLeft 14) ^^^ ((W (16 + i - 15)).rotateLeft 25))) + (D)) + (W (16 + i - 7))) + (((W (16 + i - 2)) >>> 10) ^^^ (((W (16 + i - 2)).rotateLeft 13) ^^^ ((W (16 + i - 2)).rotateLeft 15))) := by
      rw [read_d_of_writes h20w]
      simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
      rw [v19, read_d_of_other (r := Reg.rsi) h19w (by decide), v18]
      try rfl
    have v23 : read32 c23.core Reg.rdx =
        W (16 + i - 15) := by
      rw [read_d_of_writes h23w]
      simp only [← read32_eq]
      rw [read_d_of_other (r := Reg.rcx) h22w (by decide), read32_of_sameRegs h21regs, read_d_of_other (r := Reg.rcx) h20w (by decide), read_d_of_other (r := Reg.rcx) h19w (by decide), read_d_of_other (r := Reg.rcx) h18w (by decide), read_d_of_other (r := Reg.rcx) h17w (by decide), read_d_of_other (r := Reg.rcx) h16w (by decide), read_d_of_other (r := Reg.rcx) h15w (by decide), read_d_of_other (r := Reg.rcx) h14w (by decide), read_d_of_other (r := Reg.rcx) h13w (by decide), read_d_of_other (r := Reg.rcx) h12w (by decide), read_d_of_other (r := Reg.rcx) h11w (by decide), read_d_of_other (r := Reg.rcx) h10w (by decide), read_d_of_other (r := Reg.rcx) h9w (by decide), read_d_of_other (r := Reg.rcx) h8w (by decide), read_d_of_other (r := Reg.rcx) h7w (by decide), read_d_of_other (r := Reg.rcx) h6w (by decide), read_d_of_other (r := Reg.rcx) h5w (by decide), read_d_of_other (r := Reg.rcx) h4w (by decide), read_d_of_other (r := Reg.rcx) h3w (by decide), read_d_of_other (r := Reg.rcx) h2w (by decide), v1]
      try rfl
    have f_stored : read32 c20.core Reg.r8 =
        (((((W (16 + i - 15)) >>> 3) ^^^ (((W (16 + i - 15)).rotateLeft 14) ^^^ ((W (16 + i - 15)).rotateLeft 25))) + (D)) + (W (16 + i - 7))) + (((W (16 + i - 2)) >>> 10) ^^^ (((W (16 + i - 2)).rotateLeft 13) ^^^ ((W (16 + i - 2)).rotateLeft 15))) := by
      rw [v20]
      try rfl
    have f_carry : read32 c25.core Reg.rdx =
        W (16 + i - 15) := by
      rw [read32_of_sameRegs h25regs, read32_of_sameRegs h24regs, v23]
      try rfl
    refine ⟨f_carry, ?_⟩
    rw [h25mem, h24mem, h23mem, h22mem, ← a20.mem]
    have hst := h21stored
    rw [show (Silmaril.X86.Ext.Sz.d.read c20.core Reg.r8).setWidth 64
        = (SHA256.Kernel.sigma1 (W (16 + i - 2)) + W (16 + i - 7)
            + SHA256.Kernel.sigma0 (W (16 + i - 15)) + read32 cur.core Reg.rdx).setWidth 64 from by
      rw [show Silmaril.X86.Ext.Sz.d.read c20.core Reg.r8 = read32 c20.core Reg.r8 from rfl,
        f_stored, hD, sigma0_eq_object, sigma1_eq_object, schedule_sum_comm]
      rfl] at hst
    exact hst

/-- **The L2 trace.** One iteration of the schedule loop, at the real image.
Supplies `l2_trace_img` with the twenty-five decode facts, each a slice of the
459-byte literal; the literal does not enter the proof itself. -/
theorem l2_trace (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} {i : Nat} (hi : i < 48)
    (hat : L2At L rspEntry state (image L.textBase L.rodataBase) 64
      (BitVec.ofNat 64 (16 + i)) cur)
    {W : Nat → SHA256.Kernel.Word}
    (hwords : WWordsAt cur.memory rspEntry (fun j => (W j).setWidth 64) (16 + i))
    (hwrite : cur.memory.Permitted .write (rspEntry.toNat - 312 + 4 * (16 + i)) 4) :
    ∃ cur', Reaches L.exit cur cur' ∧ L2Effect L rspEntry i cur cur' ∧
      ScheduleOut rspEntry W i cur cur' := by
  have hsl : ∀ o l : Nat, o + l ≤ relocOffset →
      ((image L.textBase L.rodataBase).drop o).take l = (raw.drop o).take l :=
    fun o l hb => image_slice _ _ hb
  exact l2_trace_img h hi (image_length L.textBase L.rodataBase)
    (by rw [hsl 64 7 (by decide)]; exact l2_decode_64)
    (by rw [hsl 71 4 (by decide)]; exact l2_decode_71)
    (by rw [hsl 75 3 (by decide)]; exact l2_decode_75)
    (by rw [hsl 78 4 (by decide)]; exact l2_decode_78)
    (by rw [hsl 82 3 (by decide)]; exact l2_decode_82)
    (by rw [hsl 85 4 (by decide)]; exact l2_decode_85)
    (by rw [hsl 89 3 (by decide)]; exact l2_decode_89)
    (by rw [hsl 92 3 (by decide)]; exact l2_decode_92)
    (by rw [hsl 95 4 (by decide)]; exact l2_decode_95)
    (by rw [hsl 99 3 (by decide)]; exact l2_decode_99)
    (by rw [hsl 102 3 (by decide)]; exact l2_decode_102)
    (by rw [hsl 105 2 (by decide)]; exact l2_decode_105)
    (by rw [hsl 107 3 (by decide)]; exact l2_decode_107)
    (by rw [hsl 110 3 (by decide)]; exact l2_decode_110)
    (by rw [hsl 113 4 (by decide)]; exact l2_decode_113)
    (by rw [hsl 117 3 (by decide)]; exact l2_decode_117)
    (by rw [hsl 120 3 (by decide)]; exact l2_decode_120)
    (by rw [hsl 123 3 (by decide)]; exact l2_decode_123)
    (by rw [hsl 126 5 (by decide)]; exact l2_decode_126)
    (by rw [hsl 131 3 (by decide)]; exact l2_decode_131)
    (by rw [hsl 134 5 (by decide)]; exact l2_decode_134)
    (by rw [hsl 139 3 (by decide)]; exact l2_decode_139)
    (by rw [hsl 142 2 (by decide)]; exact l2_decode_142)
    (by rw [hsl 144 4 (by decide)]; exact l2_decode_144)
    (by rw [hsl 148 2 (by decide)]; exact l2_decode_148)
    hat hwords hwrite

/-- **The weak L2 trace**, for the liveness chain. Chooses a witness function
for the existential slot rule, runs the pinned trace, and forgets the values
again.

`Ext.HoldsLE.norm32` is what makes the choice possible: a four-byte slot
records only the low thirty-two bits, so an arbitrary 64-bit witness can be
normalised into the `(w : BitVec 32).setWidth 64` shape `WWordsAt` is stated
at, without changing what the slot holds. Without it the two forms would not
meet and the loop would need its own copy of the twenty-five-step trace. -/
theorem l2_trace_weak (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} {i : Nat} (hi : i < 48)
    (hat : L2At L rspEntry state (image L.textBase L.rodataBase) 64
      (BitVec.ofNat 64 (16 + i)) cur)
    (hwords : WWordsRead cur.memory rspEntry (16 + i))
    (hwrite : cur.memory.Permitted .write (rspEntry.toNat - 312 + 4 * (16 + i)) 4) :
    ∃ cur', Reaches L.exit cur cur' ∧ L2Effect L rspEntry i cur cur' := by
  classical
  have key : ∀ j, ∃ v : SHA256.Kernel.Word, j < 16 + i →
      Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 312 + 4 * j) 4 (v.setWidth 64) := by
    intro j
    by_cases hj : j < 16 + i
    · obtain ⟨v, hv⟩ := hwords j hj
      exact ⟨v.setWidth 32, fun _ => hv.norm32⟩
    · exact ⟨0, fun hc => absurd hc hj⟩
  choose W hW using key
  obtain ⟨c', r, eff, _⟩ := l2_trace h hi hat (W := W) hW hwrite
  exact ⟨c', r, eff⟩

set_option maxRecDepth 8000 in
/-- `50: mov $0x10,%eax`, `55: mov -0x60(%rsp),%edx` (the `w[0]` preload) and
a NOP: control arrives at L2's head with the counter at 16 and `%edx`
carrying `w[0]`. The preload's *value* is not tracked — the weak invariant
does not need it. -/
theorem blockA (h : SysVEntry L state block rspEntry frameSize m) {cur : MState}
    (hs : L1Inv L state block rspEntry m 16 cur) {W : Nat → SHA256.Kernel.Word}
    (hw0 : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 312 + 4 * 0) 4
      ((W 0).setWidth 64)) :
    ∃ cur', Reaches L.exit cur cur' ∧
      L2At L rspEntry state (image L.textBase L.rodataBase) 64 (BitVec.ofNat 64 (16 + 0)) cur' ∧
      cur'.memory = cur.memory ∧ read32 cur'.core .rdx = W 0 := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hrip : cur.core.rip = L.textBase + BitVec.ofNat 64 50 := by
    have := hs.at_.rip; simpa using this
  have hwv := hw0
  obtain ⟨c1, s1, h1rip, h1w, _, h1mem⟩ :=
    stepOpt_movI32 (exit := L.exit) (offset := 50) (len := 5)
      hs.at_.loaded hrip (by rw [image_length]; decide)
      (by rw [image_slice _ _ (by decide : 50 + 5 ≤ relocOffset)]; exact blockA_decode_50)
  obtain ⟨c2, s2, h2rip, h2w, _, h2mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 55) (len := 4) (width := 4)
      (h1mem ▸ hs.at_.loaded) h1rip (by rw [image_length]; decide)
      (by rw [image_slice _ _ (by decide : 55 + 4 ≤ relocOffset)]; exact blockA_decode_55)
      (by rw [rspOnly_addr (off := 96) hfits (by omega) rfl rfl rfl (by omega)
            (by rw [h1w.other _ (by decide)]; exact hs.at_.rsp) _])
      rfl (by rw [h1mem]; exact hwv) rfl
  obtain ⟨c3, s3, h3rip, h3regs, _, h3mem⟩ :=
    stepOpt_nop (exit := L.exit) (offset := 59) (len := 5)
      (h2mem ▸ h1mem ▸ hs.at_.loaded) h2rip (by rw [image_length]; decide)
      (by rw [image_slice _ _ (by decide : 59 + 5 ≤ relocOffset)]; exact blockA_decode_59)
  refine ⟨c3, Reaches.cons s1 (Reaches.cons s2 (Reaches.one s3)),
    ⟨h3rip, ?_, ?_, ?_, ?_⟩, by rw [h3mem, h2mem, h1mem], ?_⟩
  · rw [h3regs _, h2w.other _ (by decide), h1w.target]; rfl
  · rw [h3regs _, h2w.other _ (by decide), h1w.other _ (by decide)]; exact hs.at_.rsp
  · rw [h3regs _, h2w.other _ (by decide), h1w.other _ (by decide)]; exact hs.at_.rdi
  · rw [h3mem, h2mem, h1mem]; exact hs.at_.loaded
  · rw [read32_of_sameRegs h3regs, read_d_of_writes h2w]
    exact trunc32 _

/-! ## Block `374 … 441`: `state[j] += a_j`

Eight pairs, each an `add` from a spill slot into the round register and a
`mov` of the result into `state[j]`. This is the only block that writes
`state[]`, so it is where the output half of the footprint is used. -/

/-- The eight `a…h` spill slots at `[rspEntry - 344, rspEntry - 312)` read.
Written by block `150 … 224`, read here. -/
def SpillSlotsHold (memory : Memory) (rspEntry : Word) : Prop :=
  ∀ j, j < 8 → ∃ v : Word,
    Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 344 + 4 * j) 4 v

set_option maxRecDepth 8000 in
/-- The effective address of `off(%rdi)` with no index: `state[off/4]`. -/
theorem rdiOnly_addr {cur : MState} {mm : Silmaril.X86.Ext.Mem} {off : Nat} {st : Word}
    (hnw : st.toNat + 32 ≤ 2 ^ 64) (hoff : off ≤ 28)
    (hbase : mm.base = .reg .rdi) (hindex : mm.index = Option.none)
    (hdisp : mm.disp.signExtend 64 = BitVec.ofNat 64 off)
    (hrdi : cur.core.read .rdi = st) (next : Word) :
    (mm.addr cur.core next).toNat = st.toNat + off := by
  simp only [Silmaril.X86.Ext.Mem.addr, hbase, hindex, Silmaril.X86.Ext.Base.value_reg,
    Option.map_none, Option.getD_none, hrdi, hdisp, BitVec.add_zero]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega)]
  omega

/-- `-0x80(%rsp)` — the spill slot at `rspEntry - 344`. -/
def cSpill128Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := Option.none, disp := 0xffffff80#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `0x0(%rdi)` — `state[0]`. -/
def cState0Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rdi, index := Option.none, disp := 0x00000000#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `-0x84(%rsp)` — the spill slot at `rspEntry - 340`. -/
def cSpill124Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := Option.none, disp := 0xffffff84#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `0x4(%rdi)` — `state[1]`. -/
def cState4Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rdi, index := Option.none, disp := 0x00000004#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `-0x88(%rsp)` — the spill slot at `rspEntry - 336`. -/
def cSpill120Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := Option.none, disp := 0xffffff88#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `0x8(%rdi)` — `state[2]`. -/
def cState8Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rdi, index := Option.none, disp := 0x00000008#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `-0x8c(%rsp)` — the spill slot at `rspEntry - 332`. -/
def cSpill116Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := Option.none, disp := 0xffffff8c#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `0xc(%rdi)` — `state[3]`. -/
def cState12Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rdi, index := Option.none, disp := 0x0000000c#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `-0x90(%rsp)` — the spill slot at `rspEntry - 328`. -/
def cSpill112Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := Option.none, disp := 0xffffff90#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `0x10(%rdi)` — `state[4]`. -/
def cState16Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rdi, index := Option.none, disp := 0x00000010#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `-0x94(%rsp)` — the spill slot at `rspEntry - 324`. -/
def cSpill108Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := Option.none, disp := 0xffffff94#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `0x14(%rdi)` — `state[5]`. -/
def cState20Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rdi, index := Option.none, disp := 0x00000014#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `-0x98(%rsp)` — the spill slot at `rspEntry - 320`. -/
def cSpill104Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := Option.none, disp := 0xffffff98#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `0x18(%rdi)` — `state[6]`. -/
def cState24Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rdi, index := Option.none, disp := 0x00000018#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `-0x9c(%rsp)` — the spill slot at `rspEntry - 316`. -/
def cSpill100Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := Option.none, disp := 0xffffff9c#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }
/-- `0x1c(%rdi)` — `state[7]`. -/
def cState28Mem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rdi, index := Option.none, disp := 0x0000001c#32,
    rip_no_index := by intro hc; exact absurd hc (by decide) }

set_option maxRecDepth 8000 in
/-- `374`: `add -0x80(%rsp),%r12d`. -/
theorem blockC_decode_374 : decode ((raw.drop 374).take 5)
    = some (.aluR .d .add .r12 (.mem cSpill128Mem), 5) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `379`: `mov %r12d,0x0(%rdi)`. -/
theorem blockC_decode_379 : decode ((raw.drop 379).take 3)
    = some (.mov .d (.mem cState0Mem) .r12, 3) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `382`: `add -0x84(%rsp),%r8d`. -/
theorem blockC_decode_382 : decode ((raw.drop 382).take 5)
    = some (.aluR .d .add .r8 (.mem cSpill124Mem), 5) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `387`: `mov %r8d,0x4(%rdi)`. -/
theorem blockC_decode_387 : decode ((raw.drop 387).take 4)
    = some (.mov .d (.mem cState4Mem) .r8, 4) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `391`: `add -0x88(%rsp),%rdxd`. -/
theorem blockC_decode_391 : decode ((raw.drop 391).take 4)
    = some (.aluR .d .add .rdx (.mem cSpill120Mem), 4) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `395`: `mov %rdxd,0x8(%rdi)`. -/
theorem blockC_decode_395 : decode ((raw.drop 395).take 3)
    = some (.mov .d (.mem cState8Mem) .rdx, 3) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `398`: `add -0x8c(%rsp),%r11d`. -/
theorem blockC_decode_398 : decode ((raw.drop 398).take 5)
    = some (.aluR .d .add .r11 (.mem cSpill116Mem), 5) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `403`: `mov %r11d,0xc(%rdi)`. -/
theorem blockC_decode_403 : decode ((raw.drop 403).take 4)
    = some (.mov .d (.mem cState12Mem) .r11, 4) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `407`: `add -0x90(%rsp),%r13d`. -/
theorem blockC_decode_407 : decode ((raw.drop 407).take 5)
    = some (.aluR .d .add .r13 (.mem cSpill112Mem), 5) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `412`: `mov %r13d,0x10(%rdi)`. -/
theorem blockC_decode_412 : decode ((raw.drop 412).take 4)
    = some (.mov .d (.mem cState16Mem) .r13, 4) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `416`: `add -0x94(%rsp),%r10d`. -/
theorem blockC_decode_416 : decode ((raw.drop 416).take 5)
    = some (.aluR .d .add .r10 (.mem cSpill108Mem), 5) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `421`: `mov %r10d,0x14(%rdi)`. -/
theorem blockC_decode_421 : decode ((raw.drop 421).take 4)
    = some (.mov .d (.mem cState20Mem) .r10, 4) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `425`: `add -0x98(%rsp),%r9d`. -/
theorem blockC_decode_425 : decode ((raw.drop 425).take 5)
    = some (.aluR .d .add .r9 (.mem cSpill104Mem), 5) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `430`: `mov %r9d,0x18(%rdi)`. -/
theorem blockC_decode_430 : decode ((raw.drop 430).take 4)
    = some (.mov .d (.mem cState24Mem) .r9, 4) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `434`: `add -0x9c(%rsp),%rbxd`. -/
theorem blockC_decode_434 : decode ((raw.drop 434).take 4)
    = some (.aluR .d .add .rbx (.mem cSpill100Mem), 4) :=
  decode_raw (by decide +kernel)
set_option maxRecDepth 8000 in
/-- `438`: `mov %rbxd,0x1c(%rdi)`. -/
theorem blockC_decode_438 : decode ((raw.drop 438).take 3)
    = some (.mov .d (.mem cState28Mem) .rbx, 3) :=
  decode_raw (by decide +kernel)
/-- Where block `374 … 441` is. -/
structure CAt (L : Layout) (st rspEntry : Word) (off : Nat) (entry cur : MState) : Prop where
  /-- RIP is at function offset `off`. -/
  rip : cur.core.rip = L.textBase + BitVec.ofNat 64 off
  /-- The output pointer. -/
  rdi : cur.core.read .rdi = st
  /-- The frame is still open. -/
  rsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216
  /-- Everything written so far is inside the modifies set. -/
  frame : Memory.WritesWithin entry.memory cur.memory (Footprint st rspEntry frameSize)
  /-- The spill slots still read: the stores here go to `state[]`. -/
  spills : SpillSlotsHold cur.memory rspEntry
  /-- The callee-saved slots still read. -/
  saved : SavedSlotsAt cur.memory rspEntry (fun j => entry.core.read (savedReg j))
  /-- The image is still loaded. -/
  loaded : Loaded cur.memory L.textBase (image L.textBase L.rodataBase)

/-- An `add` from a spill slot: a scratch register and the flags, no memory. -/
theorem CAt.addStep {off len : Nat} {st : Word} {entry cur next : MState}
    {dst : Reg} {v : Word}
    (hs : CAt L st rspEntry off entry cur)
    (hrip : next.core.rip = L.textBase + BitVec.ofNat 64 (off + len))
    (hw : Silmaril.X86.Ext.WritesReg cur.core next.core dst v)
    (hmem : next.memory = cur.memory)
    (d1 : Reg.rdi ≠ dst) (d2 : Reg.rsp ≠ dst) :
    CAt L st rspEntry (off + len) entry next where
  rip := hrip
  rdi := by rw [hw.other _ d1]; exact hs.rdi
  rsp := by rw [hw.other _ d2]; exact hs.rsp
  frame := by rw [hmem]; exact hs.frame
  spills := by rw [hmem]; exact hs.spills
  saved := by rw [hmem]; exact hs.saved
  loaded := by rw [hmem]; exact hs.loaded

/-- A store into `state[]`: no register changes, and the spill and saved
slots survive because `state[]` is disjoint from the callee's stack. -/
theorem CAt.storeStep (h : SysVEntry L state block rspEntry frameSize m)
    {off len d : Nat} {entry cur next : MState} {v : Word}
    (hs : CAt L state rspEntry off entry cur) (hd : d ≤ 28)
    (hrip : next.core.rip = L.textBase + BitVec.ofNat 64 (off + len))
    (hregs : Silmaril.X86.Ext.SameRegs cur.core next.core)
    (hst : Stored cur.memory next.memory (state.toNat + d)
      (Silmaril.X86.Ext.leBytes v 4)) :
    CAt L state rspEntry (off + len) entry next := by
  have hlen : (Silmaril.X86.Ext.leBytes v 4).length = 4 :=
    Silmaril.X86.Ext.length_leBytes _ _
  have hfits := h.frameFits
  rw [frameExtent_eq] at hfits
  refine { rip := hrip, rdi := ?_, rsp := ?_, frame := ?_, spills := ?_, saved := ?_, loaded := ?_ }
  · rw [hregs _]; exact hs.rdi
  · rw [hregs _]; exact hs.rsp
  · refine Silmaril.Process.Memory.WritesWithin.step hs.frame hst ?_
    intro o ho
    rw [hlen] at ho
    refine Or.inl ?_
    simp only [stateRegion, Region.Contains]
    omega
  · have hd2 := h.state_disjoint_frame
    simp only [stateRegion, frameRegion, Region.Disjoint, frameFloor_eq, frameExtent_eq] at hd2
    intro j hj
    obtain ⟨w, hw⟩ := hs.spills j hj
    exact ⟨w, Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst hw (by rw [hlen]; omega)⟩
  · have hd2 := h.state_disjoint_frame
    simp only [stateRegion, frameRegion, Region.Disjoint, frameFloor_eq, frameExtent_eq] at hd2
    intro j hj
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst (hs.saved j hj) (by rw [hlen]; omega)
  · refine Silmaril.X86.Ext.Loaded.of_stored hs.loaded hst ?_
    rw [hlen, image_length]
    exact h.stateStore_disjoint_code (by omega) (by omega)

/-- Any slice of `state[]` is readable: the contract's `StateReads` gives the
whole buffer, and `Permitted.sub` cuts it down. -/
theorem SysVEntry.state_readable (h : SysVEntry L state block rspEntry frameSize m)
    {o k : Nat} (hpos : 0 < k) (hk : o + k ≤ 32) :
    m.memory.Permitted .read (state.toNat + o) k := by
  obtain ⟨bytes, hb⟩ := h.stateReads
  exact Silmaril.X86.Ext.Memory.Permitted.sub
    (Silmaril.Process.Memory.readWith_permitted hb) hpos (by omega) (by omega)

set_option maxRecDepth 8000 in
/-- **Block `374 … 441`.** The eight `state[j] += a_j` pairs: control arrives
at the epilogue with `state[]` written and everything else intact. -/
theorem blockC (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} (hstart : CAt L state rspEntry 374 m cur)
    {sv : Nat → SHA256.Kernel.Word}
    (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : SHA256.Kernel.Word)
    (hsp0 : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 344 + 4 * 0) 4 ((sv 0).setWidth 64))
    (hsp1 : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 344 + 4 * 1) 4 ((sv 1).setWidth 64))
    (hsp2 : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 344 + 4 * 2) 4 ((sv 2).setWidth 64))
    (hsp3 : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 344 + 4 * 3) 4 ((sv 3).setWidth 64))
    (hsp4 : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 344 + 4 * 4) 4 ((sv 4).setWidth 64))
    (hsp5 : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 344 + 4 * 5) 4 ((sv 5).setWidth 64))
    (hsp6 : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 344 + 4 * 6) 4 ((sv 6).setWidth 64))
    (hsp7 : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 344 + 4 * 7) 4 ((sv 7).setWidth 64))
    (hr0 : read32 cur.core .r12 = rr0) (hr1 : read32 cur.core .r8 = rr1)
    (hr2 : read32 cur.core .rdx = rr2) (hr3 : read32 cur.core .r11 = rr3)
    (hr4 : read32 cur.core .r13 = rr4) (hr5 : read32 cur.core .r10 = rr5)
    (hr6 : read32 cur.core .r9 = rr6) (hr7 : read32 cur.core .rbx = rr7) :
    ∃ cur', Reaches L.exit cur cur' ∧ CAt L state rspEntry 441 m cur' ∧
      Silmaril.X86.Ext.HoldsLE cur'.memory (state.toNat + 4 * 0) 4 ((rr0 + sv 0).setWidth 64) ∧
      Silmaril.X86.Ext.HoldsLE cur'.memory (state.toNat + 4 * 1) 4 ((rr1 + sv 1).setWidth 64) ∧
      Silmaril.X86.Ext.HoldsLE cur'.memory (state.toNat + 4 * 2) 4 ((rr2 + sv 2).setWidth 64) ∧
      Silmaril.X86.Ext.HoldsLE cur'.memory (state.toNat + 4 * 3) 4 ((rr3 + sv 3).setWidth 64) ∧
      Silmaril.X86.Ext.HoldsLE cur'.memory (state.toNat + 4 * 4) 4 ((rr4 + sv 4).setWidth 64) ∧
      Silmaril.X86.Ext.HoldsLE cur'.memory (state.toNat + 4 * 5) 4 ((rr5 + sv 5).setWidth 64) ∧
      Silmaril.X86.Ext.HoldsLE cur'.memory (state.toNat + 4 * 6) 4 ((rr6 + sv 6).setWidth 64) ∧
      Silmaril.X86.Ext.HoldsLE cur'.memory (state.toNat + 4 * 7) 4 ((rr7 + sv 7).setWidth 64) := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hsnw : state.toNat + 32 ≤ 2 ^ 64 := by
    have := h.noWrap (stateRegion state) (by simp [regions])
    simpa [stateRegion, Silmaril.Process.addressLimit] using this
  have hsl : ∀ o l : Nat, relocOffset + 4 ≤ o →
      ((image L.textBase L.rodataBase).drop o).take l = (raw.drop o).take l :=
    fun o l hb => image_slice_above _ _ hb
  have hd2 := h.state_disjoint_frame
  simp only [stateRegion, frameRegion, Region.Disjoint, frameFloor_eq,
    frameExtent_eq] at hd2
  have hv1 : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 344 + 4 * 0) 4
      ((sv 0).setWidth 64) := by
    have t0 := hsp0
    exact t0
  obtain ⟨c1, s1, h1rip, h1w, _, h1mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 374) (len := 5) (width := 4)
      hstart.loaded hstart.rip (by rw [image_length]; decide)
      (by rw [hsl 374 5 (by decide)]; exact blockC_decode_374)
      (by decide)
      (by rw [rspOnly_addr (off := 128) hfits (by omega) rfl rfl rfl (by omega) hstart.rsp _]; omega)
      rfl hv1
  have a1 := hstart.addStep h1rip h1w h1mem (by decide) (by decide)
  obtain ⟨c2, s2, h2rip, h2regs, _, h2st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 379) (len := 3) (width := 4)
      a1.loaded a1.rip (by rw [image_length]; decide)
      (by rw [hsl 379 3 (by decide)]; exact blockC_decode_379)
      (rdiOnly_addr (off := 0) hsnw (by omega) rfl rfl rfl a1.rdi _) rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff a1.frame]
          exact Silmaril.X86.Ext.Memory.Permitted.sub h.stateWritable (by omega)
            (by omega) (by omega))
  have a2 := CAt.storeStep h a1 (by omega) h2rip h2regs h2st
  have hv3 : Silmaril.X86.Ext.HoldsLE c2.memory (rspEntry.toNat - 344 + 4 * 1) 4
      ((sv 1).setWidth 64) := by
    have t0 := hsp1
    rw [← h1mem] at t0
    have t1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h2st t0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact t1
  obtain ⟨c3, s3, h3rip, h3w, _, h3mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 382) (len := 5) (width := 4)
      a2.loaded a2.rip (by rw [image_length]; decide)
      (by rw [hsl 382 5 (by decide)]; exact blockC_decode_382)
      (by decide)
      (by rw [rspOnly_addr (off := 124) hfits (by omega) rfl rfl rfl (by omega) a2.rsp _]; omega)
      rfl hv3
  have a3 := a2.addStep h3rip h3w h3mem (by decide) (by decide)
  obtain ⟨c4, s4, h4rip, h4regs, _, h4st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 387) (len := 4) (width := 4)
      a3.loaded a3.rip (by rw [image_length]; decide)
      (by rw [hsl 387 4 (by decide)]; exact blockC_decode_387)
      (rdiOnly_addr (off := 4) hsnw (by omega) rfl rfl rfl a3.rdi _) rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff a3.frame]
          exact Silmaril.X86.Ext.Memory.Permitted.sub h.stateWritable (by omega)
            (by omega) (by omega))
  have a4 := CAt.storeStep h a3 (by omega) h4rip h4regs h4st
  have hv5 : Silmaril.X86.Ext.HoldsLE c4.memory (rspEntry.toNat - 344 + 4 * 2) 4
      ((sv 2).setWidth 64) := by
    have t0 := hsp2
    rw [← h1mem] at t0
    have t1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h2st t0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h3mem] at t1
    have t2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h4st t1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact t2
  obtain ⟨c5, s5, h5rip, h5w, _, h5mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 391) (len := 4) (width := 4)
      a4.loaded a4.rip (by rw [image_length]; decide)
      (by rw [hsl 391 4 (by decide)]; exact blockC_decode_391)
      (by decide)
      (by rw [rspOnly_addr (off := 120) hfits (by omega) rfl rfl rfl (by omega) a4.rsp _]; omega)
      rfl hv5
  have a5 := a4.addStep h5rip h5w h5mem (by decide) (by decide)
  obtain ⟨c6, s6, h6rip, h6regs, _, h6st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 395) (len := 3) (width := 4)
      a5.loaded a5.rip (by rw [image_length]; decide)
      (by rw [hsl 395 3 (by decide)]; exact blockC_decode_395)
      (rdiOnly_addr (off := 8) hsnw (by omega) rfl rfl rfl a5.rdi _) rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff a5.frame]
          exact Silmaril.X86.Ext.Memory.Permitted.sub h.stateWritable (by omega)
            (by omega) (by omega))
  have a6 := CAt.storeStep h a5 (by omega) h6rip h6regs h6st
  have hv7 : Silmaril.X86.Ext.HoldsLE c6.memory (rspEntry.toNat - 344 + 4 * 3) 4
      ((sv 3).setWidth 64) := by
    have t0 := hsp3
    rw [← h1mem] at t0
    have t1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h2st t0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h3mem] at t1
    have t2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h4st t1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h5mem] at t2
    have t3 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h6st t2
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact t3
  obtain ⟨c7, s7, h7rip, h7w, _, h7mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 398) (len := 5) (width := 4)
      a6.loaded a6.rip (by rw [image_length]; decide)
      (by rw [hsl 398 5 (by decide)]; exact blockC_decode_398)
      (by decide)
      (by rw [rspOnly_addr (off := 116) hfits (by omega) rfl rfl rfl (by omega) a6.rsp _]; omega)
      rfl hv7
  have a7 := a6.addStep h7rip h7w h7mem (by decide) (by decide)
  obtain ⟨c8, s8, h8rip, h8regs, _, h8st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 403) (len := 4) (width := 4)
      a7.loaded a7.rip (by rw [image_length]; decide)
      (by rw [hsl 403 4 (by decide)]; exact blockC_decode_403)
      (rdiOnly_addr (off := 12) hsnw (by omega) rfl rfl rfl a7.rdi _) rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff a7.frame]
          exact Silmaril.X86.Ext.Memory.Permitted.sub h.stateWritable (by omega)
            (by omega) (by omega))
  have a8 := CAt.storeStep h a7 (by omega) h8rip h8regs h8st
  have hv9 : Silmaril.X86.Ext.HoldsLE c8.memory (rspEntry.toNat - 344 + 4 * 4) 4
      ((sv 4).setWidth 64) := by
    have t0 := hsp4
    rw [← h1mem] at t0
    have t1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h2st t0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h3mem] at t1
    have t2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h4st t1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h5mem] at t2
    have t3 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h6st t2
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h7mem] at t3
    have t4 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h8st t3
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact t4
  obtain ⟨c9, s9, h9rip, h9w, _, h9mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 407) (len := 5) (width := 4)
      a8.loaded a8.rip (by rw [image_length]; decide)
      (by rw [hsl 407 5 (by decide)]; exact blockC_decode_407)
      (by decide)
      (by rw [rspOnly_addr (off := 112) hfits (by omega) rfl rfl rfl (by omega) a8.rsp _]; omega)
      rfl hv9
  have a9 := a8.addStep h9rip h9w h9mem (by decide) (by decide)
  obtain ⟨c10, s10, h10rip, h10regs, _, h10st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 412) (len := 4) (width := 4)
      a9.loaded a9.rip (by rw [image_length]; decide)
      (by rw [hsl 412 4 (by decide)]; exact blockC_decode_412)
      (rdiOnly_addr (off := 16) hsnw (by omega) rfl rfl rfl a9.rdi _) rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff a9.frame]
          exact Silmaril.X86.Ext.Memory.Permitted.sub h.stateWritable (by omega)
            (by omega) (by omega))
  have a10 := CAt.storeStep h a9 (by omega) h10rip h10regs h10st
  have hv11 : Silmaril.X86.Ext.HoldsLE c10.memory (rspEntry.toNat - 344 + 4 * 5) 4
      ((sv 5).setWidth 64) := by
    have t0 := hsp5
    rw [← h1mem] at t0
    have t1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h2st t0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h3mem] at t1
    have t2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h4st t1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h5mem] at t2
    have t3 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h6st t2
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h7mem] at t3
    have t4 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h8st t3
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h9mem] at t4
    have t5 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h10st t4
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact t5
  obtain ⟨c11, s11, h11rip, h11w, _, h11mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 416) (len := 5) (width := 4)
      a10.loaded a10.rip (by rw [image_length]; decide)
      (by rw [hsl 416 5 (by decide)]; exact blockC_decode_416)
      (by decide)
      (by rw [rspOnly_addr (off := 108) hfits (by omega) rfl rfl rfl (by omega) a10.rsp _]; omega)
      rfl hv11
  have a11 := a10.addStep h11rip h11w h11mem (by decide) (by decide)
  obtain ⟨c12, s12, h12rip, h12regs, _, h12st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 421) (len := 4) (width := 4)
      a11.loaded a11.rip (by rw [image_length]; decide)
      (by rw [hsl 421 4 (by decide)]; exact blockC_decode_421)
      (rdiOnly_addr (off := 20) hsnw (by omega) rfl rfl rfl a11.rdi _) rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff a11.frame]
          exact Silmaril.X86.Ext.Memory.Permitted.sub h.stateWritable (by omega)
            (by omega) (by omega))
  have a12 := CAt.storeStep h a11 (by omega) h12rip h12regs h12st
  have hv13 : Silmaril.X86.Ext.HoldsLE c12.memory (rspEntry.toNat - 344 + 4 * 6) 4
      ((sv 6).setWidth 64) := by
    have t0 := hsp6
    rw [← h1mem] at t0
    have t1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h2st t0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h3mem] at t1
    have t2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h4st t1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h5mem] at t2
    have t3 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h6st t2
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h7mem] at t3
    have t4 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h8st t3
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h9mem] at t4
    have t5 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h10st t4
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h11mem] at t5
    have t6 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h12st t5
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact t6
  obtain ⟨c13, s13, h13rip, h13w, _, h13mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 425) (len := 5) (width := 4)
      a12.loaded a12.rip (by rw [image_length]; decide)
      (by rw [hsl 425 5 (by decide)]; exact blockC_decode_425)
      (by decide)
      (by rw [rspOnly_addr (off := 104) hfits (by omega) rfl rfl rfl (by omega) a12.rsp _]; omega)
      rfl hv13
  have a13 := a12.addStep h13rip h13w h13mem (by decide) (by decide)
  obtain ⟨c14, s14, h14rip, h14regs, _, h14st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 430) (len := 4) (width := 4)
      a13.loaded a13.rip (by rw [image_length]; decide)
      (by rw [hsl 430 4 (by decide)]; exact blockC_decode_430)
      (rdiOnly_addr (off := 24) hsnw (by omega) rfl rfl rfl a13.rdi _) rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff a13.frame]
          exact Silmaril.X86.Ext.Memory.Permitted.sub h.stateWritable (by omega)
            (by omega) (by omega))
  have a14 := CAt.storeStep h a13 (by omega) h14rip h14regs h14st
  have hv15 : Silmaril.X86.Ext.HoldsLE c14.memory (rspEntry.toNat - 344 + 4 * 7) 4
      ((sv 7).setWidth 64) := by
    have t0 := hsp7
    rw [← h1mem] at t0
    have t1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h2st t0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h3mem] at t1
    have t2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h4st t1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h5mem] at t2
    have t3 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h6st t2
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h7mem] at t3
    have t4 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h8st t3
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h9mem] at t4
    have t5 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h10st t4
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h11mem] at t5
    have t6 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h12st t5
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h13mem] at t6
    have t7 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h14st t6
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact t7
  obtain ⟨c15, s15, h15rip, h15w, _, h15mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 434) (len := 4) (width := 4)
      a14.loaded a14.rip (by rw [image_length]; decide)
      (by rw [hsl 434 4 (by decide)]; exact blockC_decode_434)
      (by decide)
      (by rw [rspOnly_addr (off := 100) hfits (by omega) rfl rfl rfl (by omega) a14.rsp _]; omega)
      rfl hv15
  have a15 := a14.addStep h15rip h15w h15mem (by decide) (by decide)
  obtain ⟨c16, s16, h16rip, h16regs, _, h16st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 438) (len := 3) (width := 4)
      a15.loaded a15.rip (by rw [image_length]; decide)
      (by rw [hsl 438 3 (by decide)]; exact blockC_decode_438)
      (rdiOnly_addr (off := 28) hsnw (by omega) rfl rfl rfl a15.rdi _) rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff a15.frame]
          exact Silmaril.X86.Ext.Memory.Permitted.sub h.stateWritable (by omega)
            (by omega) (by omega))
  have a16 := CAt.storeStep h a15 (by omega) h16rip h16regs h16st
  have q0 : read32 c1.core Reg.r12 = rr0 + sv 0 := by
    rw [read_d_of_writes h1w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN, trunc32']
    rw [hr0]
    try rfl
  have perm0 : c1.memory.Permitted .read (state.toNat + 4 * 0) 4 := by
    rw [h1mem, Silmaril.Process.Memory.WritesWithin.permitted_iff hstart.frame]
    exact h.state_readable (by omega) (by omega)
  have fin0 : Silmaril.X86.Ext.HoldsLE c16.memory (state.toNat + 4 * 0) 4
      ((rr0 + sv 0).setWidth 64) := by
    have u0 : Silmaril.X86.Ext.HoldsLE c2.memory (state.toNat + 4 * 0) 4
        ((rr0 + sv 0).setWidth 64) := by
      rw [← q0]
      exact Silmaril.X86.Ext.HoldsLE.of_stored_self h2st perm0
    rw [← h3mem] at u0
    have u1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h4st u0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h5mem] at u1
    have u2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h6st u1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h7mem] at u2
    have u3 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h8st u2
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h9mem] at u3
    have u4 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h10st u3
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h11mem] at u4
    have u5 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h12st u4
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h13mem] at u5
    have u6 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h14st u5
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h15mem] at u6
    have u7 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st u6
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact u7
  have q1 : read32 c3.core Reg.r8 = rr1 + sv 1 := by
    rw [read_d_of_writes h3w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN, trunc32']
    rw [read32_of_sameRegs h2regs, read_d_of_other (r := Reg.r8) h1w (by decide), hr1]
    try rfl
  have perm1 : c3.memory.Permitted .read (state.toNat + 4 * 1) 4 := by
    rw [h3mem, Silmaril.Process.Memory.WritesWithin.permitted_iff a2.frame]
    exact h.state_readable (by omega) (by omega)
  have fin1 : Silmaril.X86.Ext.HoldsLE c16.memory (state.toNat + 4 * 1) 4
      ((rr1 + sv 1).setWidth 64) := by
    have u0 : Silmaril.X86.Ext.HoldsLE c4.memory (state.toNat + 4 * 1) 4
        ((rr1 + sv 1).setWidth 64) := by
      rw [← q1]
      exact Silmaril.X86.Ext.HoldsLE.of_stored_self h4st perm1
    rw [← h5mem] at u0
    have u1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h6st u0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h7mem] at u1
    have u2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h8st u1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h9mem] at u2
    have u3 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h10st u2
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h11mem] at u3
    have u4 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h12st u3
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h13mem] at u4
    have u5 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h14st u4
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h15mem] at u5
    have u6 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st u5
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact u6
  have q2 : read32 c5.core Reg.rdx = rr2 + sv 2 := by
    rw [read_d_of_writes h5w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN, trunc32']
    rw [read32_of_sameRegs h4regs, read_d_of_other (r := Reg.rdx) h3w (by decide), read32_of_sameRegs h2regs, read_d_of_other (r := Reg.rdx) h1w (by decide), hr2]
    try rfl
  have perm2 : c5.memory.Permitted .read (state.toNat + 4 * 2) 4 := by
    rw [h5mem, Silmaril.Process.Memory.WritesWithin.permitted_iff a4.frame]
    exact h.state_readable (by omega) (by omega)
  have fin2 : Silmaril.X86.Ext.HoldsLE c16.memory (state.toNat + 4 * 2) 4
      ((rr2 + sv 2).setWidth 64) := by
    have u0 : Silmaril.X86.Ext.HoldsLE c6.memory (state.toNat + 4 * 2) 4
        ((rr2 + sv 2).setWidth 64) := by
      rw [← q2]
      exact Silmaril.X86.Ext.HoldsLE.of_stored_self h6st perm2
    rw [← h7mem] at u0
    have u1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h8st u0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h9mem] at u1
    have u2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h10st u1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h11mem] at u2
    have u3 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h12st u2
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h13mem] at u3
    have u4 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h14st u3
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h15mem] at u4
    have u5 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st u4
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact u5
  have q3 : read32 c7.core Reg.r11 = rr3 + sv 3 := by
    rw [read_d_of_writes h7w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN, trunc32']
    rw [read32_of_sameRegs h6regs, read_d_of_other (r := Reg.r11) h5w (by decide), read32_of_sameRegs h4regs, read_d_of_other (r := Reg.r11) h3w (by decide), read32_of_sameRegs h2regs, read_d_of_other (r := Reg.r11) h1w (by decide), hr3]
    try rfl
  have perm3 : c7.memory.Permitted .read (state.toNat + 4 * 3) 4 := by
    rw [h7mem, Silmaril.Process.Memory.WritesWithin.permitted_iff a6.frame]
    exact h.state_readable (by omega) (by omega)
  have fin3 : Silmaril.X86.Ext.HoldsLE c16.memory (state.toNat + 4 * 3) 4
      ((rr3 + sv 3).setWidth 64) := by
    have u0 : Silmaril.X86.Ext.HoldsLE c8.memory (state.toNat + 4 * 3) 4
        ((rr3 + sv 3).setWidth 64) := by
      rw [← q3]
      exact Silmaril.X86.Ext.HoldsLE.of_stored_self h8st perm3
    rw [← h9mem] at u0
    have u1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h10st u0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h11mem] at u1
    have u2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h12st u1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h13mem] at u2
    have u3 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h14st u2
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h15mem] at u3
    have u4 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st u3
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact u4
  have q4 : read32 c9.core Reg.r13 = rr4 + sv 4 := by
    rw [read_d_of_writes h9w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN, trunc32']
    rw [read32_of_sameRegs h8regs, read_d_of_other (r := Reg.r13) h7w (by decide), read32_of_sameRegs h6regs, read_d_of_other (r := Reg.r13) h5w (by decide), read32_of_sameRegs h4regs, read_d_of_other (r := Reg.r13) h3w (by decide), read32_of_sameRegs h2regs, read_d_of_other (r := Reg.r13) h1w (by decide), hr4]
    try rfl
  have perm4 : c9.memory.Permitted .read (state.toNat + 4 * 4) 4 := by
    rw [h9mem, Silmaril.Process.Memory.WritesWithin.permitted_iff a8.frame]
    exact h.state_readable (by omega) (by omega)
  have fin4 : Silmaril.X86.Ext.HoldsLE c16.memory (state.toNat + 4 * 4) 4
      ((rr4 + sv 4).setWidth 64) := by
    have u0 : Silmaril.X86.Ext.HoldsLE c10.memory (state.toNat + 4 * 4) 4
        ((rr4 + sv 4).setWidth 64) := by
      rw [← q4]
      exact Silmaril.X86.Ext.HoldsLE.of_stored_self h10st perm4
    rw [← h11mem] at u0
    have u1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h12st u0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h13mem] at u1
    have u2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h14st u1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h15mem] at u2
    have u3 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st u2
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact u3
  have q5 : read32 c11.core Reg.r10 = rr5 + sv 5 := by
    rw [read_d_of_writes h11w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN, trunc32']
    rw [read32_of_sameRegs h10regs, read_d_of_other (r := Reg.r10) h9w (by decide), read32_of_sameRegs h8regs, read_d_of_other (r := Reg.r10) h7w (by decide), read32_of_sameRegs h6regs, read_d_of_other (r := Reg.r10) h5w (by decide), read32_of_sameRegs h4regs, read_d_of_other (r := Reg.r10) h3w (by decide), read32_of_sameRegs h2regs, read_d_of_other (r := Reg.r10) h1w (by decide), hr5]
    try rfl
  have perm5 : c11.memory.Permitted .read (state.toNat + 4 * 5) 4 := by
    rw [h11mem, Silmaril.Process.Memory.WritesWithin.permitted_iff a10.frame]
    exact h.state_readable (by omega) (by omega)
  have fin5 : Silmaril.X86.Ext.HoldsLE c16.memory (state.toNat + 4 * 5) 4
      ((rr5 + sv 5).setWidth 64) := by
    have u0 : Silmaril.X86.Ext.HoldsLE c12.memory (state.toNat + 4 * 5) 4
        ((rr5 + sv 5).setWidth 64) := by
      rw [← q5]
      exact Silmaril.X86.Ext.HoldsLE.of_stored_self h12st perm5
    rw [← h13mem] at u0
    have u1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h14st u0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    rw [← h15mem] at u1
    have u2 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st u1
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact u2
  have q6 : read32 c13.core Reg.r9 = rr6 + sv 6 := by
    rw [read_d_of_writes h13w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN, trunc32']
    rw [read32_of_sameRegs h12regs, read_d_of_other (r := Reg.r9) h11w (by decide), read32_of_sameRegs h10regs, read_d_of_other (r := Reg.r9) h9w (by decide), read32_of_sameRegs h8regs, read_d_of_other (r := Reg.r9) h7w (by decide), read32_of_sameRegs h6regs, read_d_of_other (r := Reg.r9) h5w (by decide), read32_of_sameRegs h4regs, read_d_of_other (r := Reg.r9) h3w (by decide), read32_of_sameRegs h2regs, read_d_of_other (r := Reg.r9) h1w (by decide), hr6]
    try rfl
  have perm6 : c13.memory.Permitted .read (state.toNat + 4 * 6) 4 := by
    rw [h13mem, Silmaril.Process.Memory.WritesWithin.permitted_iff a12.frame]
    exact h.state_readable (by omega) (by omega)
  have fin6 : Silmaril.X86.Ext.HoldsLE c16.memory (state.toNat + 4 * 6) 4
      ((rr6 + sv 6).setWidth 64) := by
    have u0 : Silmaril.X86.Ext.HoldsLE c14.memory (state.toNat + 4 * 6) 4
        ((rr6 + sv 6).setWidth 64) := by
      rw [← q6]
      exact Silmaril.X86.Ext.HoldsLE.of_stored_self h14st perm6
    rw [← h15mem] at u0
    have u1 := Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st u0
      (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
    exact u1
  have q7 : read32 c15.core Reg.rbx = rr7 + sv 7 := by
    rw [read_d_of_writes h15w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN, trunc32']
    rw [read32_of_sameRegs h14regs, read_d_of_other (r := Reg.rbx) h13w (by decide), read32_of_sameRegs h12regs, read_d_of_other (r := Reg.rbx) h11w (by decide), read32_of_sameRegs h10regs, read_d_of_other (r := Reg.rbx) h9w (by decide), read32_of_sameRegs h8regs, read_d_of_other (r := Reg.rbx) h7w (by decide), read32_of_sameRegs h6regs, read_d_of_other (r := Reg.rbx) h5w (by decide), read32_of_sameRegs h4regs, read_d_of_other (r := Reg.rbx) h3w (by decide), read32_of_sameRegs h2regs, read_d_of_other (r := Reg.rbx) h1w (by decide), hr7]
    try rfl
  have perm7 : c15.memory.Permitted .read (state.toNat + 4 * 7) 4 := by
    rw [h15mem, Silmaril.Process.Memory.WritesWithin.permitted_iff a14.frame]
    exact h.state_readable (by omega) (by omega)
  have fin7 : Silmaril.X86.Ext.HoldsLE c16.memory (state.toNat + 4 * 7) 4
      ((rr7 + sv 7).setWidth 64) := by
    have u0 : Silmaril.X86.Ext.HoldsLE c16.memory (state.toNat + 4 * 7) 4
        ((rr7 + sv 7).setWidth 64) := by
      rw [← q7]
      exact Silmaril.X86.Ext.HoldsLE.of_stored_self h16st perm7
    exact u0
  refine ⟨c16, Reaches.cons s1 (Reaches.cons s2 (Reaches.cons s3 (Reaches.cons s4 (Reaches.cons s5 (Reaches.cons s6 (Reaches.cons s7 (Reaches.cons s8 (Reaches.cons s9 (Reaches.cons s10 (Reaches.cons s11 (Reaches.cons s12 (Reaches.cons s13 (Reaches.cons s14 (Reaches.cons s15 (Reaches.one s16))))))))))))))), a16, ?_⟩
  exact ⟨fin0, fin1, fin2, fin3, fin4, fin5, fin6, fin7⟩

/-- **Block `374 … 441`, for the liveness chain.** Chooses witnesses for the
spill slots and reads the round registers off the entry state, then forgets
both. -/
theorem blockC_weak (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} (hstart : CAt L state rspEntry 374 m cur) :
    ∃ cur', Reaches L.exit cur cur' ∧ CAt L state rspEntry 441 m cur' := by
  classical
  have hsv : ∀ j, ∃ v : SHA256.Kernel.Word, j < 8 →
      Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 344 + 4 * j) 4 (v.setWidth 64) := by
    intro j
    by_cases hj : j < 8
    · obtain ⟨v, hv⟩ := hstart.spills j hj
      exact ⟨v.setWidth 32, fun _ => hv.norm32⟩
    · exact ⟨0, fun hc => absurd hc hj⟩
  choose sv hsvw using hsv
  obtain ⟨c', r, a', _, _, _, _, _, _, _, _⟩ := blockC h hstart (sv := sv)
    (read32 cur.core .r12) (read32 cur.core .r8) (read32 cur.core .rdx)
    (read32 cur.core .r11) (read32 cur.core .r13) (read32 cur.core .r10)
    (read32 cur.core .r9) (read32 cur.core .rbx)
    (hsvw 0 (by omega)) (hsvw 1 (by omega)) (hsvw 2 (by omega)) (hsvw 3 (by omega))
    (hsvw 4 (by omega)) (hsvw 5 (by omega)) (hsvw 6 (by omega)) (hsvw 7 (by omega))
    rfl rfl rfl rfl rfl rfl rfl rfl
  exact ⟨c', r, a'⟩

/-! ### The one decode that is not a `decide`

The `lea` at function offset 180 carries the single `R_X86_64_PC32`
displacement. `kLeaDisp`, `image_lea_slice` and `image_decode_lea` (it decodes
at every layout) are in `Sha256O2/Listing.lean`, which also proves the whole
loaded image decodes to the transcription at every layout (`image_decode`). -/

set_option maxRecDepth 8000 in
/-- The `lea` materialises `.rodata`: the RIP-relative effective address at
offset 180 is `rodataBase`, provided the relocation fits — which is exactly
what `Layout.RelocFits` asserts and why it is a precondition. -/
theorem kLea_value (L : Layout) (hfit : L.RelocFits) (core : Silmaril.X86.State) :
    (Silmaril.X86.Ext.Mem.ofRip (kLeaDisp L)).addr core
      (L.textBase + BitVec.ofNat 64 (180 + 7)) = L.rodataBase := by
  have hd : (kLeaDisp L).signExtend 64 = L.relocValue := by
    rw [kLeaDisp, show (relocOffset + 4) = 187 from rfl]
    exact hfit
  simp only [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofRip,
    Option.map_none, Option.getD_none, BitVec.add_zero, hd, Layout.relocValue]
  rw [show (relocOffset + 4) = 187 from rfl, sub_sub]
  show (L.textBase + BitVec.ofNat 64 (180 + 7))
      + (L.rodataBase - (L.textBase + BitVec.ofNat 64 187)) = L.rodataBase
  rw [show (BitVec.ofNat 64 (180 + 7)) = BitVec.ofNat 64 187 from rfl]
  simp

/-- The spill slots written so far, named by their displacement below `%rsp`.
The eight stores of block `150 … 224` are not in slot order, so a prefix
predicate like `WWordsRead` does not fit; a set does. -/
def SpillsAt (memory : Memory) (rspEntry : Word) (S : List Nat) : Prop :=
  ∀ d ∈ S, ∃ v : Word,
    Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 216 - d) 4 v

/-- One more spill slot written: the new one reads back, the old ones survive
because the slots are four bytes apart. -/
theorem SpillsAt.store {before after : Memory} {S : List Nat} {d' : Nat} {v : Word}
    (hfits : (344 : Nat) ≤ rspEntry.toNat)
    (hs : SpillsAt before rspEntry S)
    (hne : ∀ d ∈ S, d + 4 ≤ d' ∨ d' + 4 ≤ d)
    (hb : ∀ d ∈ S, 100 ≤ d ∧ d ≤ 128) (hb' : 100 ≤ d' ∧ d' ≤ 128)
    (hperm : before.Permitted .read (rspEntry.toNat - 216 - d') 4)
    (hst : Stored before after (rspEntry.toNat - 216 - d')
      (Silmaril.X86.Ext.leBytes v 4)) :
    SpillsAt after rspEntry (d' :: S) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact ⟨v, Silmaril.X86.Ext.HoldsLE.of_stored_self hst hperm⟩
  · obtain ⟨w, hw⟩ := hs d hd
    refine ⟨w, Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst hw ?_⟩
    rw [Silmaril.X86.Ext.length_leBytes]
    have h1 := hne d hd
    have h2 := hb d hd
    omega

/-- The eight slots, as `SpillSlotsHold`. -/
theorem SpillsAt.toSpillSlots {memory : Memory}
    (hfits : (344 : Nat) ≤ rspEntry.toNat)
    (h : SpillsAt memory rspEntry [112, 108, 104, 100, 116, 120, 124, 128]) :
    SpillSlotsHold memory rspEntry := by
  intro j hj
  have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  have hmem : (128 - 4 * j) ∈ [112, 108, 104, 100, 116, 120, 124, 128] := by
    rcases hcase with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  obtain ⟨v, hv⟩ := h _ hmem
  exact ⟨v, by
    have : rspEntry.toNat - 216 - (128 - 4 * j) = rspEntry.toNat - 344 + 4 * j := by omega
    rwa [this] at hv⟩

/-- Where block `150 … 224` is, before the stores. -/
structure BAt (L : Layout) (st rspEntry : Word) (off : Nat) (base cur : MState) : Prop where
  /-- RIP is at function offset `off`. -/
  rip : cur.core.rip = L.textBase + BitVec.ofNat 64 off
  /-- The output pointer. -/
  rdi : cur.core.read .rdi = st
  /-- The frame is still open. -/
  rsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216
  /-- Memory is untouched: the loads, the `xor` and the `lea` write none. -/
  mem : cur.memory = base.memory

/-- Advance `BAt` across a load, the `xor` or the `lea`. -/
theorem BAt.regStep {off len : Nat} {st : Word} {base cur next : MState}
    {dst : Reg} {v : Word}
    (hs : BAt L st rspEntry off base cur)
    (hrip : next.core.rip = L.textBase + BitVec.ofNat 64 (off + len))
    (hw : Silmaril.X86.Ext.WritesReg cur.core next.core dst v)
    (hmem : next.memory = cur.memory)
    (d1 : Reg.rdi ≠ dst) (d2 : Reg.rsp ≠ dst) :
    BAt L st rspEntry (off + len) base next where
  rip := hrip
  rdi := by rw [hw.other _ d1]; exact hs.rdi
  rsp := by rw [hw.other _ d2]; exact hs.rsp
  mem := by rw [hmem]; exact hs.mem

/-- Where block `150 … 224` is, during the stores. -/
structure BSt (L : Layout) (st rspEntry kB : Word) (off : Nat) (S : List Nat)
    (Wv : Nat → SHA256.Kernel.Word) (entry cur : MState) : Prop where
  /-- RIP is at function offset `off`. -/
  rip : cur.core.rip = L.textBase + BitVec.ofNat 64 off
  /-- The round counter, zeroed by the `xor`. -/
  rax : cur.core.read .rax = BitVec.ofNat 64 0
  /-- The `K` pointer, set by the `lea`. -/
  rcx : cur.core.read .rcx = kB
  /-- The frame is still open. -/
  rsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216
  /-- The output pointer. -/
  rdi : cur.core.read .rdi = st
  /-- Everything written so far is inside the modifies set. -/
  frame : Memory.WritesWithin entry.memory cur.memory (Footprint st rspEntry frameSize)
  /-- The sixty-four schedule words still hold what L2 put there. The spill
  stores land in `[rspEntry − 344, rspEntry − 312)` and `w[]` starts at
  `rspEntry − 312`, so they are untouched. -/
  words : WWordsAt cur.memory rspEntry (fun j => (Wv j).setWidth 64) 64
  /-- The callee-saved slots still read. -/
  saved : SavedSlotsAt cur.memory rspEntry (fun j => entry.core.read (savedReg j))
  /-- The spill slots written so far. -/
  spills : SpillsAt cur.memory rspEntry S
  /-- The image is still loaded. -/
  loaded : Loaded cur.memory L.textBase (image L.textBase L.rodataBase)

/-- One spill store. -/
theorem BSt.storeStep (h : SysVEntry L state block rspEntry frameSize m)
    {off len d : Nat} {S : List Nat} {kB : Word} {cur next : MState} {v : Word}
    {Wv : Nat → SHA256.Kernel.Word} (hs : BSt L state rspEntry kB off S Wv m cur)
    (hd : 100 ≤ d ∧ d ≤ 128)
    (hne : ∀ e ∈ S, e + 4 ≤ d ∨ d + 4 ≤ e)
    (hb : ∀ e ∈ S, 100 ≤ e ∧ e ≤ 128)
    (hrip : next.core.rip = L.textBase + BitVec.ofNat 64 (off + len))
    (hregs : Silmaril.X86.Ext.SameRegs cur.core next.core)
    (hst : Stored cur.memory next.memory (rspEntry.toNat - 216 - d)
      (Silmaril.X86.Ext.leBytes v 4)) :
    BSt L state rspEntry kB (off + len) (d :: S) Wv m next := by
  have hlen : (Silmaril.X86.Ext.leBytes v 4).length = 4 :=
    Silmaril.X86.Ext.length_leBytes _ _
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  obtain ⟨hd1, hd2⟩ := hd
  have hd : 100 ≤ d ∧ d ≤ 128 := ⟨hd1, hd2⟩
  have hperm : cur.memory.Permitted .read (rspEntry.toNat - 216 - d) 4 := by
    rw [Silmaril.Process.Memory.WritesWithin.permitted_iff hs.frame]
    exact h.frame_readable (by omega) (by omega) (by omega)
  refine { rip := hrip, rax := ?_, rcx := ?_, rsp := ?_, rdi := ?_, frame := ?_, words := ?_, saved := ?_, spills := ?_, loaded := ?_ }
  · rw [hregs _]; exact hs.rax
  · rw [hregs _]; exact hs.rcx
  · rw [hregs _]; exact hs.rsp
  · rw [hregs _]; exact hs.rdi
  · refine Silmaril.Process.Memory.WritesWithin.step hs.frame hst ?_
    intro o ho
    rw [hlen] at ho
    exact frame_in_footprint (by rw [frameExtent_eq]; omega) (by omega) (by omega)
  · intro j hj
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst (hs.words j hj) (by rw [hlen]; omega)
  · intro j hj
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst (hs.saved j hj) (by rw [hlen]; omega)
  · exact SpillsAt.store hfits hs.spills hne hb hd hperm hst
  · refine Silmaril.X86.Ext.Loaded.of_stored hs.loaded hst ?_
    rw [hlen, image_length]
    exact h.store_disjoint_code (by omega) (by omega)

/-! ### The decode facts of block `150 … 224` -/

set_option maxRecDepth 8000 in
/-- `150`: `mov 0x0(%rdi),%r12d`. -/
theorem blockB_decode_150 : decode ((raw.drop 150).take 3)
    = some (.load .d .r12 cState0Mem, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `153`: `mov 0x4(%rdi),%r8d`. -/
theorem blockB_decode_153 : decode ((raw.drop 153).take 4)
    = some (.load .d .r8 cState4Mem, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `157`: `mov 0x8(%rdi),%rdxd`. -/
theorem blockB_decode_157 : decode ((raw.drop 157).take 3)
    = some (.load .d .rdx cState8Mem, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `160`: `mov 0xc(%rdi),%r11d`. -/
theorem blockB_decode_160 : decode ((raw.drop 160).take 4)
    = some (.load .d .r11 cState12Mem, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `164`: `mov 0x10(%rdi),%r13d`. -/
theorem blockB_decode_164 : decode ((raw.drop 164).take 4)
    = some (.load .d .r13 cState16Mem, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `168`: `mov 0x14(%rdi),%rsid`. -/
theorem blockB_decode_168 : decode ((raw.drop 168).take 3)
    = some (.load .d .rsi cState20Mem, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `171`: `mov 0x18(%rdi),%rbpd`. -/
theorem blockB_decode_171 : decode ((raw.drop 171).take 3)
    = some (.load .d .rbp cState24Mem, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `174`: `mov 0x1c(%rdi),%r14d`. -/
theorem blockB_decode_174 : decode ((raw.drop 174).take 4)
    = some (.load .d .r14 cState28Mem, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `178: 31 c0` — `xor %eax,%eax`. -/
theorem blockB_decode_178 : decode ((raw.drop 178).take 2)
    = some (.alu .d .xor (.reg .rax) .rax, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `187`: `mov %r12d,-0x80(%rsp)`. -/
theorem blockB_decode_187 : decode ((raw.drop 187).take 5)
    = some (.mov .d (.mem cSpill128Mem) .r12, 5) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `192`: `mov %r8d,-0x84(%rsp)`. -/
theorem blockB_decode_192 : decode ((raw.drop 192).take 5)
    = some (.mov .d (.mem cSpill124Mem) .r8, 5) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `197`: `mov %rdxd,-0x88(%rsp)`. -/
theorem blockB_decode_197 : decode ((raw.drop 197).take 4)
    = some (.mov .d (.mem cSpill120Mem) .rdx, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `201`: `mov %r11d,-0x8c(%rsp)`. -/
theorem blockB_decode_201 : decode ((raw.drop 201).take 5)
    = some (.mov .d (.mem cSpill116Mem) .r11, 5) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `206`: `mov %r14d,-0x9c(%rsp)`. -/
theorem blockB_decode_206 : decode ((raw.drop 206).take 5)
    = some (.mov .d (.mem cSpill100Mem) .r14, 5) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `211`: `mov %rbpd,-0x98(%rsp)`. -/
theorem blockB_decode_211 : decode ((raw.drop 211).take 4)
    = some (.mov .d (.mem cSpill104Mem) .rbp, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `215`: `mov %rsid,-0x94(%rsp)`. -/
theorem blockB_decode_215 : decode ((raw.drop 215).take 4)
    = some (.mov .d (.mem cSpill108Mem) .rsi, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `219`: `mov %r13d,-0x90(%rsp)`. -/
theorem blockB_decode_219 : decode ((raw.drop 219).take 5)
    = some (.mov .d (.mem cSpill112Mem) .r13, 5) :=
  decode_raw (by decide +kernel)

/-- **The eight spill slots, by value.** Block `150 … 224` copies `state[]`'s
words into `[rspEntry − 344, rspEntry − 312)` and block `374 … 441` adds them
back: that round trip is the specification's feed-forward, `h0 := a + H.h0`.
Pinning the slots is what turns it from "some bytes come back" into "the entry
hash comes back". -/
def SpillPin (memory : Memory) (rspEntry : Word) (sv : Nat → SHA256.Kernel.Word) : Prop :=
  Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 216 - 128) 4 ((sv 0).setWidth 64) ∧
  Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 216 - 124) 4 ((sv 1).setWidth 64) ∧
  Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 216 - 120) 4 ((sv 2).setWidth 64) ∧
  Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 216 - 116) 4 ((sv 3).setWidth 64) ∧
  Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 216 - 112) 4 ((sv 4).setWidth 64) ∧
  Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 216 - 108) 4 ((sv 5).setWidth 64) ∧
  Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 216 - 104) 4 ((sv 6).setWidth 64) ∧
  Silmaril.X86.Ext.HoldsLE memory (rspEntry.toNat - 216 - 100) 4 ((sv 7).setWidth 64)

set_option maxRecDepth 8000 in
/-- **Block `150 … 224`.** Eight loads of `state[0..8)`, the `xor` that zeroes
the round counter, the relocated `lea` that materialises `K`, and eight stores
spilling `a…h`. Control arrives at L3's head.

This is the only block that reads `state[]`, and the only one containing a
layout-dependent instruction. -/
theorem blockB (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} (hstart : BAt L state rspEntry 150 cur cur)
    (hloaded : Loaded cur.memory L.textBase (image L.textBase L.rodataBase))
    {sv : Nat → SHA256.Kernel.Word}
    (hstate : ∀ j, j < 8 → Silmaril.X86.Ext.HoldsLE cur.memory (state.toNat + 4 * j) 4
      ((sv j).setWidth 64))
    (hframe : Memory.WritesWithin m.memory cur.memory
      (Footprint state rspEntry frameSize))
    {Wv : Nat → SHA256.Kernel.Word}
    (hwords : WWordsAt cur.memory rspEntry (fun j => (Wv j).setWidth 64) 64)
    (hsaved : SavedSlotsAt cur.memory rspEntry (fun j => m.core.read (savedReg j))) :
    ∃ cur', Reaches L.exit cur cur' ∧
      BSt L state rspEntry L.rodataBase 224
        [112, 108, 104, 100, 116, 120, 124, 128] Wv m cur' ∧
      RoundState (sv 0, sv 1, sv 2, sv 3, sv 4, sv 5, sv 6, sv 7) cur' ∧
      SpillPin cur'.memory rspEntry sv := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hsnw : state.toNat + 32 ≤ 2 ^ 64 := by
    have := h.noWrap (stateRegion state) (by simp [regions])
    simpa [stateRegion, Silmaril.Process.addressLimit] using this
  have hsl : ∀ o l : Nat, o + l ≤ relocOffset →
      ((image L.textBase L.rodataBase).drop o).take l = (raw.drop o).take l :=
    fun o l hb => image_slice _ _ hb
  have hsla : ∀ o l : Nat, relocOffset + 4 ≤ o →
      ((image L.textBase L.rodataBase).drop o).take l = (raw.drop o).take l :=
    fun o l hb => image_slice_above _ _ hb
  have hsv1 := hstate 0 (by omega)
  obtain ⟨c1, s1, h1rip, h1w, _, h1mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 150) (len := 3) (width := 4)
      (by rw [hstart.mem]; exact hloaded) hstart.rip (by rw [image_length]; decide)
      (by rw [hsl 150 3 (by decide)]; exact blockB_decode_150)
      (rdiOnly_addr (off := 0) hsnw (by omega) rfl rfl rfl hstart.rdi _) rfl
      (by rw [hstart.mem]; exact hsv1) rfl
  have a1 := hstart.regStep h1rip h1w h1mem (by decide) (by decide)
  have hsv2 := hstate 1 (by omega)
  obtain ⟨c2, s2, h2rip, h2w, _, h2mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 153) (len := 4) (width := 4)
      (by rw [a1.mem]; exact hloaded) a1.rip (by rw [image_length]; decide)
      (by rw [hsl 153 4 (by decide)]; exact blockB_decode_153)
      (rdiOnly_addr (off := 4) hsnw (by omega) rfl rfl rfl a1.rdi _) rfl
      (by rw [a1.mem]; exact hsv2) rfl
  have a2 := a1.regStep h2rip h2w h2mem (by decide) (by decide)
  have hsv3 := hstate 2 (by omega)
  obtain ⟨c3, s3, h3rip, h3w, _, h3mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 157) (len := 3) (width := 4)
      (by rw [a2.mem]; exact hloaded) a2.rip (by rw [image_length]; decide)
      (by rw [hsl 157 3 (by decide)]; exact blockB_decode_157)
      (rdiOnly_addr (off := 8) hsnw (by omega) rfl rfl rfl a2.rdi _) rfl
      (by rw [a2.mem]; exact hsv3) rfl
  have a3 := a2.regStep h3rip h3w h3mem (by decide) (by decide)
  have hsv4 := hstate 3 (by omega)
  obtain ⟨c4, s4, h4rip, h4w, _, h4mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 160) (len := 4) (width := 4)
      (by rw [a3.mem]; exact hloaded) a3.rip (by rw [image_length]; decide)
      (by rw [hsl 160 4 (by decide)]; exact blockB_decode_160)
      (rdiOnly_addr (off := 12) hsnw (by omega) rfl rfl rfl a3.rdi _) rfl
      (by rw [a3.mem]; exact hsv4) rfl
  have a4 := a3.regStep h4rip h4w h4mem (by decide) (by decide)
  have hsv5 := hstate 4 (by omega)
  obtain ⟨c5, s5, h5rip, h5w, _, h5mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 164) (len := 4) (width := 4)
      (by rw [a4.mem]; exact hloaded) a4.rip (by rw [image_length]; decide)
      (by rw [hsl 164 4 (by decide)]; exact blockB_decode_164)
      (rdiOnly_addr (off := 16) hsnw (by omega) rfl rfl rfl a4.rdi _) rfl
      (by rw [a4.mem]; exact hsv5) rfl
  have a5 := a4.regStep h5rip h5w h5mem (by decide) (by decide)
  have hsv6 := hstate 5 (by omega)
  obtain ⟨c6, s6, h6rip, h6w, _, h6mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 168) (len := 3) (width := 4)
      (by rw [a5.mem]; exact hloaded) a5.rip (by rw [image_length]; decide)
      (by rw [hsl 168 3 (by decide)]; exact blockB_decode_168)
      (rdiOnly_addr (off := 20) hsnw (by omega) rfl rfl rfl a5.rdi _) rfl
      (by rw [a5.mem]; exact hsv6) rfl
  have a6 := a5.regStep h6rip h6w h6mem (by decide) (by decide)
  have hsv7 := hstate 6 (by omega)
  obtain ⟨c7, s7, h7rip, h7w, _, h7mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 171) (len := 3) (width := 4)
      (by rw [a6.mem]; exact hloaded) a6.rip (by rw [image_length]; decide)
      (by rw [hsl 171 3 (by decide)]; exact blockB_decode_171)
      (rdiOnly_addr (off := 24) hsnw (by omega) rfl rfl rfl a6.rdi _) rfl
      (by rw [a6.mem]; exact hsv7) rfl
  have a7 := a6.regStep h7rip h7w h7mem (by decide) (by decide)
  have hsv8 := hstate 7 (by omega)
  obtain ⟨c8, s8, h8rip, h8w, _, h8mem⟩ :=
    Silmaril.X86.Ext.stepOpt_load (exit := L.exit) (offset := 174) (len := 4) (width := 4)
      (by rw [a7.mem]; exact hloaded) a7.rip (by rw [image_length]; decide)
      (by rw [hsl 174 4 (by decide)]; exact blockB_decode_174)
      (rdiOnly_addr (off := 28) hsnw (by omega) rfl rfl rfl a7.rdi _) rfl
      (by rw [a7.mem]; exact hsv8) rfl
  have a8 := a7.regStep h8rip h8w h8mem (by decide) (by decide)
  obtain ⟨c9, s9, h9rip, h9w, _, h9mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 178) (len := 2)
      (by rw [a8.mem]; exact hloaded) a8.rip (by rw [image_length]; decide)
      (by rw [hsl 178 2 (by decide)]; exact blockB_decode_178) (by decide) rfl
  have a9 := a8.regStep h9rip h9w h9mem (by decide) (by decide)
  have h9rax : c9.core.read .rax = BitVec.ofNat 64 0 := by
    rw [h9w.target]
    show ((Silmaril.X86.Ext.Sz.d.read c8.core Reg.rax) ^^^
      (Silmaril.X86.Ext.Sz.d.read c8.core Reg.rax)).setWidth 64 = _
    rw [BitVec.xor_self]; rfl
  obtain ⟨c10, s10, h10rip, h10w, _, h10mem⟩ :=
    stepOpt_lea (exit := L.exit) (offset := 180) (len := 7)
      (by rw [a9.mem]; exact hloaded) a9.rip (by rw [image_length]; decide)
      (image_decode_lea L) (kLea_value L h.relocFits _)
  have a10 := a9.regStep h10rip h10w h10mem (by decide) (by decide)
  have h10rax : c10.core.read .rax = BitVec.ofNat 64 0 := by
    rw [h10w.other _ (by decide)]; exact h9rax
  have b10 : BSt L state rspEntry L.rodataBase 187 [] Wv m c10 :=
    { rip := a10.rip, rax := h10rax, rcx := h10w.target, rsp := a10.rsp, rdi := a10.rdi
      frame := by rw [a10.mem]; exact hframe
      words := by rw [a10.mem]; exact hwords
      saved := by rw [a10.mem]; exact hsaved
      spills := by intro d hd; simp at hd
      loaded := by rw [a10.mem]; exact hloaded }
  obtain ⟨c11, s11, h11rip, h11regs, _, h11st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 187) (len := 5) (width := 4)
      b10.loaded b10.rip (by rw [image_length]; decide)
      (by rw [hsla 187 5 (by decide)]; exact blockB_decode_187)
      (by rw [rspOnly_addr (off := 128) hfits (by omega) rfl rfl rfl (by omega) b10.rsp _])
      rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b10.frame]
          exact h.frame_writable (by omega) (by omega) (by omega))
  have b11 := BSt.storeStep h b10 (by omega) (by decide) (by decide) h11rip h11regs h11st
  obtain ⟨c12, s12, h12rip, h12regs, _, h12st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 192) (len := 5) (width := 4)
      b11.loaded b11.rip (by rw [image_length]; decide)
      (by rw [hsla 192 5 (by decide)]; exact blockB_decode_192)
      (by rw [rspOnly_addr (off := 124) hfits (by omega) rfl rfl rfl (by omega) b11.rsp _])
      rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b11.frame]
          exact h.frame_writable (by omega) (by omega) (by omega))
  have b12 := BSt.storeStep h b11 (by omega) (by decide) (by decide) h12rip h12regs h12st
  obtain ⟨c13, s13, h13rip, h13regs, _, h13st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 197) (len := 4) (width := 4)
      b12.loaded b12.rip (by rw [image_length]; decide)
      (by rw [hsla 197 4 (by decide)]; exact blockB_decode_197)
      (by rw [rspOnly_addr (off := 120) hfits (by omega) rfl rfl rfl (by omega) b12.rsp _])
      rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b12.frame]
          exact h.frame_writable (by omega) (by omega) (by omega))
  have b13 := BSt.storeStep h b12 (by omega) (by decide) (by decide) h13rip h13regs h13st
  obtain ⟨c14, s14, h14rip, h14regs, _, h14st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 201) (len := 5) (width := 4)
      b13.loaded b13.rip (by rw [image_length]; decide)
      (by rw [hsla 201 5 (by decide)]; exact blockB_decode_201)
      (by rw [rspOnly_addr (off := 116) hfits (by omega) rfl rfl rfl (by omega) b13.rsp _])
      rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b13.frame]
          exact h.frame_writable (by omega) (by omega) (by omega))
  have b14 := BSt.storeStep h b13 (by omega) (by decide) (by decide) h14rip h14regs h14st
  obtain ⟨c15, s15, h15rip, h15regs, _, h15st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 206) (len := 5) (width := 4)
      b14.loaded b14.rip (by rw [image_length]; decide)
      (by rw [hsla 206 5 (by decide)]; exact blockB_decode_206)
      (by rw [rspOnly_addr (off := 100) hfits (by omega) rfl rfl rfl (by omega) b14.rsp _])
      rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b14.frame]
          exact h.frame_writable (by omega) (by omega) (by omega))
  have b15 := BSt.storeStep h b14 (by omega) (by decide) (by decide) h15rip h15regs h15st
  obtain ⟨c16, s16, h16rip, h16regs, _, h16st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 211) (len := 4) (width := 4)
      b15.loaded b15.rip (by rw [image_length]; decide)
      (by rw [hsla 211 4 (by decide)]; exact blockB_decode_211)
      (by rw [rspOnly_addr (off := 104) hfits (by omega) rfl rfl rfl (by omega) b15.rsp _])
      rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b15.frame]
          exact h.frame_writable (by omega) (by omega) (by omega))
  have b16 := BSt.storeStep h b15 (by omega) (by decide) (by decide) h16rip h16regs h16st
  obtain ⟨c17, s17, h17rip, h17regs, _, h17st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 215) (len := 4) (width := 4)
      b16.loaded b16.rip (by rw [image_length]; decide)
      (by rw [hsla 215 4 (by decide)]; exact blockB_decode_215)
      (by rw [rspOnly_addr (off := 108) hfits (by omega) rfl rfl rfl (by omega) b16.rsp _])
      rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b16.frame]
          exact h.frame_writable (by omega) (by omega) (by omega))
  have b17 := BSt.storeStep h b16 (by omega) (by decide) (by decide) h17rip h17regs h17st
  obtain ⟨c18, s18, h18rip, h18regs, _, h18st⟩ :=
    Silmaril.X86.Ext.stepOpt_store_reg (exit := L.exit) (offset := 219) (len := 5) (width := 4)
      b17.loaded b17.rip (by rw [image_length]; decide)
      (by rw [hsla 219 5 (by decide)]; exact blockB_decode_219)
      (by rw [rspOnly_addr (off := 112) hfits (by omega) rfl rfl rfl (by omega) b17.rsp _])
      rfl rfl
      (by rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b17.frame]
          exact h.frame_writable (by omega) (by omega) (by omega))
  have b18 := BSt.storeStep h b17 (by omega) (by decide) (by decide) h18rip h18regs h18st
  have d0 : read32 c10.core Reg.r12 = sv 0 := by
    rw [read_d_of_other (r := Reg.r12) h10w (by decide), read_d_of_other (r := Reg.r12) h9w (by decide), read_d_of_other (r := Reg.r12) h8w (by decide), read_d_of_other (r := Reg.r12) h7w (by decide), read_d_of_other (r := Reg.r12) h6w (by decide), read_d_of_other (r := Reg.r12) h5w (by decide), read_d_of_other (r := Reg.r12) h4w (by decide), read_d_of_other (r := Reg.r12) h3w (by decide), read_d_of_other (r := Reg.r12) h2w (by decide), read_d_of_writes h1w]
    exact trunc32 _
  have d1 : read32 c10.core Reg.r8 = sv 1 := by
    rw [read_d_of_other (r := Reg.r8) h10w (by decide), read_d_of_other (r := Reg.r8) h9w (by decide), read_d_of_other (r := Reg.r8) h8w (by decide), read_d_of_other (r := Reg.r8) h7w (by decide), read_d_of_other (r := Reg.r8) h6w (by decide), read_d_of_other (r := Reg.r8) h5w (by decide), read_d_of_other (r := Reg.r8) h4w (by decide), read_d_of_other (r := Reg.r8) h3w (by decide), read_d_of_writes h2w]
    exact trunc32 _
  have d2 : read32 c10.core Reg.rdx = sv 2 := by
    rw [read_d_of_other (r := Reg.rdx) h10w (by decide), read_d_of_other (r := Reg.rdx) h9w (by decide), read_d_of_other (r := Reg.rdx) h8w (by decide), read_d_of_other (r := Reg.rdx) h7w (by decide), read_d_of_other (r := Reg.rdx) h6w (by decide), read_d_of_other (r := Reg.rdx) h5w (by decide), read_d_of_other (r := Reg.rdx) h4w (by decide), read_d_of_writes h3w]
    exact trunc32 _
  have d3 : read32 c10.core Reg.r11 = sv 3 := by
    rw [read_d_of_other (r := Reg.r11) h10w (by decide), read_d_of_other (r := Reg.r11) h9w (by decide), read_d_of_other (r := Reg.r11) h8w (by decide), read_d_of_other (r := Reg.r11) h7w (by decide), read_d_of_other (r := Reg.r11) h6w (by decide), read_d_of_other (r := Reg.r11) h5w (by decide), read_d_of_writes h4w]
    exact trunc32 _
  have d4 : read32 c10.core Reg.r13 = sv 4 := by
    rw [read_d_of_other (r := Reg.r13) h10w (by decide), read_d_of_other (r := Reg.r13) h9w (by decide), read_d_of_other (r := Reg.r13) h8w (by decide), read_d_of_other (r := Reg.r13) h7w (by decide), read_d_of_other (r := Reg.r13) h6w (by decide), read_d_of_writes h5w]
    exact trunc32 _
  have d5 : read32 c10.core Reg.rsi = sv 5 := by
    rw [read_d_of_other (r := Reg.rsi) h10w (by decide), read_d_of_other (r := Reg.rsi) h9w (by decide), read_d_of_other (r := Reg.rsi) h8w (by decide), read_d_of_other (r := Reg.rsi) h7w (by decide), read_d_of_writes h6w]
    exact trunc32 _
  have d6 : read32 c10.core Reg.rbp = sv 6 := by
    rw [read_d_of_other (r := Reg.rbp) h10w (by decide), read_d_of_other (r := Reg.rbp) h9w (by decide), read_d_of_other (r := Reg.rbp) h8w (by decide), read_d_of_writes h7w]
    exact trunc32 _
  have d7 : read32 c10.core Reg.r14 = sv 7 := by
    rw [read_d_of_other (r := Reg.r14) h10w (by decide), read_d_of_other (r := Reg.r14) h9w (by decide), read_d_of_writes h8w]
    exact trunc32 _
  have hp11 : c10.memory.Permitted .read (rspEntry.toNat - 216 - 128) 4 := by
    rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b10.frame]
    exact h.frame_readable (by omega) (by omega) (by omega)
  have hp12 : c11.memory.Permitted .read (rspEntry.toNat - 216 - 124) 4 := by
    rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b11.frame]
    exact h.frame_readable (by omega) (by omega) (by omega)
  have hp13 : c12.memory.Permitted .read (rspEntry.toNat - 216 - 120) 4 := by
    rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b12.frame]
    exact h.frame_readable (by omega) (by omega) (by omega)
  have hp14 : c13.memory.Permitted .read (rspEntry.toNat - 216 - 116) 4 := by
    rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b13.frame]
    exact h.frame_readable (by omega) (by omega) (by omega)
  have hp15 : c14.memory.Permitted .read (rspEntry.toNat - 216 - 100) 4 := by
    rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b14.frame]
    exact h.frame_readable (by omega) (by omega) (by omega)
  have hp16 : c15.memory.Permitted .read (rspEntry.toNat - 216 - 104) 4 := by
    rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b15.frame]
    exact h.frame_readable (by omega) (by omega) (by omega)
  have hp17 : c16.memory.Permitted .read (rspEntry.toNat - 216 - 108) 4 := by
    rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b16.frame]
    exact h.frame_readable (by omega) (by omega) (by omega)
  have hp18 : c17.memory.Permitted .read (rspEntry.toNat - 216 - 112) 4 := by
    rw [Silmaril.Process.Memory.WritesWithin.permitted_iff b17.frame]
    exact h.frame_readable (by omega) (by omega) (by omega)
  have hv0 : (Silmaril.X86.Ext.Sz.d.read c10.core Reg.r12).setWidth 64
      = (sv 0).setWidth 64 := by
    rw [show Silmaril.X86.Ext.Sz.d.read c10.core Reg.r12 = read32 c10.core Reg.r12 from rfl, d0]
    try rfl
  have p0 : Silmaril.X86.Ext.HoldsLE c18.memory (rspEntry.toNat - 216 - 128) 4
      ((sv 0).setWidth 64) := by
    rw [← hv0]
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h18st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h17st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h15st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h14st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h13st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h12st (Silmaril.X86.Ext.HoldsLE.of_stored_self h11st hp11)
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
  have hv1 : (Silmaril.X86.Ext.Sz.d.read c11.core Reg.r8).setWidth 64
      = (sv 1).setWidth 64 := by
    rw [show Silmaril.X86.Ext.Sz.d.read c11.core Reg.r8 = read32 c11.core Reg.r8 from rfl, read32_of_sameRegs h11regs, d1]
    try rfl
  have p1 : Silmaril.X86.Ext.HoldsLE c18.memory (rspEntry.toNat - 216 - 124) 4
      ((sv 1).setWidth 64) := by
    rw [← hv1]
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h18st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h17st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h15st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h14st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h13st (Silmaril.X86.Ext.HoldsLE.of_stored_self h12st hp12)
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
  have hv2 : (Silmaril.X86.Ext.Sz.d.read c12.core Reg.rdx).setWidth 64
      = (sv 2).setWidth 64 := by
    rw [show Silmaril.X86.Ext.Sz.d.read c12.core Reg.rdx = read32 c12.core Reg.rdx from rfl, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, d2]
    try rfl
  have p2 : Silmaril.X86.Ext.HoldsLE c18.memory (rspEntry.toNat - 216 - 120) 4
      ((sv 2).setWidth 64) := by
    rw [← hv2]
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h18st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h17st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h15st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h14st (Silmaril.X86.Ext.HoldsLE.of_stored_self h13st hp13)
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
  have hv3 : (Silmaril.X86.Ext.Sz.d.read c13.core Reg.r11).setWidth 64
      = (sv 3).setWidth 64 := by
    rw [show Silmaril.X86.Ext.Sz.d.read c13.core Reg.r11 = read32 c13.core Reg.r11 from rfl, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, d3]
    try rfl
  have p3 : Silmaril.X86.Ext.HoldsLE c18.memory (rspEntry.toNat - 216 - 116) 4
      ((sv 3).setWidth 64) := by
    rw [← hv3]
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h18st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h17st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h15st (Silmaril.X86.Ext.HoldsLE.of_stored_self h14st hp14)
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
  have hv7 : (Silmaril.X86.Ext.Sz.d.read c14.core Reg.r14).setWidth 64
      = (sv 7).setWidth 64 := by
    rw [show Silmaril.X86.Ext.Sz.d.read c14.core Reg.r14 = read32 c14.core Reg.r14 from rfl, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, d7]
    try rfl
  have p7 : Silmaril.X86.Ext.HoldsLE c18.memory (rspEntry.toNat - 216 - 100) 4
      ((sv 7).setWidth 64) := by
    rw [← hv7]
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h18st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h17st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h16st (Silmaril.X86.Ext.HoldsLE.of_stored_self h15st hp15)
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
  have hv6 : (Silmaril.X86.Ext.Sz.d.read c15.core Reg.rbp).setWidth 64
      = (sv 6).setWidth 64 := by
    rw [show Silmaril.X86.Ext.Sz.d.read c15.core Reg.rbp = read32 c15.core Reg.rbp from rfl, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, d6]
    try rfl
  have p6 : Silmaril.X86.Ext.HoldsLE c18.memory (rspEntry.toNat - 216 - 104) 4
      ((sv 6).setWidth 64) := by
    rw [← hv6]
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h18st (Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h17st (Silmaril.X86.Ext.HoldsLE.of_stored_self h16st hp16)
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega))
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
  have hv5 : (Silmaril.X86.Ext.Sz.d.read c16.core Reg.rsi).setWidth 64
      = (sv 5).setWidth 64 := by
    rw [show Silmaril.X86.Ext.Sz.d.read c16.core Reg.rsi = read32 c16.core Reg.rsi from rfl, read32_of_sameRegs h16regs, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, d5]
    try rfl
  have p5 : Silmaril.X86.Ext.HoldsLE c18.memory (rspEntry.toNat - 216 - 108) 4
      ((sv 5).setWidth 64) := by
    rw [← hv5]
    exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint h18st (Silmaril.X86.Ext.HoldsLE.of_stored_self h17st hp17)
        (by rw [Silmaril.X86.Ext.length_leBytes]; omega)
  have hv4 : (Silmaril.X86.Ext.Sz.d.read c17.core Reg.r13).setWidth 64
      = (sv 4).setWidth 64 := by
    rw [show Silmaril.X86.Ext.Sz.d.read c17.core Reg.r13 = read32 c17.core Reg.r13 from rfl, read32_of_sameRegs h17regs, read32_of_sameRegs h16regs, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, d4]
    try rfl
  have p4 : Silmaril.X86.Ext.HoldsLE c18.memory (rspEntry.toNat - 216 - 112) 4
      ((sv 4).setWidth 64) := by
    rw [← hv4]
    exact Silmaril.X86.Ext.HoldsLE.of_stored_self h18st hp18
  refine ⟨c18, Reaches.cons s1 (Reaches.cons s2 (Reaches.cons s3 (Reaches.cons s4 (Reaches.cons s5 (Reaches.cons s6 (Reaches.cons s7 (Reaches.cons s8 (Reaches.cons s9 (Reaches.cons s10 (Reaches.cons s11 (Reaches.cons s12 (Reaches.cons s13 (Reaches.cons s14 (Reaches.cons s15 (Reaches.cons s16 (Reaches.cons s17 (Reaches.one s18))))))))))))))))), b18, ?_, ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩⟩
  have e1 : read32 c18.core Reg.r12 = sv 0 := by
    rw [read32_of_sameRegs h18regs, read32_of_sameRegs h17regs, read32_of_sameRegs h16regs, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, read_d_of_other (r := Reg.r12) h10w (by decide), read_d_of_other (r := Reg.r12) h9w (by decide), read_d_of_other (r := Reg.r12) h8w (by decide), read_d_of_other (r := Reg.r12) h7w (by decide), read_d_of_other (r := Reg.r12) h6w (by decide), read_d_of_other (r := Reg.r12) h5w (by decide), read_d_of_other (r := Reg.r12) h4w (by decide), read_d_of_other (r := Reg.r12) h3w (by decide), read_d_of_other (r := Reg.r12) h2w (by decide), read_d_of_writes h1w]
    exact trunc32 _
  have e2 : read32 c18.core Reg.r8 = sv 1 := by
    rw [read32_of_sameRegs h18regs, read32_of_sameRegs h17regs, read32_of_sameRegs h16regs, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, read_d_of_other (r := Reg.r8) h10w (by decide), read_d_of_other (r := Reg.r8) h9w (by decide), read_d_of_other (r := Reg.r8) h8w (by decide), read_d_of_other (r := Reg.r8) h7w (by decide), read_d_of_other (r := Reg.r8) h6w (by decide), read_d_of_other (r := Reg.r8) h5w (by decide), read_d_of_other (r := Reg.r8) h4w (by decide), read_d_of_other (r := Reg.r8) h3w (by decide), read_d_of_writes h2w]
    exact trunc32 _
  have e3 : read32 c18.core Reg.rdx = sv 2 := by
    rw [read32_of_sameRegs h18regs, read32_of_sameRegs h17regs, read32_of_sameRegs h16regs, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, read_d_of_other (r := Reg.rdx) h10w (by decide), read_d_of_other (r := Reg.rdx) h9w (by decide), read_d_of_other (r := Reg.rdx) h8w (by decide), read_d_of_other (r := Reg.rdx) h7w (by decide), read_d_of_other (r := Reg.rdx) h6w (by decide), read_d_of_other (r := Reg.rdx) h5w (by decide), read_d_of_other (r := Reg.rdx) h4w (by decide), read_d_of_writes h3w]
    exact trunc32 _
  have e4 : read32 c18.core Reg.r11 = sv 3 := by
    rw [read32_of_sameRegs h18regs, read32_of_sameRegs h17regs, read32_of_sameRegs h16regs, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, read_d_of_other (r := Reg.r11) h10w (by decide), read_d_of_other (r := Reg.r11) h9w (by decide), read_d_of_other (r := Reg.r11) h8w (by decide), read_d_of_other (r := Reg.r11) h7w (by decide), read_d_of_other (r := Reg.r11) h6w (by decide), read_d_of_other (r := Reg.r11) h5w (by decide), read_d_of_writes h4w]
    exact trunc32 _
  have e5 : read32 c18.core Reg.r13 = sv 4 := by
    rw [read32_of_sameRegs h18regs, read32_of_sameRegs h17regs, read32_of_sameRegs h16regs, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, read_d_of_other (r := Reg.r13) h10w (by decide), read_d_of_other (r := Reg.r13) h9w (by decide), read_d_of_other (r := Reg.r13) h8w (by decide), read_d_of_other (r := Reg.r13) h7w (by decide), read_d_of_other (r := Reg.r13) h6w (by decide), read_d_of_writes h5w]
    exact trunc32 _
  have e6 : read32 c18.core Reg.rsi = sv 5 := by
    rw [read32_of_sameRegs h18regs, read32_of_sameRegs h17regs, read32_of_sameRegs h16regs, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, read_d_of_other (r := Reg.rsi) h10w (by decide), read_d_of_other (r := Reg.rsi) h9w (by decide), read_d_of_other (r := Reg.rsi) h8w (by decide), read_d_of_other (r := Reg.rsi) h7w (by decide), read_d_of_writes h6w]
    exact trunc32 _
  have e7 : read32 c18.core Reg.rbp = sv 6 := by
    rw [read32_of_sameRegs h18regs, read32_of_sameRegs h17regs, read32_of_sameRegs h16regs, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, read_d_of_other (r := Reg.rbp) h10w (by decide), read_d_of_other (r := Reg.rbp) h9w (by decide), read_d_of_other (r := Reg.rbp) h8w (by decide), read_d_of_writes h7w]
    exact trunc32 _
  have e8 : read32 c18.core Reg.r14 = sv 7 := by
    rw [read32_of_sameRegs h18regs, read32_of_sameRegs h17regs, read32_of_sameRegs h16regs, read32_of_sameRegs h15regs, read32_of_sameRegs h14regs, read32_of_sameRegs h13regs, read32_of_sameRegs h12regs, read32_of_sameRegs h11regs, read_d_of_other (r := Reg.r14) h10w (by decide), read_d_of_other (r := Reg.r14) h9w (by decide), read_d_of_writes h8w]
    exact trunc32 _
  show (sv 0, sv 1, sv 2, sv 3, sv 4, sv 5, sv 6, sv 7) = _
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
/-! ### L3's mathematics: the four crossings

The round function is where the object's formulation and the specification's
differ most, and all of the difference is in four small identities. None needs
bit-blasting; `bv_decide` and `native decision tactic` are not used anywhere in this
file.

These are stated over `SHA256.Kernel.Word` and mention no x86 at all, so they
belong beside `Ch`/`Maj`/`Sigma0`/`Sigma1` in `Crypto/SHA256/Kernel.lean`
rather than here, and every track proving a round loop will want them. They
are local only until that move is routed. -/

/-- `Sigma1` in the association the object builds it: `rol 26`, `rol 21`,
`xor`, `rol 7`, `xor`. -/
theorem sigma1_eq_rol (x : SHA256.Kernel.Word) :
    (x.rotateLeft 7 ^^^ (x.rotateLeft 21 ^^^ x.rotateLeft 26)) = SHA256.Kernel.Sigma1 x := by
  rw [rotateLeft_eq_rotateRight x (by omega) (by omega),
    rotateLeft_eq_rotateRight x (by omega) (by omega),
    rotateLeft_eq_rotateRight x (by omega) (by omega)]
  simp only [show (32 : Nat) - 7 = 25 from rfl, show (32 : Nat) - 21 = 11 from rfl,
    show (32 : Nat) - 26 = 6 from rfl, SHA256.Kernel.Sigma1]
  rw [BitVec.xor_assoc, BitVec.xor_comm (x.rotateRight 25), ← BitVec.xor_assoc,
    BitVec.xor_comm (x.rotateRight 11) (x.rotateRight 6)]

/-- `Sigma0`, likewise: `rol 30`, `rol 19`, `xor`, `rol 10`, `xor`. -/
theorem sigma0_eq_rol (x : SHA256.Kernel.Word) :
    (x.rotateLeft 10 ^^^ (x.rotateLeft 19 ^^^ x.rotateLeft 30)) = SHA256.Kernel.Sigma0 x := by
  rw [rotateLeft_eq_rotateRight x (by omega) (by omega),
    rotateLeft_eq_rotateRight x (by omega) (by omega),
    rotateLeft_eq_rotateRight x (by omega) (by omega)]
  simp only [show (32 : Nat) - 10 = 22 from rfl, show (32 : Nat) - 19 = 13 from rfl,
    show (32 : Nat) - 30 = 2 from rfl, SHA256.Kernel.Sigma0]
  rw [BitVec.xor_assoc, BitVec.xor_comm (x.rotateRight 22), ← BitVec.xor_assoc,
    BitVec.xor_comm (x.rotateRight 13) (x.rotateRight 2)]

/-- The two halves of `Ch` are bit-disjoint: one is masked by `x`, the other
by its complement. -/
theorem ch_disjoint (x y z : SHA256.Kernel.Word) :
    (x &&& y) &&& ((~~~x) &&& z) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not]
  cases hx : x.getLsbD i <;> simp

/-- Disjoint `|||` is `^^^`. -/
theorem or_eq_xor_of_and_eq_zero {w : Nat} (x y : BitVec w) (h : x &&& y = 0#w) :
    x ||| y = x ^^^ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hi := congrArg (fun v => BitVec.getLsbD v i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all

/-- **`Ch` with `+` for `^^^`.** The object *adds* the two halves of `Ch`
rather than xoring them, because addition is what the rest of `T1` needs
anyway.

**This is not a fact about `+` and `^^^`.** They agree here only because the
two halves are bit-disjoint — one is masked by `x`, the other by `~~~x` — so
the addition carries nowhere. That disjointness is a property of **`Ch`'s
shape**, not of addition, and `x + y = x ^^^ y` is false in general: take
`x = y = 1`. A reader who lifts this lemma out of its context, or who
generalises it by dropping the `Ch` structure, is lifting a falsehood.
`ch_disjoint` is the hypothesis that makes it true and it is discharged here,
not assumed. -/
theorem ch_eq_add (x y z : SHA256.Kernel.Word) :
    (y &&& x) + ((~~~x) &&& z) = SHA256.Kernel.Ch x y z := by
  rw [BitVec.and_comm y x,
    BitVec.add_eq_or_of_and_eq_zero _ _ (ch_disjoint x y z),
    or_eq_xor_of_and_eq_zero _ _ (ch_disjoint x y z)]
  rfl

/-- **`Maj`, factored as the compiler emits it.** Three `and`s and two `xor`s
in the spec; the object shares a subexpression and uses two `and`s, one `xor`
for the operand and one for the result. -/
theorem maj_eq_factored (x y z : SHA256.Kernel.Word) :
    ((y ^^^ z) &&& x) ^^^ (y &&& z) = SHA256.Kernel.Maj x y z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [SHA256.Kernel.Maj, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> cases hz : z.getLsbD i <;> simp

/-! ## L3: the sixty-four rounds

Forty-eight instructions, `t = 0 … 63`, at function offsets 224 … 373 with a
**rel32** `jne` backedge (`0F 85`) and a fallthrough at 374.

Two things make L3 the cheapest of the three loops to prove weakly, despite
being the longest:

* **It writes no memory at all.** The round state `a…h` lives in registers;
  the spill slots at `[rsp-128, rsp-96)` are written before the loop and read
  after it. So memory is *constant* through L3, and every memory-shaped field
  of the invariant — the footprint, `WWordsRead`, `SavedSlotsHold` — is
  preserved for free.
* **Its two reads come from facts already established.** `K[t]` comes from
  the contract's `kTable`, which pins *contents*; `w[t]` from `WWordsRead`,
  which L1 and L2 established.

The counter is `%rax` holding `4t` — byte-scaled, not element-scaled — and
`%rcx` holds the address of `K`. Both must be in the invariant: `%rcx` because
the `K` read is `(%rax,%rcx,1)`, with the table address in the *index*. -/

/-- `(%rax,%rcx,1)` — `K[t]`, with the table address in the index register. -/
def l3KMem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rax, index := some { reg := .rcx, scale := 0#2, ne_rsp := by decide },
    disp := 0x00000000#32, rip_no_index := by intro hc; exact absurd hc (by decide) }

/-- `-0x60(%rsp,%rax,1)` — `w[t]`, with `%rax = 4t`. -/
def l3WMem : Silmaril.X86.Ext.Mem :=
  { base := .reg .rsp, index := some { reg := .rax, scale := 0#2, ne_rsp := by decide },
    disp := 0xffffffa0#32, rip_no_index := by intro hc; exact absurd hc (by decide) }

/-- `not r`, successor left opaque. No flags (`NOT` is the one ALU-shaped
instruction that leaves them alone), no memory. -/
theorem stepOpt_not_reg {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {sz : Silmaril.X86.Ext.Sz} {r : Reg}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.unary sz .not (.reg r), len)) :
    ∃ next, stepOpt exit mm = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      Silmaril.X86.Ext.WritesReg mm.core next.core r ((~~~(sz.read mm.core r)).setWidth 64) ∧
      next.core.flags = mm.core.flags ∧ next.memory = mm.memory := by
  refine Silmaril.X86.Ext.opaque_writeReg_noFlags ?_
  have hl : (Instr.unary sz .not (.reg r)).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM,
    Silmaril.X86.Ext.Sz.write]

/-- `cmp $imm, %rax` in the accumulator form (`3D id`), successor left opaque.
Flags only. -/
theorem stepOpt_cmpA {exit base : Word} {bytes : List Byte} {mm : MState}
    {offset len : Nat} {sz : Silmaril.X86.Ext.Sz} {imm : BitVec 32}
    (loaded : Loaded mm.memory base bytes)
    (at_offset : mm.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : decode ((bytes.drop offset).take len) = some (.aluA sz .cmp imm, len)) :
    ∃ next, stepOpt exit mm = some next ∧
      next.core.rip = base + BitVec.ofNat 64 (offset + len) ∧
      Silmaril.X86.Ext.SameRegs mm.core next.core ∧
      next.core.flags = Silmaril.X86.Ext.AluOp.flagsN .cmp (sz.read mm.core .rax)
        (imm.signExtend sz.bits) ∧
      next.memory = mm.memory := by
  refine Silmaril.X86.Ext.opaque_flagsOnly ?_
  have hl : (Instr.aluA sz .cmp imm).length = len := (decode_length decoded).1.symm
  refine stepOpt_of_loaded (len := len) loaded at_offset fits decoded
    (by intro hc; cases hc) ?_
  simp only [exec, hl, at_offset, Silmaril.X86.Ext.rip_advance base rfl,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
    ite_true]

/-- Where the L3 trace is partway through. `%rcx` is tracked because the `K`
read puts the table address in the *index* register; `%rax` holds `4t`, not
`t`. Memory is constant: L3 writes none. -/
structure L3At (L : Layout) (rspEntry kBase st : Word) (off t : Nat) (base cur : MState) :
    Prop where
  /-- RIP is at function offset `off`. -/
  rip : cur.core.rip = L.textBase + BitVec.ofNat 64 off
  /-- The byte-scaled counter. -/
  rax : cur.core.read .rax = BitVec.ofNat 64 (4 * t)
  /-- The address of `sha256_compress.K`. -/
  rcx : cur.core.read .rcx = kBase
  /-- The frame is open. -/
  rsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216
  /-- The output pointer. -/
  rdi : cur.core.read .rdi = st
  /-- Memory is untouched: L3 never writes. -/
  mem : cur.memory = base.memory

/-- Advance `L3At` across a step that writes one scratch register. Forty-five
of L3's forty-eight instructions are of this shape. -/
theorem L3At.regStep {off len t : Nat} {kBase : Word} {base cur next : MState}
    {dst : Reg} {v : Word}
    (hs : L3At L rspEntry kBase state off t base cur)
    (hrip : next.core.rip = L.textBase + BitVec.ofNat 64 (off + len))
    (hw : Silmaril.X86.Ext.WritesReg cur.core next.core dst v)
    (hmem : next.memory = cur.memory)
    (d1 : Reg.rax ≠ dst) (d2 : Reg.rcx ≠ dst) (d3 : Reg.rsp ≠ dst) (d4 : Reg.rdi ≠ dst) :
    L3At L rspEntry kBase state (off + len) t base next where
  rip := hrip
  rax := by rw [hw.other _ d1]; exact hs.rax
  rcx := by rw [hw.other _ d2]; exact hs.rcx
  rsp := by rw [hw.other _ d3]; exact hs.rsp
  rdi := by rw [hw.other _ d4]; exact hs.rdi
  mem := by rw [hmem]; exact hs.mem

/-- The address of `K[t]`: `(%rax,%rcx,1)` with `%rax = 4t` and `%rcx` the
table base. -/
theorem l3K_addr {cur : MState} {t : Nat} {kBase : Word}
    (hnw : kBase.toNat + 256 ≤ 2 ^ 64) (ht : t < 64)
    (hrax : cur.core.read .rax = BitVec.ofNat 64 (4 * t))
    (hrcx : cur.core.read .rcx = kBase) (next : Word) :
    (l3KMem.addr cur.core next).toNat = kBase.toNat + 4 * t := by
  have hlt := kBase.isLt
  simp only [l3KMem, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Base.value_reg,
    Option.map_some, Option.getD_some, Silmaril.X86.Ext.Index.value, hrax, hrcx,
    show ((0x00000000#32 : BitVec 32).signExtend 64) = 0#64 from rfl,
    show (0#2 : BitVec 2).toNat = 0 from rfl, BitVec.shiftLeft_zero, BitVec.add_zero]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4 * t < 2 ^ 64 by omega)]
  omega

/-- The address of `w[t]`: `-0x60(%rsp,%rax,1)` with `%rax = 4t`. -/
theorem l3W_addr {cur : MState} {t : Nat}
    (ht : t < 64) (hfits : (344 : Nat) ≤ rspEntry.toNat)
    (hrax : cur.core.read .rax = BitVec.ofNat 64 (4 * t))
    (hrsp : cur.core.read .rsp = rspEntry - BitVec.ofNat 64 216) (next : Word) :
    (l3WMem.addr cur.core next).toNat = rspEntry.toNat - 312 + 4 * t := by
  have hlt := rspEntry.isLt
  have hbaseNat : (rspEntry - BitVec.ofNat 64 216).toNat = rspEntry.toNat - 216 :=
    Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := 216) (by omega) (by omega)
  simp only [l3WMem, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Base.value_reg,
    Option.map_some, Option.getD_some, Silmaril.X86.Ext.Index.value, hrax, hrsp,
    show ((0xffffffa0#32 : BitVec 32).signExtend 64) = BitVec.ofNat 64 (2 ^ 64 - 96) from rfl,
    show (0#2 : BitVec 2).toNat = 0 from rfl, BitVec.shiftLeft_zero]
  rw [BitVec.toNat_add, BitVec.toNat_add, hbaseNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 4 * t < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 ^ 64 - 96 < 2 ^ 64 by omega), Nat.mod_add_mod]
  omega

/-! ### The forty-eight decode facts of L3 -/

set_option maxRecDepth 8000 in
/-- `224`, 3 bytes. -/
theorem l3_decode_224 : decode ((raw.drop 224).take 3)
    = some (.mov .d (.reg .r10) .r13, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `227`, 3 bytes. -/
theorem l3_decode_227 : decode ((raw.drop 227).take 3)
    = some (.mov .d (.reg .r9) .rsi, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `230`, 2 bytes. -/
theorem l3_decode_230 : decode ((raw.drop 230).take 2)
    = some (.mov .d (.reg .rbx) .rbp, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `232`, 3 bytes. -/
theorem l3_decode_232 : decode ((raw.drop 232).take 3)
    = some (.mov .d (.reg .r13) .r11, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `235`, 3 bytes. -/
theorem l3_decode_235 : decode ((raw.drop 235).take 3)
    = some (.mov .d (.reg .r11) .rdx, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `238`, 3 bytes. -/
theorem l3_decode_238 : decode ((raw.drop 238).take 3)
    = some (.mov .d (.reg .rdx) .r8, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `241`, 3 bytes. -/
theorem l3_decode_241 : decode ((raw.drop 241).take 3)
    = some (.mov .d (.reg .rsi) .r10, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `244`, 3 bytes. -/
theorem l3_decode_244 : decode ((raw.drop 244).take 3)
    = some (.shift .d .rol (.reg .rsi) (.imm 0x1a#8), 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `247`, 3 bytes. -/
theorem l3_decode_247 : decode ((raw.drop 247).take 3)
    = some (.mov .d (.reg .rbp) .r10, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `250`, 3 bytes. -/
theorem l3_decode_250 : decode ((raw.drop 250).take 3)
    = some (.shift .d .rol (.reg .rbp) (.imm 0x15#8), 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `253`, 2 bytes. -/
theorem l3_decode_253 : decode ((raw.drop 253).take 2)
    = some (.alu .d .xor (.reg .rbp) .rsi, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `255`, 3 bytes. -/
theorem l3_decode_255 : decode ((raw.drop 255).take 3)
    = some (.mov .d (.reg .rsi) .r10, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `258`, 3 bytes. -/
theorem l3_decode_258 : decode ((raw.drop 258).take 3)
    = some (.shift .d .rol (.reg .rsi) (.imm 0x07#8), 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `261`, 2 bytes. -/
theorem l3_decode_261 : decode ((raw.drop 261).take 2)
    = some (.alu .d .xor (.reg .rsi) .rbp, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `263`, 3 bytes. -/
theorem l3_decode_263 : decode ((raw.drop 263).take 3)
    = some (.mov .d (.reg .rbp) .r9, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `266`, 3 bytes. -/
theorem l3_decode_266 : decode ((raw.drop 266).take 3)
    = some (.alu .d .and (.reg .rbp) .r10, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `269`, 3 bytes. -/
theorem l3_decode_269 : decode ((raw.drop 269).take 3)
    = some (.alu .d .add (.reg .rbp) .r14, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `272`, 3 bytes. -/
theorem l3_decode_272 : decode ((raw.drop 272).take 3)
    = some (.mov .d (.reg .r14) .r10, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `275`, 3 bytes. -/
theorem l3_decode_275 : decode ((raw.drop 275).take 3)
    = some (.unary .d .not (.reg .r14), 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `278`, 3 bytes. -/
theorem l3_decode_278 : decode ((raw.drop 278).take 3)
    = some (.alu .d .and (.reg .r14) .rbx, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `281`, 3 bytes. -/
theorem l3_decode_281 : decode ((raw.drop 281).take 3)
    = some (.alu .d .add (.reg .r14) .rbp, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `284`, 3 bytes. -/
theorem l3_decode_284 : decode ((raw.drop 284).take 3)
    = some (.alu .d .add (.reg .r14) .rsi, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `287`, 4 bytes. -/
theorem l3_decode_287 : decode ((raw.drop 287).take 4)
    = some (.aluR .d .add .r14 (.mem l3KMem), 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `291`, 5 bytes. -/
theorem l3_decode_291 : decode ((raw.drop 291).take 5)
    = some (.aluR .d .add .r14 (.mem l3WMem), 5) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `296`, 3 bytes. -/
theorem l3_decode_296 : decode ((raw.drop 296).take 3)
    = some (.mov .d (.reg .r8) .r12, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `299`, 3 bytes. -/
theorem l3_decode_299 : decode ((raw.drop 299).take 3)
    = some (.mov .d (.reg .rsi) .r12, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `302`, 3 bytes. -/
theorem l3_decode_302 : decode ((raw.drop 302).take 3)
    = some (.shift .d .rol (.reg .rsi) (.imm 0x1e#8), 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `305`, 3 bytes. -/
theorem l3_decode_305 : decode ((raw.drop 305).take 3)
    = some (.mov .d (.reg .rbp) .r12, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `308`, 3 bytes. -/
theorem l3_decode_308 : decode ((raw.drop 308).take 3)
    = some (.shift .d .rol (.reg .rbp) (.imm 0x13#8), 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `311`, 3 bytes. -/
theorem l3_decode_311 : decode ((raw.drop 311).take 3)
    = some (.mov .d (.reg .r15) .r12, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `314`, 4 bytes. -/
theorem l3_decode_314 : decode ((raw.drop 314).take 4)
    = some (.shift .d .rol (.reg .r15) (.imm 0x0a#8), 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `318`, 2 bytes. -/
theorem l3_decode_318 : decode ((raw.drop 318).take 2)
    = some (.alu .d .xor (.reg .rbp) .rsi, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `320`, 3 bytes. -/
theorem l3_decode_320 : decode ((raw.drop 320).take 3)
    = some (.alu .d .xor (.reg .r15) .rbp, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `323`, 2 bytes. -/
theorem l3_decode_323 : decode ((raw.drop 323).take 2)
    = some (.mov .d (.reg .rsi) .rdx, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `325`, 3 bytes. -/
theorem l3_decode_325 : decode ((raw.drop 325).take 3)
    = some (.alu .d .xor (.reg .rsi) .r11, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `328`, 3 bytes. -/
theorem l3_decode_328 : decode ((raw.drop 328).take 3)
    = some (.alu .d .and (.reg .rsi) .r12, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `331`, 3 bytes. -/
theorem l3_decode_331 : decode ((raw.drop 331).take 3)
    = some (.mov .d (.reg .r12) .rdx, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `334`, 3 bytes. -/
theorem l3_decode_334 : decode ((raw.drop 334).take 3)
    = some (.alu .d .and (.reg .r12) .r11, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `337`, 3 bytes. -/
theorem l3_decode_337 : decode ((raw.drop 337).take 3)
    = some (.alu .d .xor (.reg .r12) .rsi, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `340`, 3 bytes. -/
theorem l3_decode_340 : decode ((raw.drop 340).take 3)
    = some (.alu .d .add (.reg .r12) .r15, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `343`, 3 bytes. -/
theorem l3_decode_343 : decode ((raw.drop 343).take 3)
    = some (.alu .d .add (.reg .r13) .r14, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `346`, 3 bytes. -/
theorem l3_decode_346 : decode ((raw.drop 346).take 3)
    = some (.alu .d .add (.reg .r12) .r14, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `349`, 4 bytes. -/
theorem l3_decode_349 : decode ((raw.drop 349).take 4)
    = some (.aluI8 .q .add (.reg .rax) 0x04#8, 4) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `353`, 3 bytes. -/
theorem l3_decode_353 : decode ((raw.drop 353).take 3)
    = some (.mov .d (.reg .r14) .rbx, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `356`, 3 bytes. -/
theorem l3_decode_356 : decode ((raw.drop 356).take 3)
    = some (.mov .d (.reg .rbp) .r9, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `359`, 3 bytes. -/
theorem l3_decode_359 : decode ((raw.drop 359).take 3)
    = some (.mov .d (.reg .rsi) .r10, 3) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `362`, 6 bytes. -/
theorem l3_decode_362 : decode ((raw.drop 362).take 6)
    = some (.aluA .q .cmp 0x00000100#32, 6) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `368`, 6 bytes. -/
theorem l3_decode_368 : decode ((raw.drop 368).take 6)
    = some (.jcc .ne 0xffffff6a#32, 6) :=
  decode_raw (by decide +kernel)

/-- What one round does. L3 writes no memory, so the whole effect is where
the machine ends up. -/
structure L3Effect (L : Layout) (rspEntry kBase : Word) (t : Nat) (cur cur' : MState) :
    Prop where
  /-- Back to the loop head, or out to the fallthrough on the last round. -/
  rip : cur'.core.rip = L.textBase + BitVec.ofNat 64 (if t + 1 < 64 then 224 else 374)
  /-- The byte-scaled counter advanced by four. -/
  rax : cur'.core.read .rax = BitVec.ofNat 64 (4 * (t + 1))
  /-- The `K` pointer is untouched. -/
  rcx : cur'.core.read .rcx = kBase
  /-- The frame pointer is untouched. -/
  rsp : cur'.core.read .rsp = cur.core.read .rsp
  /-- The output pointer is untouched. -/
  rdi : cur'.core.read .rdi = cur.core.read .rdi
  /-- Memory is untouched. -/
  mem : cur'.memory = cur.memory

set_option maxRecDepth 8000 in
/-- L3's `jne` backedge: the fallthrough at 374 plus the sign-extended rel32
`0xffffff6a` (−150) is the loop head at 224. -/
theorem l3_backedge (textBase : Word) :
    textBase + BitVec.ofNat 64 (368 + 6) + (0xffffff6a#32 : BitVec 32).signExtend 64
      = textBase + BitVec.ofNat 64 224 := by
  rw [show ((0xffffff6a#32 : BitVec 32).signExtend 64) = BitVec.ofNat 64 (2 ^ 64 - 150) from rfl,
    add_assoc, Silmaril.X86.Ext.ofNat_add_ofNat]
  congr 1

set_option maxRecDepth 8000 in
/-- L3's counter, as a word, is `256` exactly when `t + 1` is `64`. -/
theorem l3_counter_ne {t : Nat} (ht : t < 64) :
    (BitVec.ofNat 64 (4 * (t + 1)) ≠ BitVec.ofNat 64 256) ↔ (t + 1 ≠ 64) := by
  rw [ofNat_ne_ofNat (by omega) (by omega)]
  omega

/-- **The round state is in two register sets at once.** The loop body opens
`r10 ← e`, `r9 ← f`, `rbx ← g` and closes `rsi ← r10`, `rbp ← r9`, `r14 ← rbx`,
so after any iteration the two sets agree. Block `374 … 441` reads the first
set; `RoundState` tracks the second. This is the bridge.

It holds after *any* iteration but **not** at L3's entry, where block
`150 … 224` has set only `rsi`, `rbp` and `r14` — which is why the loop carries
it guarded by `0 < t` rather than unconditionally. -/
def RoundAlias (cur : MState) : Prop :=
  read32 cur.core .r10 = read32 cur.core .rsi ∧
  read32 cur.core .r9 = read32 cur.core .rbp ∧
  read32 cur.core .rbx = read32 cur.core .r14

/-- **One round, in the specification's vocabulary.** The eight round
registers after the iteration, against `SHA256.Kernel.round` applied to the
eight before it.

`K[t]` and `w[t]` enter as the words actually held in their slots, so this says
nothing about *which* words they are — that is the caller's business, and it is
what lets L3 be proved against an arbitrary schedule. -/
def RoundOut (cur cur' : MState) (kv wv : Word) : Prop :=
  (read32 cur'.core .r12, read32 cur'.core .r8, read32 cur'.core .rdx,
   read32 cur'.core .r11, read32 cur'.core .r13, read32 cur'.core .rsi,
   read32 cur'.core .rbp, read32 cur'.core .r14)
    = SHA256.Kernel.round (read32 cur.core .r12) (read32 cur.core .r8)
        (read32 cur.core .rdx) (read32 cur.core .r11) (read32 cur.core .r13)
        (read32 cur.core .rsi) (read32 cur.core .rbp) (read32 cur.core .r14)
        ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32)
        ((BitVec.ofNat 64 (wv.toNat % 2 ^ (8 * 4))).setWidth 32) ∧
    RoundAlias cur'

set_option maxRecDepth 8000 in
/-- **The L3 trace**, over an abstract image: one of the sixty-four rounds.

Forty-eight steps, forty-five of them a single scratch-register write handled
by `L3At.regStep`. The only memory touched is two **reads** — `K[t]` and
`w[t]` — and nothing is written, which is why the invariant is only about
where the machine is.

Note it takes no `SysVEntry`: L3 writes nothing, so it needs no frame
permission and no disjointness — only the two slot facts and the bounds. -/
theorem l3_trace_img
    {cur : MState} {t : Nat} {kBase : Word} {img : List Byte} (ht : t < 64)
    (himg : img.length = size)
    (hfits : (344 : Nat) ≤ rspEntry.toNat)
    (hknw : kBase.toNat + 256 ≤ 2 ^ 64)
    (e224 : decode ((img.drop 224).take 3) = some (.mov .d (.reg .r10) .r13, 3))
    (e227 : decode ((img.drop 227).take 3) = some (.mov .d (.reg .r9) .rsi, 3))
    (e230 : decode ((img.drop 230).take 2) = some (.mov .d (.reg .rbx) .rbp, 2))
    (e232 : decode ((img.drop 232).take 3) = some (.mov .d (.reg .r13) .r11, 3))
    (e235 : decode ((img.drop 235).take 3) = some (.mov .d (.reg .r11) .rdx, 3))
    (e238 : decode ((img.drop 238).take 3) = some (.mov .d (.reg .rdx) .r8, 3))
    (e241 : decode ((img.drop 241).take 3) = some (.mov .d (.reg .rsi) .r10, 3))
    (e244 : decode ((img.drop 244).take 3) = some (.shift .d .rol (.reg .rsi) (.imm 0x1a#8), 3))
    (e247 : decode ((img.drop 247).take 3) = some (.mov .d (.reg .rbp) .r10, 3))
    (e250 : decode ((img.drop 250).take 3) = some (.shift .d .rol (.reg .rbp) (.imm 0x15#8), 3))
    (e253 : decode ((img.drop 253).take 2) = some (.alu .d .xor (.reg .rbp) .rsi, 2))
    (e255 : decode ((img.drop 255).take 3) = some (.mov .d (.reg .rsi) .r10, 3))
    (e258 : decode ((img.drop 258).take 3) = some (.shift .d .rol (.reg .rsi) (.imm 0x07#8), 3))
    (e261 : decode ((img.drop 261).take 2) = some (.alu .d .xor (.reg .rsi) .rbp, 2))
    (e263 : decode ((img.drop 263).take 3) = some (.mov .d (.reg .rbp) .r9, 3))
    (e266 : decode ((img.drop 266).take 3) = some (.alu .d .and (.reg .rbp) .r10, 3))
    (e269 : decode ((img.drop 269).take 3) = some (.alu .d .add (.reg .rbp) .r14, 3))
    (e272 : decode ((img.drop 272).take 3) = some (.mov .d (.reg .r14) .r10, 3))
    (e275 : decode ((img.drop 275).take 3) = some (.unary .d .not (.reg .r14), 3))
    (e278 : decode ((img.drop 278).take 3) = some (.alu .d .and (.reg .r14) .rbx, 3))
    (e281 : decode ((img.drop 281).take 3) = some (.alu .d .add (.reg .r14) .rbp, 3))
    (e284 : decode ((img.drop 284).take 3) = some (.alu .d .add (.reg .r14) .rsi, 3))
    (e287 : decode ((img.drop 287).take 4) = some (.aluR .d .add .r14 (.mem l3KMem), 4))
    (e291 : decode ((img.drop 291).take 5) = some (.aluR .d .add .r14 (.mem l3WMem), 5))
    (e296 : decode ((img.drop 296).take 3) = some (.mov .d (.reg .r8) .r12, 3))
    (e299 : decode ((img.drop 299).take 3) = some (.mov .d (.reg .rsi) .r12, 3))
    (e302 : decode ((img.drop 302).take 3) = some (.shift .d .rol (.reg .rsi) (.imm 0x1e#8), 3))
    (e305 : decode ((img.drop 305).take 3) = some (.mov .d (.reg .rbp) .r12, 3))
    (e308 : decode ((img.drop 308).take 3) = some (.shift .d .rol (.reg .rbp) (.imm 0x13#8), 3))
    (e311 : decode ((img.drop 311).take 3) = some (.mov .d (.reg .r15) .r12, 3))
    (e314 : decode ((img.drop 314).take 4) = some (.shift .d .rol (.reg .r15) (.imm 0x0a#8), 4))
    (e318 : decode ((img.drop 318).take 2) = some (.alu .d .xor (.reg .rbp) .rsi, 2))
    (e320 : decode ((img.drop 320).take 3) = some (.alu .d .xor (.reg .r15) .rbp, 3))
    (e323 : decode ((img.drop 323).take 2) = some (.mov .d (.reg .rsi) .rdx, 2))
    (e325 : decode ((img.drop 325).take 3) = some (.alu .d .xor (.reg .rsi) .r11, 3))
    (e328 : decode ((img.drop 328).take 3) = some (.alu .d .and (.reg .rsi) .r12, 3))
    (e331 : decode ((img.drop 331).take 3) = some (.mov .d (.reg .r12) .rdx, 3))
    (e334 : decode ((img.drop 334).take 3) = some (.alu .d .and (.reg .r12) .r11, 3))
    (e337 : decode ((img.drop 337).take 3) = some (.alu .d .xor (.reg .r12) .rsi, 3))
    (e340 : decode ((img.drop 340).take 3) = some (.alu .d .add (.reg .r12) .r15, 3))
    (e343 : decode ((img.drop 343).take 3) = some (.alu .d .add (.reg .r13) .r14, 3))
    (e346 : decode ((img.drop 346).take 3) = some (.alu .d .add (.reg .r12) .r14, 3))
    (e349 : decode ((img.drop 349).take 4) = some (.aluI8 .q .add (.reg .rax) 0x04#8, 4))
    (e353 : decode ((img.drop 353).take 3) = some (.mov .d (.reg .r14) .rbx, 3))
    (e356 : decode ((img.drop 356).take 3) = some (.mov .d (.reg .rbp) .r9, 3))
    (e359 : decode ((img.drop 359).take 3) = some (.mov .d (.reg .rsi) .r10, 3))
    (e362 : decode ((img.drop 362).take 6) = some (.aluA .q .cmp 0x00000100#32, 6))
    (e368 : decode ((img.drop 368).take 6) = some (.jcc .ne 0xffffff6a#32, 6))
    (hat : L3At L rspEntry kBase state 224 t cur cur)
    (hloaded : Loaded cur.memory L.textBase img)
    {kv wv : Word}
    (hkv : Silmaril.X86.Ext.HoldsLE cur.memory (kBase.toNat + 4 * t) 4 kv)
    (hwv : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 312 + 4 * t) 4 wv) :
    ∃ cur', Reaches L.exit cur cur' ∧ L3Effect L rspEntry kBase t cur cur' ∧
      RoundOut cur cur' kv wv := by
  have hld : ∀ {c : MState}, c.memory = cur.memory → Loaded c.memory L.textBase img :=
    fun hm => hm ▸ hloaded
  have a0 : L3At L rspEntry kBase state 224 t cur cur :=
    { rip := hat.rip, rax := hat.rax, rcx := hat.rcx, rsp := hat.rsp, rdi := hat.rdi, mem := rfl }
  obtain ⟨c1, s1, h1rip, h1w, _, h1mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 224) (len := 3)
      (hld a0.mem) a0.rip (by rw [himg]; decide) e224
  have a1 := a0.regStep h1rip h1w h1mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c2, s2, h2rip, h2w, _, h2mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 227) (len := 3)
      (hld a1.mem) a1.rip (by rw [himg]; decide) e227
  have a2 := a1.regStep h2rip h2w h2mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c3, s3, h3rip, h3w, _, h3mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 230) (len := 2)
      (hld a2.mem) a2.rip (by rw [himg]; decide) e230
  have a3 := a2.regStep h3rip h3w h3mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c4, s4, h4rip, h4w, _, h4mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 232) (len := 3)
      (hld a3.mem) a3.rip (by rw [himg]; decide) e232
  have a4 := a3.regStep h4rip h4w h4mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c5, s5, h5rip, h5w, _, h5mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 235) (len := 3)
      (hld a4.mem) a4.rip (by rw [himg]; decide) e235
  have a5 := a4.regStep h5rip h5w h5mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c6, s6, h6rip, h6w, _, h6mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 238) (len := 3)
      (hld a5.mem) a5.rip (by rw [himg]; decide) e238
  have a6 := a5.regStep h6rip h6w h6mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c7, s7, h7rip, h7w, _, h7mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 241) (len := 3)
      (hld a6.mem) a6.rip (by rw [himg]; decide) e241
  have a7 := a6.regStep h7rip h7w h7mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c8, s8, h8rip, h8w, _, h8mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 244) (len := 3)
      (hld a7.mem) a7.rip (by rw [himg]; decide) e244 rfl
  have a8 := a7.regStep h8rip h8w h8mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c9, s9, h9rip, h9w, _, h9mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 247) (len := 3)
      (hld a8.mem) a8.rip (by rw [himg]; decide) e247
  have a9 := a8.regStep h9rip h9w h9mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c10, s10, h10rip, h10w, _, h10mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 250) (len := 3)
      (hld a9.mem) a9.rip (by rw [himg]; decide) e250 rfl
  have a10 := a9.regStep h10rip h10w h10mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c11, s11, h11rip, h11w, _, h11mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 253) (len := 2)
      (hld a10.mem) a10.rip (by rw [himg]; decide) e253 (by decide) rfl
  have a11 := a10.regStep h11rip h11w h11mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c12, s12, h12rip, h12w, _, h12mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 255) (len := 3)
      (hld a11.mem) a11.rip (by rw [himg]; decide) e255
  have a12 := a11.regStep h12rip h12w h12mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c13, s13, h13rip, h13w, _, h13mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 258) (len := 3)
      (hld a12.mem) a12.rip (by rw [himg]; decide) e258 rfl
  have a13 := a12.regStep h13rip h13w h13mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c14, s14, h14rip, h14w, _, h14mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 261) (len := 2)
      (hld a13.mem) a13.rip (by rw [himg]; decide) e261 (by decide) rfl
  have a14 := a13.regStep h14rip h14w h14mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c15, s15, h15rip, h15w, _, h15mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 263) (len := 3)
      (hld a14.mem) a14.rip (by rw [himg]; decide) e263
  have a15 := a14.regStep h15rip h15w h15mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c16, s16, h16rip, h16w, _, h16mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 266) (len := 3)
      (hld a15.mem) a15.rip (by rw [himg]; decide) e266 (by decide) rfl
  have a16 := a15.regStep h16rip h16w h16mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c17, s17, h17rip, h17w, _, h17mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 269) (len := 3)
      (hld a16.mem) a16.rip (by rw [himg]; decide) e269 (by decide) rfl
  have a17 := a16.regStep h17rip h17w h17mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c18, s18, h18rip, h18w, _, h18mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 272) (len := 3)
      (hld a17.mem) a17.rip (by rw [himg]; decide) e272
  have a18 := a17.regStep h18rip h18w h18mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c19, s19, h19rip, h19w, _, h19mem⟩ :=
    stepOpt_not_reg (exit := L.exit) (offset := 275) (len := 3)
      (hld a18.mem) a18.rip (by rw [himg]; decide) e275
  have a19 := a18.regStep h19rip h19w h19mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c20, s20, h20rip, h20w, _, h20mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 278) (len := 3)
      (hld a19.mem) a19.rip (by rw [himg]; decide) e278 (by decide) rfl
  have a20 := a19.regStep h20rip h20w h20mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c21, s21, h21rip, h21w, _, h21mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 281) (len := 3)
      (hld a20.mem) a20.rip (by rw [himg]; decide) e281 (by decide) rfl
  have a21 := a20.regStep h21rip h21w h21mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c22, s22, h22rip, h22w, _, h22mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 284) (len := 3)
      (hld a21.mem) a21.rip (by rw [himg]; decide) e284 (by decide) rfl
  have a22 := a21.regStep h22rip h22w h22mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c23, s23, h23rip, h23w, _, h23mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 287) (len := 4) (width := 4)
      (hld a22.mem) a22.rip (by rw [himg]; decide) e287
      (by decide) (l3K_addr hknw ht a22.rax a22.rcx _) rfl
      (by rw [a22.mem]; exact hkv)
  have a23 := a22.regStep h23rip h23w h23mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c24, s24, h24rip, h24w, _, h24mem⟩ :=
    stepOpt_aluR_mem (exit := L.exit) (offset := 291) (len := 5) (width := 4)
      (hld a23.mem) a23.rip (by rw [himg]; decide) e291
      (by decide) (l3W_addr ht hfits a23.rax a23.rsp _) rfl
      (by rw [a23.mem]; exact hwv)
  have a24 := a23.regStep h24rip h24w h24mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c25, s25, h25rip, h25w, _, h25mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 296) (len := 3)
      (hld a24.mem) a24.rip (by rw [himg]; decide) e296
  have a25 := a24.regStep h25rip h25w h25mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c26, s26, h26rip, h26w, _, h26mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 299) (len := 3)
      (hld a25.mem) a25.rip (by rw [himg]; decide) e299
  have a26 := a25.regStep h26rip h26w h26mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c27, s27, h27rip, h27w, _, h27mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 302) (len := 3)
      (hld a26.mem) a26.rip (by rw [himg]; decide) e302 rfl
  have a27 := a26.regStep h27rip h27w h27mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c28, s28, h28rip, h28w, _, h28mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 305) (len := 3)
      (hld a27.mem) a27.rip (by rw [himg]; decide) e305
  have a28 := a27.regStep h28rip h28w h28mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c29, s29, h29rip, h29w, _, h29mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 308) (len := 3)
      (hld a28.mem) a28.rip (by rw [himg]; decide) e308 rfl
  have a29 := a28.regStep h29rip h29w h29mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c30, s30, h30rip, h30w, _, h30mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 311) (len := 3)
      (hld a29.mem) a29.rip (by rw [himg]; decide) e311
  have a30 := a29.regStep h30rip h30w h30mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c31, s31, h31rip, h31w, _, h31mem⟩ :=
    Silmaril.X86.Ext.stepOpt_shift_reg (exit := L.exit) (offset := 314) (len := 4)
      (hld a30.mem) a30.rip (by rw [himg]; decide) e314 rfl
  have a31 := a30.regStep h31rip h31w h31mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c32, s32, h32rip, h32w, _, h32mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 318) (len := 2)
      (hld a31.mem) a31.rip (by rw [himg]; decide) e318 (by decide) rfl
  have a32 := a31.regStep h32rip h32w h32mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c33, s33, h33rip, h33w, _, h33mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 320) (len := 3)
      (hld a32.mem) a32.rip (by rw [himg]; decide) e320 (by decide) rfl
  have a33 := a32.regStep h33rip h33w h33mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c34, s34, h34rip, h34w, _, h34mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 323) (len := 2)
      (hld a33.mem) a33.rip (by rw [himg]; decide) e323
  have a34 := a33.regStep h34rip h34w h34mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c35, s35, h35rip, h35w, _, h35mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 325) (len := 3)
      (hld a34.mem) a34.rip (by rw [himg]; decide) e325 (by decide) rfl
  have a35 := a34.regStep h35rip h35w h35mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c36, s36, h36rip, h36w, _, h36mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 328) (len := 3)
      (hld a35.mem) a35.rip (by rw [himg]; decide) e328 (by decide) rfl
  have a36 := a35.regStep h36rip h36w h36mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c37, s37, h37rip, h37w, _, h37mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 331) (len := 3)
      (hld a36.mem) a36.rip (by rw [himg]; decide) e331
  have a37 := a36.regStep h37rip h37w h37mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c38, s38, h38rip, h38w, _, h38mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 334) (len := 3)
      (hld a37.mem) a37.rip (by rw [himg]; decide) e334 (by decide) rfl
  have a38 := a37.regStep h38rip h38w h38mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c39, s39, h39rip, h39w, _, h39mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 337) (len := 3)
      (hld a38.mem) a38.rip (by rw [himg]; decide) e337 (by decide) rfl
  have a39 := a38.regStep h39rip h39w h39mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c40, s40, h40rip, h40w, _, h40mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 340) (len := 3)
      (hld a39.mem) a39.rip (by rw [himg]; decide) e340 (by decide) rfl
  have a40 := a39.regStep h40rip h40w h40mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c41, s41, h41rip, h41w, _, h41mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 343) (len := 3)
      (hld a40.mem) a40.rip (by rw [himg]; decide) e343 (by decide) rfl
  have a41 := a40.regStep h41rip h41w h41mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c42, s42, h42rip, h42w, _, h42mem⟩ :=
    Silmaril.X86.Ext.stepOpt_alu_reg (exit := L.exit) (offset := 346) (len := 3)
      (hld a41.mem) a41.rip (by rw [himg]; decide) e346 (by decide) rfl
  have a42 := a41.regStep h42rip h42w h42mem (by decide) (by decide) (by decide) (by decide)
  -- 349: add $0x4,%rax
  obtain ⟨c43, s43, h43rip, h43w, _, h43mem⟩ :=
    Silmaril.X86.Ext.stepOpt_aluI8_reg (exit := L.exit) (offset := 349) (len := 4)
      (hld a42.mem) a42.rip (by rw [himg]; decide) e349 (by decide) rfl
  have h43rax : c43.core.read .rax = BitVec.ofNat 64 (4 * (t + 1)) := by
    rw [h43w.target]
    have hr : Silmaril.X86.Ext.Sz.q.read c42.core Reg.rax = BitVec.ofNat 64 (4 * t) := by
      rw [Silmaril.X86.Ext.Sz.read_q]; exact a42.rax
    rw [hr]
    show (BitVec.ofNat 64 (4 * t) + BitVec.ofNat 64 4).setWidth 64 = _
    rw [Silmaril.X86.Ext.ofNat_add_ofNat, BitVec.setWidth_eq]
    congr 1
  have a43 : L3At L rspEntry kBase state 353 (t + 1) cur c43 :=
    { rip := h43rip, rax := h43rax
      rcx := by rw [h43w.other _ (by decide)]; exact a42.rcx
      rsp := by rw [h43w.other _ (by decide)]; exact a42.rsp
      rdi := by rw [h43w.other _ (by decide)]; exact a42.rdi
      mem := by rw [h43mem]; exact a42.mem }
  -- 353, 356, 359: three register moves
  obtain ⟨c44, s44, h44rip, h44w, _, h44mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 353) (len := 3)
      (hld a43.mem) a43.rip (by rw [himg]; decide) e353
  have a44 := a43.regStep h44rip h44w h44mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c45, s45, h45rip, h45w, _, h45mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 356) (len := 3)
      (hld a44.mem) a44.rip (by rw [himg]; decide) e356
  have a45 := a44.regStep h45rip h45w h45mem (by decide) (by decide) (by decide) (by decide)
  obtain ⟨c46, s46, h46rip, h46w, _, h46mem⟩ :=
    stepOpt_mov_reg (exit := L.exit) (offset := 359) (len := 3)
      (hld a45.mem) a45.rip (by rw [himg]; decide) e359
  have a46 := a45.regStep h46rip h46w h46mem (by decide) (by decide) (by decide) (by decide)
  -- the round state, tracked back to the entry registers
  obtain ⟨A, hA⟩ : ∃ A, read32 cur.core Reg.r12 = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, read32 cur.core Reg.r8 = B := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, read32 cur.core Reg.rdx = C := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, read32 cur.core Reg.r11 = D := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, read32 cur.core Reg.r13 = E := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, read32 cur.core Reg.rsi = F := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, read32 cur.core Reg.rbp = G := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, read32 cur.core Reg.r14 = H := ⟨_, rfl⟩
  have v1 : read32 c1.core Reg.r10 =
      E := by
    rw [read_d_of_writes h1w]
    simp only [← read32_eq]
    rw [hE]
    try rfl
  have v2 : read32 c2.core Reg.r9 =
      F := by
    rw [read_d_of_writes h2w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.rsi) h1w (by decide), hF]
    try rfl
  have v3 : read32 c3.core Reg.rbx =
      G := by
    rw [read_d_of_writes h3w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.rbp) h2w (by decide), read_d_of_other (r := Reg.rbp) h1w (by decide), hG]
    try rfl
  have v4 : read32 c4.core Reg.r13 =
      D := by
    rw [read_d_of_writes h4w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r11) h3w (by decide), read_d_of_other (r := Reg.r11) h2w (by decide), read_d_of_other (r := Reg.r11) h1w (by decide), hD]
    try rfl
  have v5 : read32 c5.core Reg.r11 =
      C := by
    rw [read_d_of_writes h5w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.rdx) h4w (by decide), read_d_of_other (r := Reg.rdx) h3w (by decide), read_d_of_other (r := Reg.rdx) h2w (by decide), read_d_of_other (r := Reg.rdx) h1w (by decide), hC]
    try rfl
  have v6 : read32 c6.core Reg.rdx =
      B := by
    rw [read_d_of_writes h6w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r8) h5w (by decide), read_d_of_other (r := Reg.r8) h4w (by decide), read_d_of_other (r := Reg.r8) h3w (by decide), read_d_of_other (r := Reg.r8) h2w (by decide), read_d_of_other (r := Reg.r8) h1w (by decide), hB]
    try rfl
  have v7 : read32 c7.core Reg.rsi =
      E := by
    rw [read_d_of_writes h7w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r10) h6w (by decide), read_d_of_other (r := Reg.r10) h5w (by decide), read_d_of_other (r := Reg.r10) h4w (by decide), read_d_of_other (r := Reg.r10) h3w (by decide), read_d_of_other (r := Reg.r10) h2w (by decide), v1]
    try rfl
  have v8 : read32 c8.core Reg.rsi =
      (E).rotateLeft 26 := by
    rw [read_d_of_writes h8w]
    simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x1a#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 26 from rfl]
    rw [v7]
    try rfl
  have v9 : read32 c9.core Reg.rbp =
      E := by
    rw [read_d_of_writes h9w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r10) h8w (by decide), read_d_of_other (r := Reg.r10) h7w (by decide), read_d_of_other (r := Reg.r10) h6w (by decide), read_d_of_other (r := Reg.r10) h5w (by decide), read_d_of_other (r := Reg.r10) h4w (by decide), read_d_of_other (r := Reg.r10) h3w (by decide), read_d_of_other (r := Reg.r10) h2w (by decide), v1]
    try rfl
  have v10 : read32 c10.core Reg.rbp =
      (E).rotateLeft 21 := by
    rw [read_d_of_writes h10w]
    simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x15#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 21 from rfl]
    rw [v9]
    try rfl
  have v11 : read32 c11.core Reg.rbp =
      ((E).rotateLeft 21) ^^^ ((E).rotateLeft 26) := by
    rw [read_d_of_writes h11w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v10, read_d_of_other (r := Reg.rsi) h10w (by decide), read_d_of_other (r := Reg.rsi) h9w (by decide), v8]
    try rfl
  have v12 : read32 c12.core Reg.rsi =
      E := by
    rw [read_d_of_writes h12w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r10) h11w (by decide), read_d_of_other (r := Reg.r10) h10w (by decide), read_d_of_other (r := Reg.r10) h9w (by decide), read_d_of_other (r := Reg.r10) h8w (by decide), read_d_of_other (r := Reg.r10) h7w (by decide), read_d_of_other (r := Reg.r10) h6w (by decide), read_d_of_other (r := Reg.r10) h5w (by decide), read_d_of_other (r := Reg.r10) h4w (by decide), read_d_of_other (r := Reg.r10) h3w (by decide), read_d_of_other (r := Reg.r10) h2w (by decide), v1]
    try rfl
  have v13 : read32 c13.core Reg.rsi =
      (E).rotateLeft 7 := by
    rw [read_d_of_writes h13w]
    simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x07#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 7 from rfl]
    rw [v12]
    try rfl
  have v14 : read32 c14.core Reg.rsi =
      ((E).rotateLeft 7) ^^^ (((E).rotateLeft 21) ^^^ ((E).rotateLeft 26)) := by
    rw [read_d_of_writes h14w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v13, read_d_of_other (r := Reg.rbp) h13w (by decide), read_d_of_other (r := Reg.rbp) h12w (by decide), v11]
    try rfl
  have v15 : read32 c15.core Reg.rbp =
      F := by
    rw [read_d_of_writes h15w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r9) h14w (by decide), read_d_of_other (r := Reg.r9) h13w (by decide), read_d_of_other (r := Reg.r9) h12w (by decide), read_d_of_other (r := Reg.r9) h11w (by decide), read_d_of_other (r := Reg.r9) h10w (by decide), read_d_of_other (r := Reg.r9) h9w (by decide), read_d_of_other (r := Reg.r9) h8w (by decide), read_d_of_other (r := Reg.r9) h7w (by decide), read_d_of_other (r := Reg.r9) h6w (by decide), read_d_of_other (r := Reg.r9) h5w (by decide), read_d_of_other (r := Reg.r9) h4w (by decide), read_d_of_other (r := Reg.r9) h3w (by decide), v2]
    try rfl
  have v16 : read32 c16.core Reg.rbp =
      (F) &&& (E) := by
    rw [read_d_of_writes h16w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v15, read_d_of_other (r := Reg.r10) h15w (by decide), read_d_of_other (r := Reg.r10) h14w (by decide), read_d_of_other (r := Reg.r10) h13w (by decide), read_d_of_other (r := Reg.r10) h12w (by decide), read_d_of_other (r := Reg.r10) h11w (by decide), read_d_of_other (r := Reg.r10) h10w (by decide), read_d_of_other (r := Reg.r10) h9w (by decide), read_d_of_other (r := Reg.r10) h8w (by decide), read_d_of_other (r := Reg.r10) h7w (by decide), read_d_of_other (r := Reg.r10) h6w (by decide), read_d_of_other (r := Reg.r10) h5w (by decide), read_d_of_other (r := Reg.r10) h4w (by decide), read_d_of_other (r := Reg.r10) h3w (by decide), read_d_of_other (r := Reg.r10) h2w (by decide), v1]
    try rfl
  have v17 : read32 c17.core Reg.rbp =
      ((F) &&& (E)) + (H) := by
    rw [read_d_of_writes h17w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v16, read_d_of_other (r := Reg.r14) h16w (by decide), read_d_of_other (r := Reg.r14) h15w (by decide), read_d_of_other (r := Reg.r14) h14w (by decide), read_d_of_other (r := Reg.r14) h13w (by decide), read_d_of_other (r := Reg.r14) h12w (by decide), read_d_of_other (r := Reg.r14) h11w (by decide), read_d_of_other (r := Reg.r14) h10w (by decide), read_d_of_other (r := Reg.r14) h9w (by decide), read_d_of_other (r := Reg.r14) h8w (by decide), read_d_of_other (r := Reg.r14) h7w (by decide), read_d_of_other (r := Reg.r14) h6w (by decide), read_d_of_other (r := Reg.r14) h5w (by decide), read_d_of_other (r := Reg.r14) h4w (by decide), read_d_of_other (r := Reg.r14) h3w (by decide), read_d_of_other (r := Reg.r14) h2w (by decide), read_d_of_other (r := Reg.r14) h1w (by decide), hH]
    try rfl
  have v18 : read32 c18.core Reg.r14 =
      E := by
    rw [read_d_of_writes h18w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r10) h17w (by decide), read_d_of_other (r := Reg.r10) h16w (by decide), read_d_of_other (r := Reg.r10) h15w (by decide), read_d_of_other (r := Reg.r10) h14w (by decide), read_d_of_other (r := Reg.r10) h13w (by decide), read_d_of_other (r := Reg.r10) h12w (by decide), read_d_of_other (r := Reg.r10) h11w (by decide), read_d_of_other (r := Reg.r10) h10w (by decide), read_d_of_other (r := Reg.r10) h9w (by decide), read_d_of_other (r := Reg.r10) h8w (by decide), read_d_of_other (r := Reg.r10) h7w (by decide), read_d_of_other (r := Reg.r10) h6w (by decide), read_d_of_other (r := Reg.r10) h5w (by decide), read_d_of_other (r := Reg.r10) h4w (by decide), read_d_of_other (r := Reg.r10) h3w (by decide), read_d_of_other (r := Reg.r10) h2w (by decide), v1]
    try rfl
  have v19 : read32 c19.core Reg.r14 =
      ~~~(E) := by
    rw [read_d_of_writes h19w]
    simp only [← read32_eq]
    rw [v18]
    try rfl
  have v20 : read32 c20.core Reg.r14 =
      (~~~(E)) &&& (G) := by
    rw [read_d_of_writes h20w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v19, read_d_of_other (r := Reg.rbx) h19w (by decide), read_d_of_other (r := Reg.rbx) h18w (by decide), read_d_of_other (r := Reg.rbx) h17w (by decide), read_d_of_other (r := Reg.rbx) h16w (by decide), read_d_of_other (r := Reg.rbx) h15w (by decide), read_d_of_other (r := Reg.rbx) h14w (by decide), read_d_of_other (r := Reg.rbx) h13w (by decide), read_d_of_other (r := Reg.rbx) h12w (by decide), read_d_of_other (r := Reg.rbx) h11w (by decide), read_d_of_other (r := Reg.rbx) h10w (by decide), read_d_of_other (r := Reg.rbx) h9w (by decide), read_d_of_other (r := Reg.rbx) h8w (by decide), read_d_of_other (r := Reg.rbx) h7w (by decide), read_d_of_other (r := Reg.rbx) h6w (by decide), read_d_of_other (r := Reg.rbx) h5w (by decide), read_d_of_other (r := Reg.rbx) h4w (by decide), v3]
    try rfl
  have v21 : read32 c21.core Reg.r14 =
      ((~~~(E)) &&& (G)) + (((F) &&& (E)) + (H)) := by
    rw [read_d_of_writes h21w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v20, read_d_of_other (r := Reg.rbp) h20w (by decide), read_d_of_other (r := Reg.rbp) h19w (by decide), read_d_of_other (r := Reg.rbp) h18w (by decide), v17]
    try rfl
  have v22 : read32 c22.core Reg.r14 =
      (((~~~(E)) &&& (G)) + (((F) &&& (E)) + (H))) + (((E).rotateLeft 7) ^^^ (((E).rotateLeft 21) ^^^ ((E).rotateLeft 26))) := by
    rw [read_d_of_writes h22w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v21, read_d_of_other (r := Reg.rsi) h21w (by decide), read_d_of_other (r := Reg.rsi) h20w (by decide), read_d_of_other (r := Reg.rsi) h19w (by decide), read_d_of_other (r := Reg.rsi) h18w (by decide), read_d_of_other (r := Reg.rsi) h17w (by decide), read_d_of_other (r := Reg.rsi) h16w (by decide), read_d_of_other (r := Reg.rsi) h15w (by decide), v14]
    try rfl
  have v23 : read32 c23.core Reg.r14 =
      ((((~~~(E)) &&& (G)) + (((F) &&& (E)) + (H))) + (((E).rotateLeft 7) ^^^ (((E).rotateLeft 21) ^^^ ((E).rotateLeft 26)))) + ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32) := by
    rw [read_d_of_writes h23w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v22]
    try rfl
  have v24 : read32 c24.core Reg.r14 =
      (((((~~~(E)) &&& (G)) + (((F) &&& (E)) + (H))) + (((E).rotateLeft 7) ^^^ (((E).rotateLeft 21) ^^^ ((E).rotateLeft 26)))) + ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32)) + ((BitVec.ofNat 64 (wv.toNat % 2 ^ (8 * 4))).setWidth 32) := by
    rw [read_d_of_writes h24w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v23]
    try rfl
  have v25 : read32 c25.core Reg.r8 =
      A := by
    rw [read_d_of_writes h25w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r12) h24w (by decide), read_d_of_other (r := Reg.r12) h23w (by decide), read_d_of_other (r := Reg.r12) h22w (by decide), read_d_of_other (r := Reg.r12) h21w (by decide), read_d_of_other (r := Reg.r12) h20w (by decide), read_d_of_other (r := Reg.r12) h19w (by decide), read_d_of_other (r := Reg.r12) h18w (by decide), read_d_of_other (r := Reg.r12) h17w (by decide), read_d_of_other (r := Reg.r12) h16w (by decide), read_d_of_other (r := Reg.r12) h15w (by decide), read_d_of_other (r := Reg.r12) h14w (by decide), read_d_of_other (r := Reg.r12) h13w (by decide), read_d_of_other (r := Reg.r12) h12w (by decide), read_d_of_other (r := Reg.r12) h11w (by decide), read_d_of_other (r := Reg.r12) h10w (by decide), read_d_of_other (r := Reg.r12) h9w (by decide), read_d_of_other (r := Reg.r12) h8w (by decide), read_d_of_other (r := Reg.r12) h7w (by decide), read_d_of_other (r := Reg.r12) h6w (by decide), read_d_of_other (r := Reg.r12) h5w (by decide), read_d_of_other (r := Reg.r12) h4w (by decide), read_d_of_other (r := Reg.r12) h3w (by decide), read_d_of_other (r := Reg.r12) h2w (by decide), read_d_of_other (r := Reg.r12) h1w (by decide), hA]
    try rfl
  have v26 : read32 c26.core Reg.rsi =
      A := by
    rw [read_d_of_writes h26w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r12) h25w (by decide), read_d_of_other (r := Reg.r12) h24w (by decide), read_d_of_other (r := Reg.r12) h23w (by decide), read_d_of_other (r := Reg.r12) h22w (by decide), read_d_of_other (r := Reg.r12) h21w (by decide), read_d_of_other (r := Reg.r12) h20w (by decide), read_d_of_other (r := Reg.r12) h19w (by decide), read_d_of_other (r := Reg.r12) h18w (by decide), read_d_of_other (r := Reg.r12) h17w (by decide), read_d_of_other (r := Reg.r12) h16w (by decide), read_d_of_other (r := Reg.r12) h15w (by decide), read_d_of_other (r := Reg.r12) h14w (by decide), read_d_of_other (r := Reg.r12) h13w (by decide), read_d_of_other (r := Reg.r12) h12w (by decide), read_d_of_other (r := Reg.r12) h11w (by decide), read_d_of_other (r := Reg.r12) h10w (by decide), read_d_of_other (r := Reg.r12) h9w (by decide), read_d_of_other (r := Reg.r12) h8w (by decide), read_d_of_other (r := Reg.r12) h7w (by decide), read_d_of_other (r := Reg.r12) h6w (by decide), read_d_of_other (r := Reg.r12) h5w (by decide), read_d_of_other (r := Reg.r12) h4w (by decide), read_d_of_other (r := Reg.r12) h3w (by decide), read_d_of_other (r := Reg.r12) h2w (by decide), read_d_of_other (r := Reg.r12) h1w (by decide), hA]
    try rfl
  have v27 : read32 c27.core Reg.rsi =
      (A).rotateLeft 30 := by
    rw [read_d_of_writes h27w]
    simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x1e#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 30 from rfl]
    rw [v26]
    try rfl
  have v28 : read32 c28.core Reg.rbp =
      A := by
    rw [read_d_of_writes h28w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r12) h27w (by decide), read_d_of_other (r := Reg.r12) h26w (by decide), read_d_of_other (r := Reg.r12) h25w (by decide), read_d_of_other (r := Reg.r12) h24w (by decide), read_d_of_other (r := Reg.r12) h23w (by decide), read_d_of_other (r := Reg.r12) h22w (by decide), read_d_of_other (r := Reg.r12) h21w (by decide), read_d_of_other (r := Reg.r12) h20w (by decide), read_d_of_other (r := Reg.r12) h19w (by decide), read_d_of_other (r := Reg.r12) h18w (by decide), read_d_of_other (r := Reg.r12) h17w (by decide), read_d_of_other (r := Reg.r12) h16w (by decide), read_d_of_other (r := Reg.r12) h15w (by decide), read_d_of_other (r := Reg.r12) h14w (by decide), read_d_of_other (r := Reg.r12) h13w (by decide), read_d_of_other (r := Reg.r12) h12w (by decide), read_d_of_other (r := Reg.r12) h11w (by decide), read_d_of_other (r := Reg.r12) h10w (by decide), read_d_of_other (r := Reg.r12) h9w (by decide), read_d_of_other (r := Reg.r12) h8w (by decide), read_d_of_other (r := Reg.r12) h7w (by decide), read_d_of_other (r := Reg.r12) h6w (by decide), read_d_of_other (r := Reg.r12) h5w (by decide), read_d_of_other (r := Reg.r12) h4w (by decide), read_d_of_other (r := Reg.r12) h3w (by decide), read_d_of_other (r := Reg.r12) h2w (by decide), read_d_of_other (r := Reg.r12) h1w (by decide), hA]
    try rfl
  have v29 : read32 c29.core Reg.rbp =
      (A).rotateLeft 19 := by
    rw [read_d_of_writes h29w]
    simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x13#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 19 from rfl]
    rw [v28]
    try rfl
  have v30 : read32 c30.core Reg.r15 =
      A := by
    rw [read_d_of_writes h30w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r12) h29w (by decide), read_d_of_other (r := Reg.r12) h28w (by decide), read_d_of_other (r := Reg.r12) h27w (by decide), read_d_of_other (r := Reg.r12) h26w (by decide), read_d_of_other (r := Reg.r12) h25w (by decide), read_d_of_other (r := Reg.r12) h24w (by decide), read_d_of_other (r := Reg.r12) h23w (by decide), read_d_of_other (r := Reg.r12) h22w (by decide), read_d_of_other (r := Reg.r12) h21w (by decide), read_d_of_other (r := Reg.r12) h20w (by decide), read_d_of_other (r := Reg.r12) h19w (by decide), read_d_of_other (r := Reg.r12) h18w (by decide), read_d_of_other (r := Reg.r12) h17w (by decide), read_d_of_other (r := Reg.r12) h16w (by decide), read_d_of_other (r := Reg.r12) h15w (by decide), read_d_of_other (r := Reg.r12) h14w (by decide), read_d_of_other (r := Reg.r12) h13w (by decide), read_d_of_other (r := Reg.r12) h12w (by decide), read_d_of_other (r := Reg.r12) h11w (by decide), read_d_of_other (r := Reg.r12) h10w (by decide), read_d_of_other (r := Reg.r12) h9w (by decide), read_d_of_other (r := Reg.r12) h8w (by decide), read_d_of_other (r := Reg.r12) h7w (by decide), read_d_of_other (r := Reg.r12) h6w (by decide), read_d_of_other (r := Reg.r12) h5w (by decide), read_d_of_other (r := Reg.r12) h4w (by decide), read_d_of_other (r := Reg.r12) h3w (by decide), read_d_of_other (r := Reg.r12) h2w (by decide), read_d_of_other (r := Reg.r12) h1w (by decide), hA]
    try rfl
  have v31 : read32 c31.core Reg.r15 =
      (A).rotateLeft 10 := by
    rw [read_d_of_writes h31w]
    simp only [← read32_eq, Silmaril.X86.Ext.ShiftOp.result, show ((0x0a#8 : BitVec 8).toNat % Silmaril.X86.Ext.Sz.d.bits) = 10 from rfl]
    rw [v30]
    try rfl
  have v32 : read32 c32.core Reg.rbp =
      ((A).rotateLeft 19) ^^^ ((A).rotateLeft 30) := by
    rw [read_d_of_writes h32w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [read_d_of_other (r := Reg.rbp) h31w (by decide), read_d_of_other (r := Reg.rbp) h30w (by decide), v29, read_d_of_other (r := Reg.rsi) h31w (by decide), read_d_of_other (r := Reg.rsi) h30w (by decide), read_d_of_other (r := Reg.rsi) h29w (by decide), read_d_of_other (r := Reg.rsi) h28w (by decide), v27]
    try rfl
  have v33 : read32 c33.core Reg.r15 =
      ((A).rotateLeft 10) ^^^ (((A).rotateLeft 19) ^^^ ((A).rotateLeft 30)) := by
    rw [read_d_of_writes h33w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [read_d_of_other (r := Reg.r15) h32w (by decide), v31, v32]
    try rfl
  have v34 : read32 c34.core Reg.rsi =
      B := by
    rw [read_d_of_writes h34w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.rdx) h33w (by decide), read_d_of_other (r := Reg.rdx) h32w (by decide), read_d_of_other (r := Reg.rdx) h31w (by decide), read_d_of_other (r := Reg.rdx) h30w (by decide), read_d_of_other (r := Reg.rdx) h29w (by decide), read_d_of_other (r := Reg.rdx) h28w (by decide), read_d_of_other (r := Reg.rdx) h27w (by decide), read_d_of_other (r := Reg.rdx) h26w (by decide), read_d_of_other (r := Reg.rdx) h25w (by decide), read_d_of_other (r := Reg.rdx) h24w (by decide), read_d_of_other (r := Reg.rdx) h23w (by decide), read_d_of_other (r := Reg.rdx) h22w (by decide), read_d_of_other (r := Reg.rdx) h21w (by decide), read_d_of_other (r := Reg.rdx) h20w (by decide), read_d_of_other (r := Reg.rdx) h19w (by decide), read_d_of_other (r := Reg.rdx) h18w (by decide), read_d_of_other (r := Reg.rdx) h17w (by decide), read_d_of_other (r := Reg.rdx) h16w (by decide), read_d_of_other (r := Reg.rdx) h15w (by decide), read_d_of_other (r := Reg.rdx) h14w (by decide), read_d_of_other (r := Reg.rdx) h13w (by decide), read_d_of_other (r := Reg.rdx) h12w (by decide), read_d_of_other (r := Reg.rdx) h11w (by decide), read_d_of_other (r := Reg.rdx) h10w (by decide), read_d_of_other (r := Reg.rdx) h9w (by decide), read_d_of_other (r := Reg.rdx) h8w (by decide), read_d_of_other (r := Reg.rdx) h7w (by decide), v6]
    try rfl
  have v35 : read32 c35.core Reg.rsi =
      (B) ^^^ (C) := by
    rw [read_d_of_writes h35w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v34, read_d_of_other (r := Reg.r11) h34w (by decide), read_d_of_other (r := Reg.r11) h33w (by decide), read_d_of_other (r := Reg.r11) h32w (by decide), read_d_of_other (r := Reg.r11) h31w (by decide), read_d_of_other (r := Reg.r11) h30w (by decide), read_d_of_other (r := Reg.r11) h29w (by decide), read_d_of_other (r := Reg.r11) h28w (by decide), read_d_of_other (r := Reg.r11) h27w (by decide), read_d_of_other (r := Reg.r11) h26w (by decide), read_d_of_other (r := Reg.r11) h25w (by decide), read_d_of_other (r := Reg.r11) h24w (by decide), read_d_of_other (r := Reg.r11) h23w (by decide), read_d_of_other (r := Reg.r11) h22w (by decide), read_d_of_other (r := Reg.r11) h21w (by decide), read_d_of_other (r := Reg.r11) h20w (by decide), read_d_of_other (r := Reg.r11) h19w (by decide), read_d_of_other (r := Reg.r11) h18w (by decide), read_d_of_other (r := Reg.r11) h17w (by decide), read_d_of_other (r := Reg.r11) h16w (by decide), read_d_of_other (r := Reg.r11) h15w (by decide), read_d_of_other (r := Reg.r11) h14w (by decide), read_d_of_other (r := Reg.r11) h13w (by decide), read_d_of_other (r := Reg.r11) h12w (by decide), read_d_of_other (r := Reg.r11) h11w (by decide), read_d_of_other (r := Reg.r11) h10w (by decide), read_d_of_other (r := Reg.r11) h9w (by decide), read_d_of_other (r := Reg.r11) h8w (by decide), read_d_of_other (r := Reg.r11) h7w (by decide), read_d_of_other (r := Reg.r11) h6w (by decide), v5]
    try rfl
  have v36 : read32 c36.core Reg.rsi =
      ((B) ^^^ (C)) &&& (A) := by
    rw [read_d_of_writes h36w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v35, read_d_of_other (r := Reg.r12) h35w (by decide), read_d_of_other (r := Reg.r12) h34w (by decide), read_d_of_other (r := Reg.r12) h33w (by decide), read_d_of_other (r := Reg.r12) h32w (by decide), read_d_of_other (r := Reg.r12) h31w (by decide), read_d_of_other (r := Reg.r12) h30w (by decide), read_d_of_other (r := Reg.r12) h29w (by decide), read_d_of_other (r := Reg.r12) h28w (by decide), read_d_of_other (r := Reg.r12) h27w (by decide), read_d_of_other (r := Reg.r12) h26w (by decide), read_d_of_other (r := Reg.r12) h25w (by decide), read_d_of_other (r := Reg.r12) h24w (by decide), read_d_of_other (r := Reg.r12) h23w (by decide), read_d_of_other (r := Reg.r12) h22w (by decide), read_d_of_other (r := Reg.r12) h21w (by decide), read_d_of_other (r := Reg.r12) h20w (by decide), read_d_of_other (r := Reg.r12) h19w (by decide), read_d_of_other (r := Reg.r12) h18w (by decide), read_d_of_other (r := Reg.r12) h17w (by decide), read_d_of_other (r := Reg.r12) h16w (by decide), read_d_of_other (r := Reg.r12) h15w (by decide), read_d_of_other (r := Reg.r12) h14w (by decide), read_d_of_other (r := Reg.r12) h13w (by decide), read_d_of_other (r := Reg.r12) h12w (by decide), read_d_of_other (r := Reg.r12) h11w (by decide), read_d_of_other (r := Reg.r12) h10w (by decide), read_d_of_other (r := Reg.r12) h9w (by decide), read_d_of_other (r := Reg.r12) h8w (by decide), read_d_of_other (r := Reg.r12) h7w (by decide), read_d_of_other (r := Reg.r12) h6w (by decide), read_d_of_other (r := Reg.r12) h5w (by decide), read_d_of_other (r := Reg.r12) h4w (by decide), read_d_of_other (r := Reg.r12) h3w (by decide), read_d_of_other (r := Reg.r12) h2w (by decide), read_d_of_other (r := Reg.r12) h1w (by decide), hA]
    try rfl
  have v37 : read32 c37.core Reg.r12 =
      B := by
    rw [read_d_of_writes h37w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.rdx) h36w (by decide), read_d_of_other (r := Reg.rdx) h35w (by decide), read_d_of_other (r := Reg.rdx) h34w (by decide), read_d_of_other (r := Reg.rdx) h33w (by decide), read_d_of_other (r := Reg.rdx) h32w (by decide), read_d_of_other (r := Reg.rdx) h31w (by decide), read_d_of_other (r := Reg.rdx) h30w (by decide), read_d_of_other (r := Reg.rdx) h29w (by decide), read_d_of_other (r := Reg.rdx) h28w (by decide), read_d_of_other (r := Reg.rdx) h27w (by decide), read_d_of_other (r := Reg.rdx) h26w (by decide), read_d_of_other (r := Reg.rdx) h25w (by decide), read_d_of_other (r := Reg.rdx) h24w (by decide), read_d_of_other (r := Reg.rdx) h23w (by decide), read_d_of_other (r := Reg.rdx) h22w (by decide), read_d_of_other (r := Reg.rdx) h21w (by decide), read_d_of_other (r := Reg.rdx) h20w (by decide), read_d_of_other (r := Reg.rdx) h19w (by decide), read_d_of_other (r := Reg.rdx) h18w (by decide), read_d_of_other (r := Reg.rdx) h17w (by decide), read_d_of_other (r := Reg.rdx) h16w (by decide), read_d_of_other (r := Reg.rdx) h15w (by decide), read_d_of_other (r := Reg.rdx) h14w (by decide), read_d_of_other (r := Reg.rdx) h13w (by decide), read_d_of_other (r := Reg.rdx) h12w (by decide), read_d_of_other (r := Reg.rdx) h11w (by decide), read_d_of_other (r := Reg.rdx) h10w (by decide), read_d_of_other (r := Reg.rdx) h9w (by decide), read_d_of_other (r := Reg.rdx) h8w (by decide), read_d_of_other (r := Reg.rdx) h7w (by decide), v6]
    try rfl
  have v38 : read32 c38.core Reg.r12 =
      (B) &&& (C) := by
    rw [read_d_of_writes h38w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v37, read_d_of_other (r := Reg.r11) h37w (by decide), read_d_of_other (r := Reg.r11) h36w (by decide), read_d_of_other (r := Reg.r11) h35w (by decide), read_d_of_other (r := Reg.r11) h34w (by decide), read_d_of_other (r := Reg.r11) h33w (by decide), read_d_of_other (r := Reg.r11) h32w (by decide), read_d_of_other (r := Reg.r11) h31w (by decide), read_d_of_other (r := Reg.r11) h30w (by decide), read_d_of_other (r := Reg.r11) h29w (by decide), read_d_of_other (r := Reg.r11) h28w (by decide), read_d_of_other (r := Reg.r11) h27w (by decide), read_d_of_other (r := Reg.r11) h26w (by decide), read_d_of_other (r := Reg.r11) h25w (by decide), read_d_of_other (r := Reg.r11) h24w (by decide), read_d_of_other (r := Reg.r11) h23w (by decide), read_d_of_other (r := Reg.r11) h22w (by decide), read_d_of_other (r := Reg.r11) h21w (by decide), read_d_of_other (r := Reg.r11) h20w (by decide), read_d_of_other (r := Reg.r11) h19w (by decide), read_d_of_other (r := Reg.r11) h18w (by decide), read_d_of_other (r := Reg.r11) h17w (by decide), read_d_of_other (r := Reg.r11) h16w (by decide), read_d_of_other (r := Reg.r11) h15w (by decide), read_d_of_other (r := Reg.r11) h14w (by decide), read_d_of_other (r := Reg.r11) h13w (by decide), read_d_of_other (r := Reg.r11) h12w (by decide), read_d_of_other (r := Reg.r11) h11w (by decide), read_d_of_other (r := Reg.r11) h10w (by decide), read_d_of_other (r := Reg.r11) h9w (by decide), read_d_of_other (r := Reg.r11) h8w (by decide), read_d_of_other (r := Reg.r11) h7w (by decide), read_d_of_other (r := Reg.r11) h6w (by decide), v5]
    try rfl
  have v39 : read32 c39.core Reg.r12 =
      ((B) &&& (C)) ^^^ (((B) ^^^ (C)) &&& (A)) := by
    rw [read_d_of_writes h39w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v38, read_d_of_other (r := Reg.rsi) h38w (by decide), read_d_of_other (r := Reg.rsi) h37w (by decide), v36]
    try rfl
  have v40 : read32 c40.core Reg.r12 =
      (((B) &&& (C)) ^^^ (((B) ^^^ (C)) &&& (A))) + (((A).rotateLeft 10) ^^^ (((A).rotateLeft 19) ^^^ ((A).rotateLeft 30))) := by
    rw [read_d_of_writes h40w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [v39, read_d_of_other (r := Reg.r15) h39w (by decide), read_d_of_other (r := Reg.r15) h38w (by decide), read_d_of_other (r := Reg.r15) h37w (by decide), read_d_of_other (r := Reg.r15) h36w (by decide), read_d_of_other (r := Reg.r15) h35w (by decide), read_d_of_other (r := Reg.r15) h34w (by decide), v33]
    try rfl
  have v41 : read32 c41.core Reg.r13 =
      (D) + ((((((~~~(E)) &&& (G)) + (((F) &&& (E)) + (H))) + (((E).rotateLeft 7) ^^^ (((E).rotateLeft 21) ^^^ ((E).rotateLeft 26)))) + ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32)) + ((BitVec.ofNat 64 (wv.toNat % 2 ^ (8 * 4))).setWidth 32)) := by
    rw [read_d_of_writes h41w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [read_d_of_other (r := Reg.r13) h40w (by decide), read_d_of_other (r := Reg.r13) h39w (by decide), read_d_of_other (r := Reg.r13) h38w (by decide), read_d_of_other (r := Reg.r13) h37w (by decide), read_d_of_other (r := Reg.r13) h36w (by decide), read_d_of_other (r := Reg.r13) h35w (by decide), read_d_of_other (r := Reg.r13) h34w (by decide), read_d_of_other (r := Reg.r13) h33w (by decide), read_d_of_other (r := Reg.r13) h32w (by decide), read_d_of_other (r := Reg.r13) h31w (by decide), read_d_of_other (r := Reg.r13) h30w (by decide), read_d_of_other (r := Reg.r13) h29w (by decide), read_d_of_other (r := Reg.r13) h28w (by decide), read_d_of_other (r := Reg.r13) h27w (by decide), read_d_of_other (r := Reg.r13) h26w (by decide), read_d_of_other (r := Reg.r13) h25w (by decide), read_d_of_other (r := Reg.r13) h24w (by decide), read_d_of_other (r := Reg.r13) h23w (by decide), read_d_of_other (r := Reg.r13) h22w (by decide), read_d_of_other (r := Reg.r13) h21w (by decide), read_d_of_other (r := Reg.r13) h20w (by decide), read_d_of_other (r := Reg.r13) h19w (by decide), read_d_of_other (r := Reg.r13) h18w (by decide), read_d_of_other (r := Reg.r13) h17w (by decide), read_d_of_other (r := Reg.r13) h16w (by decide), read_d_of_other (r := Reg.r13) h15w (by decide), read_d_of_other (r := Reg.r13) h14w (by decide), read_d_of_other (r := Reg.r13) h13w (by decide), read_d_of_other (r := Reg.r13) h12w (by decide), read_d_of_other (r := Reg.r13) h11w (by decide), read_d_of_other (r := Reg.r13) h10w (by decide), read_d_of_other (r := Reg.r13) h9w (by decide), read_d_of_other (r := Reg.r13) h8w (by decide), read_d_of_other (r := Reg.r13) h7w (by decide), read_d_of_other (r := Reg.r13) h6w (by decide), read_d_of_other (r := Reg.r13) h5w (by decide), v4, read_d_of_other (r := Reg.r14) h40w (by decide), read_d_of_other (r := Reg.r14) h39w (by decide), read_d_of_other (r := Reg.r14) h38w (by decide), read_d_of_other (r := Reg.r14) h37w (by decide), read_d_of_other (r := Reg.r14) h36w (by decide), read_d_of_other (r := Reg.r14) h35w (by decide), read_d_of_other (r := Reg.r14) h34w (by decide), read_d_of_other (r := Reg.r14) h33w (by decide), read_d_of_other (r := Reg.r14) h32w (by decide), read_d_of_other (r := Reg.r14) h31w (by decide), read_d_of_other (r := Reg.r14) h30w (by decide), read_d_of_other (r := Reg.r14) h29w (by decide), read_d_of_other (r := Reg.r14) h28w (by decide), read_d_of_other (r := Reg.r14) h27w (by decide), read_d_of_other (r := Reg.r14) h26w (by decide), read_d_of_other (r := Reg.r14) h25w (by decide), v24]
    try rfl
  have v42 : read32 c42.core Reg.r12 =
      ((((B) &&& (C)) ^^^ (((B) ^^^ (C)) &&& (A))) + (((A).rotateLeft 10) ^^^ (((A).rotateLeft 19) ^^^ ((A).rotateLeft 30)))) + ((((((~~~(E)) &&& (G)) + (((F) &&& (E)) + (H))) + (((E).rotateLeft 7) ^^^ (((E).rotateLeft 21) ^^^ ((E).rotateLeft 26)))) + ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32)) + ((BitVec.ofNat 64 (wv.toNat % 2 ^ (8 * 4))).setWidth 32)) := by
    rw [read_d_of_writes h42w]
    simp only [← read32_eq, Silmaril.X86.Ext.AluOp.resultN]
    rw [read_d_of_other (r := Reg.r12) h41w (by decide), v40, read_d_of_other (r := Reg.r14) h41w (by decide), read_d_of_other (r := Reg.r14) h40w (by decide), read_d_of_other (r := Reg.r14) h39w (by decide), read_d_of_other (r := Reg.r14) h38w (by decide), read_d_of_other (r := Reg.r14) h37w (by decide), read_d_of_other (r := Reg.r14) h36w (by decide), read_d_of_other (r := Reg.r14) h35w (by decide), read_d_of_other (r := Reg.r14) h34w (by decide), read_d_of_other (r := Reg.r14) h33w (by decide), read_d_of_other (r := Reg.r14) h32w (by decide), read_d_of_other (r := Reg.r14) h31w (by decide), read_d_of_other (r := Reg.r14) h30w (by decide), read_d_of_other (r := Reg.r14) h29w (by decide), read_d_of_other (r := Reg.r14) h28w (by decide), read_d_of_other (r := Reg.r14) h27w (by decide), read_d_of_other (r := Reg.r14) h26w (by decide), read_d_of_other (r := Reg.r14) h25w (by decide), v24]
    try rfl
  have v44 : read32 c44.core Reg.r14 =
      G := by
    rw [read_d_of_writes h44w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.rbx) h43w (by decide), read_d_of_other (r := Reg.rbx) h42w (by decide), read_d_of_other (r := Reg.rbx) h41w (by decide), read_d_of_other (r := Reg.rbx) h40w (by decide), read_d_of_other (r := Reg.rbx) h39w (by decide), read_d_of_other (r := Reg.rbx) h38w (by decide), read_d_of_other (r := Reg.rbx) h37w (by decide), read_d_of_other (r := Reg.rbx) h36w (by decide), read_d_of_other (r := Reg.rbx) h35w (by decide), read_d_of_other (r := Reg.rbx) h34w (by decide), read_d_of_other (r := Reg.rbx) h33w (by decide), read_d_of_other (r := Reg.rbx) h32w (by decide), read_d_of_other (r := Reg.rbx) h31w (by decide), read_d_of_other (r := Reg.rbx) h30w (by decide), read_d_of_other (r := Reg.rbx) h29w (by decide), read_d_of_other (r := Reg.rbx) h28w (by decide), read_d_of_other (r := Reg.rbx) h27w (by decide), read_d_of_other (r := Reg.rbx) h26w (by decide), read_d_of_other (r := Reg.rbx) h25w (by decide), read_d_of_other (r := Reg.rbx) h24w (by decide), read_d_of_other (r := Reg.rbx) h23w (by decide), read_d_of_other (r := Reg.rbx) h22w (by decide), read_d_of_other (r := Reg.rbx) h21w (by decide), read_d_of_other (r := Reg.rbx) h20w (by decide), read_d_of_other (r := Reg.rbx) h19w (by decide), read_d_of_other (r := Reg.rbx) h18w (by decide), read_d_of_other (r := Reg.rbx) h17w (by decide), read_d_of_other (r := Reg.rbx) h16w (by decide), read_d_of_other (r := Reg.rbx) h15w (by decide), read_d_of_other (r := Reg.rbx) h14w (by decide), read_d_of_other (r := Reg.rbx) h13w (by decide), read_d_of_other (r := Reg.rbx) h12w (by decide), read_d_of_other (r := Reg.rbx) h11w (by decide), read_d_of_other (r := Reg.rbx) h10w (by decide), read_d_of_other (r := Reg.rbx) h9w (by decide), read_d_of_other (r := Reg.rbx) h8w (by decide), read_d_of_other (r := Reg.rbx) h7w (by decide), read_d_of_other (r := Reg.rbx) h6w (by decide), read_d_of_other (r := Reg.rbx) h5w (by decide), read_d_of_other (r := Reg.rbx) h4w (by decide), v3]
    try rfl
  have v45 : read32 c45.core Reg.rbp =
      F := by
    rw [read_d_of_writes h45w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r9) h44w (by decide), read_d_of_other (r := Reg.r9) h43w (by decide), read_d_of_other (r := Reg.r9) h42w (by decide), read_d_of_other (r := Reg.r9) h41w (by decide), read_d_of_other (r := Reg.r9) h40w (by decide), read_d_of_other (r := Reg.r9) h39w (by decide), read_d_of_other (r := Reg.r9) h38w (by decide), read_d_of_other (r := Reg.r9) h37w (by decide), read_d_of_other (r := Reg.r9) h36w (by decide), read_d_of_other (r := Reg.r9) h35w (by decide), read_d_of_other (r := Reg.r9) h34w (by decide), read_d_of_other (r := Reg.r9) h33w (by decide), read_d_of_other (r := Reg.r9) h32w (by decide), read_d_of_other (r := Reg.r9) h31w (by decide), read_d_of_other (r := Reg.r9) h30w (by decide), read_d_of_other (r := Reg.r9) h29w (by decide), read_d_of_other (r := Reg.r9) h28w (by decide), read_d_of_other (r := Reg.r9) h27w (by decide), read_d_of_other (r := Reg.r9) h26w (by decide), read_d_of_other (r := Reg.r9) h25w (by decide), read_d_of_other (r := Reg.r9) h24w (by decide), read_d_of_other (r := Reg.r9) h23w (by decide), read_d_of_other (r := Reg.r9) h22w (by decide), read_d_of_other (r := Reg.r9) h21w (by decide), read_d_of_other (r := Reg.r9) h20w (by decide), read_d_of_other (r := Reg.r9) h19w (by decide), read_d_of_other (r := Reg.r9) h18w (by decide), read_d_of_other (r := Reg.r9) h17w (by decide), read_d_of_other (r := Reg.r9) h16w (by decide), read_d_of_other (r := Reg.r9) h15w (by decide), read_d_of_other (r := Reg.r9) h14w (by decide), read_d_of_other (r := Reg.r9) h13w (by decide), read_d_of_other (r := Reg.r9) h12w (by decide), read_d_of_other (r := Reg.r9) h11w (by decide), read_d_of_other (r := Reg.r9) h10w (by decide), read_d_of_other (r := Reg.r9) h9w (by decide), read_d_of_other (r := Reg.r9) h8w (by decide), read_d_of_other (r := Reg.r9) h7w (by decide), read_d_of_other (r := Reg.r9) h6w (by decide), read_d_of_other (r := Reg.r9) h5w (by decide), read_d_of_other (r := Reg.r9) h4w (by decide), read_d_of_other (r := Reg.r9) h3w (by decide), v2]
    try rfl
  have v46 : read32 c46.core Reg.rsi =
      E := by
    rw [read_d_of_writes h46w]
    simp only [← read32_eq]
    rw [read_d_of_other (r := Reg.r10) h45w (by decide), read_d_of_other (r := Reg.r10) h44w (by decide), read_d_of_other (r := Reg.r10) h43w (by decide), read_d_of_other (r := Reg.r10) h42w (by decide), read_d_of_other (r := Reg.r10) h41w (by decide), read_d_of_other (r := Reg.r10) h40w (by decide), read_d_of_other (r := Reg.r10) h39w (by decide), read_d_of_other (r := Reg.r10) h38w (by decide), read_d_of_other (r := Reg.r10) h37w (by decide), read_d_of_other (r := Reg.r10) h36w (by decide), read_d_of_other (r := Reg.r10) h35w (by decide), read_d_of_other (r := Reg.r10) h34w (by decide), read_d_of_other (r := Reg.r10) h33w (by decide), read_d_of_other (r := Reg.r10) h32w (by decide), read_d_of_other (r := Reg.r10) h31w (by decide), read_d_of_other (r := Reg.r10) h30w (by decide), read_d_of_other (r := Reg.r10) h29w (by decide), read_d_of_other (r := Reg.r10) h28w (by decide), read_d_of_other (r := Reg.r10) h27w (by decide), read_d_of_other (r := Reg.r10) h26w (by decide), read_d_of_other (r := Reg.r10) h25w (by decide), read_d_of_other (r := Reg.r10) h24w (by decide), read_d_of_other (r := Reg.r10) h23w (by decide), read_d_of_other (r := Reg.r10) h22w (by decide), read_d_of_other (r := Reg.r10) h21w (by decide), read_d_of_other (r := Reg.r10) h20w (by decide), read_d_of_other (r := Reg.r10) h19w (by decide), read_d_of_other (r := Reg.r10) h18w (by decide), read_d_of_other (r := Reg.r10) h17w (by decide), read_d_of_other (r := Reg.r10) h16w (by decide), read_d_of_other (r := Reg.r10) h15w (by decide), read_d_of_other (r := Reg.r10) h14w (by decide), read_d_of_other (r := Reg.r10) h13w (by decide), read_d_of_other (r := Reg.r10) h12w (by decide), read_d_of_other (r := Reg.r10) h11w (by decide), read_d_of_other (r := Reg.r10) h10w (by decide), read_d_of_other (r := Reg.r10) h9w (by decide), read_d_of_other (r := Reg.r10) h8w (by decide), read_d_of_other (r := Reg.r10) h7w (by decide), read_d_of_other (r := Reg.r10) h6w (by decide), read_d_of_other (r := Reg.r10) h5w (by decide), read_d_of_other (r := Reg.r10) h4w (by decide), read_d_of_other (r := Reg.r10) h3w (by decide), read_d_of_other (r := Reg.r10) h2w (by decide), v1]
    try rfl
  have f_r12 : read32 c46.core Reg.r12 =
      ((((B) &&& (C)) ^^^ (((B) ^^^ (C)) &&& (A))) + (((A).rotateLeft 10) ^^^ (((A).rotateLeft 19) ^^^ ((A).rotateLeft 30)))) + ((((((~~~(E)) &&& (G)) + (((F) &&& (E)) + (H))) + (((E).rotateLeft 7) ^^^ (((E).rotateLeft 21) ^^^ ((E).rotateLeft 26)))) + ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32)) + ((BitVec.ofNat 64 (wv.toNat % 2 ^ (8 * 4))).setWidth 32)) := by
    rw [read_d_of_other (r := Reg.r12) h46w (by decide), read_d_of_other (r := Reg.r12) h45w (by decide), read_d_of_other (r := Reg.r12) h44w (by decide), read_d_of_other (r := Reg.r12) h43w (by decide), v42]
    try rfl
  have f_r8 : read32 c46.core Reg.r8 =
      A := by
    rw [read_d_of_other (r := Reg.r8) h46w (by decide), read_d_of_other (r := Reg.r8) h45w (by decide), read_d_of_other (r := Reg.r8) h44w (by decide), read_d_of_other (r := Reg.r8) h43w (by decide), read_d_of_other (r := Reg.r8) h42w (by decide), read_d_of_other (r := Reg.r8) h41w (by decide), read_d_of_other (r := Reg.r8) h40w (by decide), read_d_of_other (r := Reg.r8) h39w (by decide), read_d_of_other (r := Reg.r8) h38w (by decide), read_d_of_other (r := Reg.r8) h37w (by decide), read_d_of_other (r := Reg.r8) h36w (by decide), read_d_of_other (r := Reg.r8) h35w (by decide), read_d_of_other (r := Reg.r8) h34w (by decide), read_d_of_other (r := Reg.r8) h33w (by decide), read_d_of_other (r := Reg.r8) h32w (by decide), read_d_of_other (r := Reg.r8) h31w (by decide), read_d_of_other (r := Reg.r8) h30w (by decide), read_d_of_other (r := Reg.r8) h29w (by decide), read_d_of_other (r := Reg.r8) h28w (by decide), read_d_of_other (r := Reg.r8) h27w (by decide), read_d_of_other (r := Reg.r8) h26w (by decide), v25]
    try rfl
  have f_rdx : read32 c46.core Reg.rdx =
      B := by
    rw [read_d_of_other (r := Reg.rdx) h46w (by decide), read_d_of_other (r := Reg.rdx) h45w (by decide), read_d_of_other (r := Reg.rdx) h44w (by decide), read_d_of_other (r := Reg.rdx) h43w (by decide), read_d_of_other (r := Reg.rdx) h42w (by decide), read_d_of_other (r := Reg.rdx) h41w (by decide), read_d_of_other (r := Reg.rdx) h40w (by decide), read_d_of_other (r := Reg.rdx) h39w (by decide), read_d_of_other (r := Reg.rdx) h38w (by decide), read_d_of_other (r := Reg.rdx) h37w (by decide), read_d_of_other (r := Reg.rdx) h36w (by decide), read_d_of_other (r := Reg.rdx) h35w (by decide), read_d_of_other (r := Reg.rdx) h34w (by decide), read_d_of_other (r := Reg.rdx) h33w (by decide), read_d_of_other (r := Reg.rdx) h32w (by decide), read_d_of_other (r := Reg.rdx) h31w (by decide), read_d_of_other (r := Reg.rdx) h30w (by decide), read_d_of_other (r := Reg.rdx) h29w (by decide), read_d_of_other (r := Reg.rdx) h28w (by decide), read_d_of_other (r := Reg.rdx) h27w (by decide), read_d_of_other (r := Reg.rdx) h26w (by decide), read_d_of_other (r := Reg.rdx) h25w (by decide), read_d_of_other (r := Reg.rdx) h24w (by decide), read_d_of_other (r := Reg.rdx) h23w (by decide), read_d_of_other (r := Reg.rdx) h22w (by decide), read_d_of_other (r := Reg.rdx) h21w (by decide), read_d_of_other (r := Reg.rdx) h20w (by decide), read_d_of_other (r := Reg.rdx) h19w (by decide), read_d_of_other (r := Reg.rdx) h18w (by decide), read_d_of_other (r := Reg.rdx) h17w (by decide), read_d_of_other (r := Reg.rdx) h16w (by decide), read_d_of_other (r := Reg.rdx) h15w (by decide), read_d_of_other (r := Reg.rdx) h14w (by decide), read_d_of_other (r := Reg.rdx) h13w (by decide), read_d_of_other (r := Reg.rdx) h12w (by decide), read_d_of_other (r := Reg.rdx) h11w (by decide), read_d_of_other (r := Reg.rdx) h10w (by decide), read_d_of_other (r := Reg.rdx) h9w (by decide), read_d_of_other (r := Reg.rdx) h8w (by decide), read_d_of_other (r := Reg.rdx) h7w (by decide), v6]
    try rfl
  have f_r11 : read32 c46.core Reg.r11 =
      C := by
    rw [read_d_of_other (r := Reg.r11) h46w (by decide), read_d_of_other (r := Reg.r11) h45w (by decide), read_d_of_other (r := Reg.r11) h44w (by decide), read_d_of_other (r := Reg.r11) h43w (by decide), read_d_of_other (r := Reg.r11) h42w (by decide), read_d_of_other (r := Reg.r11) h41w (by decide), read_d_of_other (r := Reg.r11) h40w (by decide), read_d_of_other (r := Reg.r11) h39w (by decide), read_d_of_other (r := Reg.r11) h38w (by decide), read_d_of_other (r := Reg.r11) h37w (by decide), read_d_of_other (r := Reg.r11) h36w (by decide), read_d_of_other (r := Reg.r11) h35w (by decide), read_d_of_other (r := Reg.r11) h34w (by decide), read_d_of_other (r := Reg.r11) h33w (by decide), read_d_of_other (r := Reg.r11) h32w (by decide), read_d_of_other (r := Reg.r11) h31w (by decide), read_d_of_other (r := Reg.r11) h30w (by decide), read_d_of_other (r := Reg.r11) h29w (by decide), read_d_of_other (r := Reg.r11) h28w (by decide), read_d_of_other (r := Reg.r11) h27w (by decide), read_d_of_other (r := Reg.r11) h26w (by decide), read_d_of_other (r := Reg.r11) h25w (by decide), read_d_of_other (r := Reg.r11) h24w (by decide), read_d_of_other (r := Reg.r11) h23w (by decide), read_d_of_other (r := Reg.r11) h22w (by decide), read_d_of_other (r := Reg.r11) h21w (by decide), read_d_of_other (r := Reg.r11) h20w (by decide), read_d_of_other (r := Reg.r11) h19w (by decide), read_d_of_other (r := Reg.r11) h18w (by decide), read_d_of_other (r := Reg.r11) h17w (by decide), read_d_of_other (r := Reg.r11) h16w (by decide), read_d_of_other (r := Reg.r11) h15w (by decide), read_d_of_other (r := Reg.r11) h14w (by decide), read_d_of_other (r := Reg.r11) h13w (by decide), read_d_of_other (r := Reg.r11) h12w (by decide), read_d_of_other (r := Reg.r11) h11w (by decide), read_d_of_other (r := Reg.r11) h10w (by decide), read_d_of_other (r := Reg.r11) h9w (by decide), read_d_of_other (r := Reg.r11) h8w (by decide), read_d_of_other (r := Reg.r11) h7w (by decide), read_d_of_other (r := Reg.r11) h6w (by decide), v5]
    try rfl
  have f_r13 : read32 c46.core Reg.r13 =
      (D) + ((((((~~~(E)) &&& (G)) + (((F) &&& (E)) + (H))) + (((E).rotateLeft 7) ^^^ (((E).rotateLeft 21) ^^^ ((E).rotateLeft 26)))) + ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32)) + ((BitVec.ofNat 64 (wv.toNat % 2 ^ (8 * 4))).setWidth 32)) := by
    rw [read_d_of_other (r := Reg.r13) h46w (by decide), read_d_of_other (r := Reg.r13) h45w (by decide), read_d_of_other (r := Reg.r13) h44w (by decide), read_d_of_other (r := Reg.r13) h43w (by decide), read_d_of_other (r := Reg.r13) h42w (by decide), v41]
    try rfl
  have f_rsi : read32 c46.core Reg.rsi =
      E := by
    rw [v46]
    try rfl
  have f_rbp : read32 c46.core Reg.rbp =
      F := by
    rw [read_d_of_other (r := Reg.rbp) h46w (by decide), v45]
    try rfl
  have f_r14 : read32 c46.core Reg.r14 =
      G := by
    rw [read_d_of_other (r := Reg.r14) h46w (by decide), read_d_of_other (r := Reg.r14) h45w (by decide), v44]
    try rfl
  -- the round, in the specification's vocabulary
  have hrdef : SHA256.Kernel.round A B C D E F G H
      ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32)
      ((BitVec.ofNat 64 (wv.toNat % 2 ^ (8 * 4))).setWidth 32)
      = ((H + SHA256.Kernel.Sigma1 E + SHA256.Kernel.Ch E F G + ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32) + ((BitVec.ofNat 64 (wv.toNat % 2 ^ (8 * 4))).setWidth 32)) + (SHA256.Kernel.Sigma0 A + SHA256.Kernel.Maj A B C), A, B, C, D + (H + SHA256.Kernel.Sigma1 E + SHA256.Kernel.Ch E F G + ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32) + ((BitVec.ofNat 64 (wv.toNat % 2 ^ (8 * 4))).setWidth 32)), E, F, G) := rfl
  have hround :
      (read32 c46.core Reg.r12,
       read32 c46.core Reg.r8,
       read32 c46.core Reg.rdx,
       read32 c46.core Reg.r11,
       read32 c46.core Reg.r13,
       read32 c46.core Reg.rsi,
       read32 c46.core Reg.rbp,
       read32 c46.core Reg.r14)
      = SHA256.Kernel.round A B C D E F G H
          ((BitVec.ofNat 64 (kv.toNat % 2 ^ (8 * 4))).setWidth 32)
          ((BitVec.ofNat 64 (wv.toNat % 2 ^ (8 * 4))).setWidth 32) := by
    rw [hrdef, f_r12, f_r8, f_rdx, f_r11, f_r13, f_rsi, f_rbp, f_r14]
    simp only [← ch_eq_add E F G, ← sigma1_eq_rol E, ← maj_eq_factored A B C,
      ← sigma0_eq_rol A, Prod.mk.injEq]
    and_intros <;> first | trivial | ac_rfl
  -- 362: cmp $0x100,%rax
  obtain ⟨c47, s47, h47rip, h47regs, h47flags, h47mem⟩ :=
    stepOpt_cmpA (exit := L.exit) (offset := 362) (len := 6)
      (hld a46.mem) a46.rip (by rw [himg]; decide) e362
  have hcond : Silmaril.X86.Ext.Cond.ne.eval c47.core.flags
      = some (decide (t + 1 ≠ 64)) := by
    rw [h47flags]
    simp only [Silmaril.X86.Ext.Sz.read_q]
    show Silmaril.X86.Ext.Cond.ne.eval (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp
        (c46.core.read Reg.rax) ((0x00000100#32 : BitVec 32).signExtend 64)) = _
    rw [Silmaril.X86.Ext.eval_ne_cmp, a46.rax,
      show ((0x00000100#32 : BitVec 32).signExtend 64) = BitVec.ofNat 64 256 from rfl]
    congr 1
    simp only [l3_counter_ne ht]
  -- 368: jne 224
  have htarget : (if decide (t + 1 ≠ 64) = true then
        L.textBase + BitVec.ofNat 64 (368 + 6) + (0xffffff6a#32 : BitVec 32).signExtend 64
      else L.textBase + BitVec.ofNat 64 (368 + 6))
      = L.textBase + BitVec.ofNat 64 (if t + 1 < 64 then 224 else 374) := by
    by_cases hlast : t + 1 = 64
    · rw [show (decide (t + 1 ≠ 64)) = false from by simp [hlast]]
      rw [show (if t + 1 < 64 then (224 : Nat) else 374) = 374 from by simp [hlast]]
      rfl
    · rw [show (decide (t + 1 ≠ 64)) = true from by simp [hlast]]
      rw [show (if t + 1 < 64 then (224 : Nat) else 374) = 224 from
        ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      exact l3_backedge L.textBase
  obtain ⟨c48, s48, h48rip, h48regs, _, h48mem⟩ :=
    Silmaril.X86.Ext.stepOpt_jcc (exit := L.exit) (offset := 368) (len := 6)
      (hld (h47mem.trans a46.mem)) h47rip (by rw [himg]; decide) e368 hcond htarget
  have g_r10 : read32 c48.core Reg.r10 = E := by
    rw [read32_of_sameRegs h48regs, read32_of_sameRegs h47regs, read_d_of_other (r := Reg.r10) h46w (by decide), read_d_of_other (r := Reg.r10) h45w (by decide), read_d_of_other (r := Reg.r10) h44w (by decide), read_d_of_other (r := Reg.r10) h43w (by decide), read_d_of_other (r := Reg.r10) h42w (by decide), read_d_of_other (r := Reg.r10) h41w (by decide), read_d_of_other (r := Reg.r10) h40w (by decide), read_d_of_other (r := Reg.r10) h39w (by decide), read_d_of_other (r := Reg.r10) h38w (by decide), read_d_of_other (r := Reg.r10) h37w (by decide), read_d_of_other (r := Reg.r10) h36w (by decide), read_d_of_other (r := Reg.r10) h35w (by decide), read_d_of_other (r := Reg.r10) h34w (by decide), read_d_of_other (r := Reg.r10) h33w (by decide), read_d_of_other (r := Reg.r10) h32w (by decide), read_d_of_other (r := Reg.r10) h31w (by decide), read_d_of_other (r := Reg.r10) h30w (by decide), read_d_of_other (r := Reg.r10) h29w (by decide), read_d_of_other (r := Reg.r10) h28w (by decide), read_d_of_other (r := Reg.r10) h27w (by decide), read_d_of_other (r := Reg.r10) h26w (by decide), read_d_of_other (r := Reg.r10) h25w (by decide), read_d_of_other (r := Reg.r10) h24w (by decide), read_d_of_other (r := Reg.r10) h23w (by decide), read_d_of_other (r := Reg.r10) h22w (by decide), read_d_of_other (r := Reg.r10) h21w (by decide), read_d_of_other (r := Reg.r10) h20w (by decide), read_d_of_other (r := Reg.r10) h19w (by decide), read_d_of_other (r := Reg.r10) h18w (by decide), read_d_of_other (r := Reg.r10) h17w (by decide), read_d_of_other (r := Reg.r10) h16w (by decide), read_d_of_other (r := Reg.r10) h15w (by decide), read_d_of_other (r := Reg.r10) h14w (by decide), read_d_of_other (r := Reg.r10) h13w (by decide), read_d_of_other (r := Reg.r10) h12w (by decide), read_d_of_other (r := Reg.r10) h11w (by decide), read_d_of_other (r := Reg.r10) h10w (by decide), read_d_of_other (r := Reg.r10) h9w (by decide), read_d_of_other (r := Reg.r10) h8w (by decide), read_d_of_other (r := Reg.r10) h7w (by decide), read_d_of_other (r := Reg.r10) h6w (by decide), read_d_of_other (r := Reg.r10) h5w (by decide), read_d_of_other (r := Reg.r10) h4w (by decide), read_d_of_other (r := Reg.r10) h3w (by decide), read_d_of_other (r := Reg.r10) h2w (by decide), v1]
    try rfl
  have g_r9 : read32 c48.core Reg.r9 = F := by
    rw [read32_of_sameRegs h48regs, read32_of_sameRegs h47regs, read_d_of_other (r := Reg.r9) h46w (by decide), read_d_of_other (r := Reg.r9) h45w (by decide), read_d_of_other (r := Reg.r9) h44w (by decide), read_d_of_other (r := Reg.r9) h43w (by decide), read_d_of_other (r := Reg.r9) h42w (by decide), read_d_of_other (r := Reg.r9) h41w (by decide), read_d_of_other (r := Reg.r9) h40w (by decide), read_d_of_other (r := Reg.r9) h39w (by decide), read_d_of_other (r := Reg.r9) h38w (by decide), read_d_of_other (r := Reg.r9) h37w (by decide), read_d_of_other (r := Reg.r9) h36w (by decide), read_d_of_other (r := Reg.r9) h35w (by decide), read_d_of_other (r := Reg.r9) h34w (by decide), read_d_of_other (r := Reg.r9) h33w (by decide), read_d_of_other (r := Reg.r9) h32w (by decide), read_d_of_other (r := Reg.r9) h31w (by decide), read_d_of_other (r := Reg.r9) h30w (by decide), read_d_of_other (r := Reg.r9) h29w (by decide), read_d_of_other (r := Reg.r9) h28w (by decide), read_d_of_other (r := Reg.r9) h27w (by decide), read_d_of_other (r := Reg.r9) h26w (by decide), read_d_of_other (r := Reg.r9) h25w (by decide), read_d_of_other (r := Reg.r9) h24w (by decide), read_d_of_other (r := Reg.r9) h23w (by decide), read_d_of_other (r := Reg.r9) h22w (by decide), read_d_of_other (r := Reg.r9) h21w (by decide), read_d_of_other (r := Reg.r9) h20w (by decide), read_d_of_other (r := Reg.r9) h19w (by decide), read_d_of_other (r := Reg.r9) h18w (by decide), read_d_of_other (r := Reg.r9) h17w (by decide), read_d_of_other (r := Reg.r9) h16w (by decide), read_d_of_other (r := Reg.r9) h15w (by decide), read_d_of_other (r := Reg.r9) h14w (by decide), read_d_of_other (r := Reg.r9) h13w (by decide), read_d_of_other (r := Reg.r9) h12w (by decide), read_d_of_other (r := Reg.r9) h11w (by decide), read_d_of_other (r := Reg.r9) h10w (by decide), read_d_of_other (r := Reg.r9) h9w (by decide), read_d_of_other (r := Reg.r9) h8w (by decide), read_d_of_other (r := Reg.r9) h7w (by decide), read_d_of_other (r := Reg.r9) h6w (by decide), read_d_of_other (r := Reg.r9) h5w (by decide), read_d_of_other (r := Reg.r9) h4w (by decide), read_d_of_other (r := Reg.r9) h3w (by decide), v2]
    try rfl
  have g_rbx : read32 c48.core Reg.rbx = G := by
    rw [read32_of_sameRegs h48regs, read32_of_sameRegs h47regs, read_d_of_other (r := Reg.rbx) h46w (by decide), read_d_of_other (r := Reg.rbx) h45w (by decide), read_d_of_other (r := Reg.rbx) h44w (by decide), read_d_of_other (r := Reg.rbx) h43w (by decide), read_d_of_other (r := Reg.rbx) h42w (by decide), read_d_of_other (r := Reg.rbx) h41w (by decide), read_d_of_other (r := Reg.rbx) h40w (by decide), read_d_of_other (r := Reg.rbx) h39w (by decide), read_d_of_other (r := Reg.rbx) h38w (by decide), read_d_of_other (r := Reg.rbx) h37w (by decide), read_d_of_other (r := Reg.rbx) h36w (by decide), read_d_of_other (r := Reg.rbx) h35w (by decide), read_d_of_other (r := Reg.rbx) h34w (by decide), read_d_of_other (r := Reg.rbx) h33w (by decide), read_d_of_other (r := Reg.rbx) h32w (by decide), read_d_of_other (r := Reg.rbx) h31w (by decide), read_d_of_other (r := Reg.rbx) h30w (by decide), read_d_of_other (r := Reg.rbx) h29w (by decide), read_d_of_other (r := Reg.rbx) h28w (by decide), read_d_of_other (r := Reg.rbx) h27w (by decide), read_d_of_other (r := Reg.rbx) h26w (by decide), read_d_of_other (r := Reg.rbx) h25w (by decide), read_d_of_other (r := Reg.rbx) h24w (by decide), read_d_of_other (r := Reg.rbx) h23w (by decide), read_d_of_other (r := Reg.rbx) h22w (by decide), read_d_of_other (r := Reg.rbx) h21w (by decide), read_d_of_other (r := Reg.rbx) h20w (by decide), read_d_of_other (r := Reg.rbx) h19w (by decide), read_d_of_other (r := Reg.rbx) h18w (by decide), read_d_of_other (r := Reg.rbx) h17w (by decide), read_d_of_other (r := Reg.rbx) h16w (by decide), read_d_of_other (r := Reg.rbx) h15w (by decide), read_d_of_other (r := Reg.rbx) h14w (by decide), read_d_of_other (r := Reg.rbx) h13w (by decide), read_d_of_other (r := Reg.rbx) h12w (by decide), read_d_of_other (r := Reg.rbx) h11w (by decide), read_d_of_other (r := Reg.rbx) h10w (by decide), read_d_of_other (r := Reg.rbx) h9w (by decide), read_d_of_other (r := Reg.rbx) h8w (by decide), read_d_of_other (r := Reg.rbx) h7w (by decide), read_d_of_other (r := Reg.rbx) h6w (by decide), read_d_of_other (r := Reg.rbx) h5w (by decide), read_d_of_other (r := Reg.rbx) h4w (by decide), v3]
    try rfl
  have halias : read32 c48.core Reg.r10 = read32 c48.core Reg.rsi ∧
      read32 c48.core Reg.r9 = read32 c48.core Reg.rbp ∧
      read32 c48.core Reg.rbx = read32 c48.core Reg.r14 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [g_r10, read32_of_sameRegs h48regs, read32_of_sameRegs h47regs, f_rsi]
    · rw [g_r9, read32_of_sameRegs h48regs, read32_of_sameRegs h47regs, f_rbp]
    · rw [g_rbx, read32_of_sameRegs h48regs, read32_of_sameRegs h47regs, f_r14]
  refine ⟨c48, Reaches.cons s1 (Reaches.cons s2 (Reaches.cons s3 (Reaches.cons s4 (Reaches.cons s5 (Reaches.cons s6 (Reaches.cons s7 (Reaches.cons s8 (Reaches.cons s9 (Reaches.cons s10 (Reaches.cons s11 (Reaches.cons s12 (Reaches.cons s13 (Reaches.cons s14 (Reaches.cons s15 (Reaches.cons s16 (Reaches.cons s17 (Reaches.cons s18 (Reaches.cons s19 (Reaches.cons s20 (Reaches.cons s21 (Reaches.cons s22 (Reaches.cons s23 (Reaches.cons s24 (Reaches.cons s25 (Reaches.cons s26 (Reaches.cons s27 (Reaches.cons s28 (Reaches.cons s29 (Reaches.cons s30 (Reaches.cons s31 (Reaches.cons s32 (Reaches.cons s33 (Reaches.cons s34 (Reaches.cons s35 (Reaches.cons s36 (Reaches.cons s37 (Reaches.cons s38 (Reaches.cons s39 (Reaches.cons s40 (Reaches.cons s41 (Reaches.cons s42 (Reaches.cons s43 (Reaches.cons s44 (Reaches.cons s45 (Reaches.cons s46 (Reaches.cons s47 (Reaches.one s48))))))))))))))))))))))))))))))))))))))))))))))), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h48rip
  · rw [h48regs _, h47regs _]; exact a46.rax
  · rw [h48regs _, h47regs _]; exact a46.rcx
  · rw [h48regs _, h47regs _, a46.rsp]; exact a0.rsp.symm
  · rw [h48regs _, h47regs _, a46.rdi]; exact a0.rdi.symm
  · rw [h48mem, h47mem]; exact a46.mem
  · refine ⟨?_, halias⟩
    show (read32 c48.core Reg.r12, _, _, _, _, _, _, _) = _
    simp only [read32_of_sameRegs h48regs, read32_of_sameRegs h47regs]
    simp only [← hA, ← hB, ← hC, ← hD, ← hE, ← hF, ← hG, ← hH] at hround
    exact hround


/-- The sixty-four words of `sha256_compress.K` read. Unlike `block[]` and
`state[]` this comes **free** from the contract, because `SysVEntry.kTable`
pins the `.rodata` *contents* rather than only its backing: the witness is
known, so no general `readBytes → HoldsLE` bridge is needed. -/
def KWordsHold (memory : Memory) (kBase : Word) : Prop :=
  ∀ j, j < 64 → ∃ v : Word, Silmaril.X86.Ext.HoldsLE memory (kBase.toNat + 4 * j) 4 v

/-- **The L3 trace**, at the real image. -/
theorem l3_trace {cur : MState} {t : Nat} {kBase : Word} (ht : t < 64)
    (hfits : (344 : Nat) ≤ rspEntry.toNat)
    (hknw : kBase.toNat + 256 ≤ 2 ^ 64)
    (hat : L3At L rspEntry kBase state 224 t cur cur)
    (hloaded : Loaded cur.memory L.textBase (image L.textBase L.rodataBase))
    {kv wv : Word}
    (hkv : Silmaril.X86.Ext.HoldsLE cur.memory (kBase.toNat + 4 * t) 4 kv)
    (hwv : Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 312 + 4 * t) 4 wv) :
    ∃ cur', Reaches L.exit cur cur' ∧ L3Effect L rspEntry kBase t cur cur' ∧
      RoundOut cur cur' kv wv := by
  have hsl : ∀ o l : Nat, relocOffset + 4 ≤ o →
      ((image L.textBase L.rodataBase).drop o).take l = (raw.drop o).take l :=
    fun o l hb => image_slice_above _ _ hb
  exact l3_trace_img ht (image_length L.textBase L.rodataBase) hfits hknw
    (by rw [hsl 224 3 (by decide)]; exact l3_decode_224)
    (by rw [hsl 227 3 (by decide)]; exact l3_decode_227)
    (by rw [hsl 230 2 (by decide)]; exact l3_decode_230)
    (by rw [hsl 232 3 (by decide)]; exact l3_decode_232)
    (by rw [hsl 235 3 (by decide)]; exact l3_decode_235)
    (by rw [hsl 238 3 (by decide)]; exact l3_decode_238)
    (by rw [hsl 241 3 (by decide)]; exact l3_decode_241)
    (by rw [hsl 244 3 (by decide)]; exact l3_decode_244)
    (by rw [hsl 247 3 (by decide)]; exact l3_decode_247)
    (by rw [hsl 250 3 (by decide)]; exact l3_decode_250)
    (by rw [hsl 253 2 (by decide)]; exact l3_decode_253)
    (by rw [hsl 255 3 (by decide)]; exact l3_decode_255)
    (by rw [hsl 258 3 (by decide)]; exact l3_decode_258)
    (by rw [hsl 261 2 (by decide)]; exact l3_decode_261)
    (by rw [hsl 263 3 (by decide)]; exact l3_decode_263)
    (by rw [hsl 266 3 (by decide)]; exact l3_decode_266)
    (by rw [hsl 269 3 (by decide)]; exact l3_decode_269)
    (by rw [hsl 272 3 (by decide)]; exact l3_decode_272)
    (by rw [hsl 275 3 (by decide)]; exact l3_decode_275)
    (by rw [hsl 278 3 (by decide)]; exact l3_decode_278)
    (by rw [hsl 281 3 (by decide)]; exact l3_decode_281)
    (by rw [hsl 284 3 (by decide)]; exact l3_decode_284)
    (by rw [hsl 287 4 (by decide)]; exact l3_decode_287)
    (by rw [hsl 291 5 (by decide)]; exact l3_decode_291)
    (by rw [hsl 296 3 (by decide)]; exact l3_decode_296)
    (by rw [hsl 299 3 (by decide)]; exact l3_decode_299)
    (by rw [hsl 302 3 (by decide)]; exact l3_decode_302)
    (by rw [hsl 305 3 (by decide)]; exact l3_decode_305)
    (by rw [hsl 308 3 (by decide)]; exact l3_decode_308)
    (by rw [hsl 311 3 (by decide)]; exact l3_decode_311)
    (by rw [hsl 314 4 (by decide)]; exact l3_decode_314)
    (by rw [hsl 318 2 (by decide)]; exact l3_decode_318)
    (by rw [hsl 320 3 (by decide)]; exact l3_decode_320)
    (by rw [hsl 323 2 (by decide)]; exact l3_decode_323)
    (by rw [hsl 325 3 (by decide)]; exact l3_decode_325)
    (by rw [hsl 328 3 (by decide)]; exact l3_decode_328)
    (by rw [hsl 331 3 (by decide)]; exact l3_decode_331)
    (by rw [hsl 334 3 (by decide)]; exact l3_decode_334)
    (by rw [hsl 337 3 (by decide)]; exact l3_decode_337)
    (by rw [hsl 340 3 (by decide)]; exact l3_decode_340)
    (by rw [hsl 343 3 (by decide)]; exact l3_decode_343)
    (by rw [hsl 346 3 (by decide)]; exact l3_decode_346)
    (by rw [hsl 349 4 (by decide)]; exact l3_decode_349)
    (by rw [hsl 353 3 (by decide)]; exact l3_decode_353)
    (by rw [hsl 356 3 (by decide)]; exact l3_decode_356)
    (by rw [hsl 359 3 (by decide)]; exact l3_decode_359)
    (by rw [hsl 362 6 (by decide)]; exact l3_decode_362)
    (by rw [hsl 368 6 (by decide)]; exact l3_decode_368)
    hat hloaded hkv hwv

/-- The **weak** L3 invariant after `t` rounds. L3 writes no memory, so the
whole invariant is where the machine is: everything else is inherited from
`base` through `L3At.mem`. -/
structure L3Inv (L : Layout) (rspEntry kBase st : Word) (base : MState) (t : Nat)
    (cur : MState) : Prop where
  /-- The counter has not run past the trip count. -/
  bound : t ≤ 64
  /-- Where the machine is; `rip` is a function of the index because the loop
  is bottom-tested. -/
  at_ : L3At L rspEntry kBase st (if t < 64 then 224 else 374) t base cur

/-- **L3 closes under the weak invariant.** -/
theorem l3_loop {base : MState} {kBase : Word}
    (hfits : (344 : Nat) ≤ rspEntry.toNat)
    (hknw : kBase.toNat + 256 ≤ 2 ^ 64)
    (hloaded : Loaded base.memory L.textBase (image L.textBase L.rodataBase))
    (hk : KWordsHold base.memory kBase)
    (hw : WWordsRead base.memory rspEntry 64)
    {cur : MState} (start : L3Inv L rspEntry kBase state base 0 cur) :
    ∃ fin, Reaches L.exit cur fin ∧ L3Inv L rspEntry kBase state base 64 fin := by
  refine Silmaril.X86.Ext.reaches_loop_of_trace
    (I := L3Inv L rspEntry kBase state base)
    (Q := L3Inv L rspEntry kBase state base 64)
    (Pre := fun t c => L3At L rspEntry kBase state 224 t base c)
    (Effect := fun t c c' => L3Effect L rspEntry kBase t c c')
    (N := 64) ?_ ?_ ?_ ?_ start
  · intro t ht c inv
    have hat := inv.at_
    rwa [show (if t < 64 then (224 : Nat) else 374) = 224 from
      ite_eq_left_of_eq_true _ _ (eq_true ht)] at hat
  · intro t ht c hpre
    obtain ⟨kvv, hkvv⟩ := hk t ht
    obtain ⟨wvv, hwvv⟩ := hw t ht
    obtain ⟨c', r, eff, _⟩ := l3_trace (state := state) ht hfits hknw
      { rip := hpre.rip, rax := hpre.rax, rcx := hpre.rcx, rsp := hpre.rsp,
        rdi := hpre.rdi, mem := rfl }
      (hpre.mem ▸ hloaded) (by rw [hpre.mem]; exact hkvv) (by rw [hpre.mem]; exact hwvv)
    exact ⟨c', r, eff⟩
  · intro t ht c c' inv eff
    exact { bound := by omega
            at_ := { rip := eff.rip, rax := eff.rax, rcx := eff.rcx
                     rsp := by rw [eff.rsp]; exact inv.at_.rsp
                     rdi := by rw [eff.rdi]; exact inv.at_.rdi
                     mem := by rw [eff.mem]; exact inv.at_.mem } }
  · intro c inv
    exact ⟨c, Silmaril.X86.Ext.Reaches.of_runs (Silmaril.X86.Ext.Runs.nil c), inv⟩

set_option maxRecDepth 8000 in
/-- **L3 computes sixty-four rounds.** The weak loop, conjoined with the round
state after `t` rounds of an **arbitrary** schedule `W`.

`W` is a parameter, not `block[]`'s schedule: L3 reads `w[t]` and never looks
at it, so what the rounds compute is settled without knowing which words the
slots hold. That is why L2 and L3 are independent, and why this theorem ports
to any image whose round loop has the same shape.

`K[t]` enters already named as `Ks.getD t 0`, which `SysVEntry.kTable` gives
for free — the contract pins the table's contents, so the constant is known
rather than merely readable. -/
theorem l3_loop_at {base : MState} {kBase : Word} {W : Nat → SHA256.Kernel.Word}
    {st0 : SHA256.Kernel.State}
    (hfits : (344 : Nat) ≤ rspEntry.toNat)
    (hknw : kBase.toNat + 256 ≤ 2 ^ 64)
    (hloaded : Loaded base.memory L.textBase (image L.textBase L.rodataBase))
    (hkw : ∀ j, j < 64 → Silmaril.X86.Ext.HoldsLE base.memory (kBase.toNat + 4 * j) 4
      ((SHA256.Kernel.Ks.getD j 0).setWidth 64))
    (hww : WWordsAt base.memory rspEntry (fun j => (W j).setWidth 64) 64)
    {cur : MState} (start : L3Inv L rspEntry kBase state base 0 cur)
    (hstart : RoundState st0 cur) :
    ∃ fin, Reaches L.exit cur fin ∧ L3Inv L rspEntry kBase state base 64 fin ∧
      RoundState (SHA256.Kernel.roundsUpTo W st0 64) fin ∧ RoundAlias fin := by
  refine Silmaril.X86.Ext.reaches_loop_of_trace
    (I := fun t c => L3Inv L rspEntry kBase state base t c ∧
      RoundState (SHA256.Kernel.roundsUpTo W st0 t) c ∧ (0 < t → RoundAlias c))
    (Q := fun c => L3Inv L rspEntry kBase state base 64 c ∧
      RoundState (SHA256.Kernel.roundsUpTo W st0 64) c ∧ RoundAlias c)
    (Pre := fun t c => L3At L rspEntry kBase state 224 t base c ∧
      RoundState (SHA256.Kernel.roundsUpTo W st0 t) c)
    (Effect := fun t c c' => L3Effect L rspEntry kBase t c c' ∧
      RoundOut c c' ((SHA256.Kernel.Ks.getD t 0).setWidth 64) ((W t).setWidth 64))
    (N := 64) ?_ ?_ ?_ ?_ ⟨start, by rw [SHA256.Kernel.roundsUpTo_zero]; exact hstart,
      fun hc => absurd hc (by omega)⟩
  · intro t ht c inv
    refine ⟨?_, inv.2.1⟩
    have hat := inv.1.at_
    rwa [show (if t < 64 then (224 : Nat) else 374) = 224 from
      ite_eq_left_of_eq_true _ _ (eq_true ht)] at hat
  · intro t ht c hpre
    exact l3_trace (state := state) ht hfits hknw
      { rip := hpre.1.rip, rax := hpre.1.rax, rcx := hpre.1.rcx, rsp := hpre.1.rsp,
        rdi := hpre.1.rdi, mem := rfl }
      (hpre.1.mem ▸ hloaded)
      (by rw [hpre.1.mem]; exact hkw t ht) (by rw [hpre.1.mem]; exact hww t ht)
  · intro t ht c c' inv eff
    refine ⟨{ bound := by omega
              at_ := { rip := eff.1.rip, rax := eff.1.rax, rcx := eff.1.rcx
                       rsp := by rw [eff.1.rsp]; exact inv.1.at_.rsp
                       rdi := by rw [eff.1.rdi]; exact inv.1.at_.rdi
                       mem := by rw [eff.1.mem]; exact inv.1.at_.mem } }, ?_, fun _ => eff.2.2⟩
    show SHA256.Kernel.roundsUpTo W st0 (t + 1) = _
    rw [SHA256.Kernel.roundsUpTo_succ, inv.2.1]
    have hro := eff.2
    simp only [RoundOut, trunc32] at hro
    exact hro.1.symm
  · intro c inv
    exact ⟨c, Silmaril.X86.Ext.Reaches.of_runs (Silmaril.X86.Ext.Runs.nil c),
      inv.1, inv.2.1, inv.2.2 (by omega)⟩

/-- **Invariant preservation for L2.** Consumes `L2Effect` and says nothing
about how the iteration ran, so strengthening to the schedule extends this and
leaves `l2_trace` untouched. -/
theorem l2_preserve (h : SysVEntry L state block rspEntry frameSize m)
    {i : Nat} (hi : i < 48) {cur cur' : MState}
    (inv : L2Inv L state rspEntry m i cur)
    (eff : L2Effect L rspEntry i cur cur') :
    L2Inv L state rspEntry m (i + 1) cur' := by
  obtain ⟨sv, hst⟩ := eff.stored
  have hbs : (Silmaril.X86.Ext.leBytes sv 4).length = 4 :=
    Silmaril.X86.Ext.length_leBytes _ _
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hlow : rspEntry.toNat - 344 ≤ rspEntry.toNat - 312 + 4 * (16 + i) := by omega
  have hhigh : rspEntry.toNat - 312 + 4 * (16 + i) + 4 ≤ rspEntry.toNat := by omega
  refine { bound := by omega, at_ := ?_, frame := ?_, words := ?_, saved := ?_, stwords := ?_ }
  · exact { rip := eff.rip
            rax := eff.rax
            rsp := by rw [eff.rsp]; exact inv.at_.rsp
            rdi := by rw [eff.rdi]; exact inv.at_.rdi
            loaded := Silmaril.X86.Ext.Loaded.of_stored inv.at_.loaded hst
              (by rw [hbs, image_length]; exact h.store_disjoint_code hlow hhigh) }
  · exact Silmaril.Process.Memory.WritesWithin.step inv.frame hst (by
      intro offset hoff
      rw [hbs] at hoff
      exact frame_in_footprint (by rw [frameExtent_eq]; omega) (by omega) (by omega))
  · have := WWordsRead.succ (t := 16 + i) (by omega) inv.words hst (by
      rw [Silmaril.Process.Memory.WritesWithin.permitted_iff inv.frame]
      exact h.frame_readable (by omega) hlow hhigh)
    exact this
  · exact SavedSlotsAt.store inv.saved hst hbs hfits (by omega)
  · have hd2 := h.state_disjoint_frame
    simp only [stateRegion, frameRegion, Region.Disjoint, frameFloor_eq, frameExtent_eq] at hd2
    intro j hj
    obtain ⟨w, hw⟩ := inv.stwords j hj
    exact ⟨w, Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst hw (by rw [hbs]; omega)⟩

/-- **L2 closes under the weak invariant**, modulo `l2_trace`. -/
theorem l2_loop (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} (start : L2Inv L state rspEntry m 0 cur) :
    ∃ fin, Reaches L.exit cur fin ∧ L2Inv L state rspEntry m 48 fin := by
  refine Silmaril.X86.Ext.reaches_loop_of_trace
    (I := L2Inv L state rspEntry m)
    (Q := L2Inv L state rspEntry m 48)
    (Pre := fun i c => L2At L rspEntry state (image L.textBase L.rodataBase) 64
        (BitVec.ofNat 64 (16 + i)) c ∧ WWordsRead c.memory rspEntry (16 + i) ∧
        c.memory.Permitted .write (rspEntry.toNat - 312 + 4 * (16 + i)) 4)
    (Effect := fun i c c' => L2Effect L rspEntry i c c')
    (N := 48) ?_ ?_ ?_ ?_ start
  · intro i hi c inv
    have hfits : (344 : Nat) ≤ rspEntry.toNat := by
      have := h.frameFits; rwa [frameExtent_eq] at this
    refine ⟨?_, inv.words, ?_⟩
    · have hat := inv.at_
      rwa [show (if i < 48 then (64 : Nat) else 150) = 64 from
        ite_eq_left_of_eq_true _ _ (eq_true hi)] at hat
    · rw [Silmaril.Process.Memory.WritesWithin.permitted_iff inv.frame]
      exact h.frame_writable (by omega) (by omega) (by omega)
  · intro i hi c pre
    exact l2_trace_weak h hi pre.1 pre.2.1 pre.2.2
  · intro i hi c c' inv eff
    exact l2_preserve h hi inv eff
  · intro c inv
    exact ⟨c, Silmaril.X86.Ext.Reaches.of_runs (Silmaril.X86.Ext.Runs.nil c), inv⟩

set_option maxRecDepth 8000 in
/-- **L2 computes the message schedule.** From the sixteen words L1 wrote, the
loop fills `w[16 … 64)` with the schedule recurrence.

`W` is a parameter constrained only by `hsched`, the recurrence itself; the
loop never mentions `messageSchedule`. The caller instantiates it, which is
where the schedule bridge enters and the only place it is needed.

The carried `%edx` is one conjunct, `read32 c.core .rdx = W i`. It steps
because the iteration ends `mov %ecx,%edx` with `%ecx = w[t-15] = w[(t+1)-16]`
— the next iteration's carried word. That is the whole of the software
pipelining, and it is invisible to the weak invariant because reading a
register cannot fault. -/
theorem l2_loop_at (h : SysVEntry L state block rspEntry frameSize m)
    {W : Nat → SHA256.Kernel.Word}
    (hsched : ∀ j, 16 ≤ j → j < 64 →
      W j = SHA256.Kernel.sigma1 (W (j - 2)) + W (j - 7)
              + SHA256.Kernel.sigma0 (W (j - 15)) + W (j - 16))
    {sv : Nat → SHA256.Kernel.Word}
    {cur : MState} (start : L2Inv L state rspEntry m 0 cur)
    (hw0 : WWordsAt cur.memory rspEntry (fun j => (W j).setWidth 64) 16)
    (hdx : read32 cur.core .rdx = W 0) (hsw : StateWordsAt cur.memory state sv) :
    ∃ fin, Reaches L.exit cur fin ∧ L2Inv L state rspEntry m 48 fin ∧
      WWordsAt fin.memory rspEntry (fun j => (W j).setWidth 64) 64 ∧
      StateWordsAt fin.memory state sv := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  refine Silmaril.X86.Ext.reaches_loop_of_trace
    (I := fun i c => L2Inv L state rspEntry m i c ∧
      WWordsAt c.memory rspEntry (fun j => (W j).setWidth 64) (16 + i) ∧
      read32 c.core .rdx = W i ∧ StateWordsAt c.memory state sv)
    (Q := fun c => L2Inv L state rspEntry m 48 c ∧
      WWordsAt c.memory rspEntry (fun j => (W j).setWidth 64) 64 ∧
      StateWordsAt c.memory state sv)
    (Pre := fun i c => L2At L rspEntry state (image L.textBase L.rodataBase) 64
        (BitVec.ofNat 64 (16 + i)) c ∧
        WWordsAt c.memory rspEntry (fun j => (W j).setWidth 64) (16 + i) ∧
        c.memory.Permitted .write (rspEntry.toNat - 312 + 4 * (16 + i)) 4 ∧
        read32 c.core .rdx = W i)
    (Effect := fun i c c' => L2Effect L rspEntry i c c' ∧ ScheduleOut rspEntry W i c c')
    (N := 48) ?_ ?_ ?_ ?_ ⟨start, hw0, hdx, hsw⟩
  · intro i hi c inv
    refine ⟨?_, inv.2.1, ?_, inv.2.2.1⟩
    · have hat := inv.1.at_
      rwa [show (if i < 48 then (64 : Nat) else 150) = 64 from
        ite_eq_left_of_eq_true _ _ (eq_true hi)] at hat
    · rw [Silmaril.Process.Memory.WritesWithin.permitted_iff inv.1.frame]
      exact h.frame_writable (by omega) (by omega) (by omega)
  · intro i hi c pre
    exact l2_trace h hi pre.1 pre.2.1 pre.2.2.1
  · intro i hi c c' inv eff
    refine ⟨l2_preserve h hi inv.1 eff.1, ?_, ?_, ?_⟩
    · have hstore := eff.2.2
      rw [inv.2.2.1] at hstore
      have hw : SHA256.Kernel.sigma1 (W (16 + i - 2)) + W (16 + i - 7)
          + SHA256.Kernel.sigma0 (W (16 + i - 15)) + W i = W (16 + i) := by
        rw [hsched (16 + i) (by omega) (by omega), show 16 + i - 16 = i from by omega]
      rw [hw] at hstore
      have hnext := WWordsAt.succ (t := 16 + i) (by omega) inv.2.1 hstore ?_
      · exact hnext
      · rw [Silmaril.Process.Memory.WritesWithin.permitted_iff inv.1.frame]
        exact h.frame_readable (by omega) (by omega) (by omega)
    · rw [eff.2.1, show 16 + i - 15 = i + 1 from by omega]
    · obtain ⟨sval, hst⟩ := eff.1.stored
      have hbs2 : (Silmaril.X86.Ext.leBytes sval 4).length = 4 :=
        Silmaril.X86.Ext.length_leBytes _ _
      have hd2 := h.state_disjoint_frame
      simp only [stateRegion, frameRegion, Region.Disjoint, frameFloor_eq,
        frameExtent_eq] at hd2
      intro j hj
      exact Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hst (inv.2.2.2 j hj)
        (by rw [hbs2]; omega)
  · intro c inv
    exact ⟨c, Silmaril.X86.Ext.Reaches.of_runs (Silmaril.X86.Ext.Runs.nil c),
      inv.1, inv.2.1, inv.2.2.2⟩

/-! ## Liveness

The composition: `prologue → blockA0 → L1 → blockA → L2 → blockB → L3 →
blockC → epilogue`. Every piece is proved above; this threads them. -/

set_option maxRecDepth 8000 in
/-- From a System V entry state, control reaches L1's head with the counter
zeroed and every fact the loop invariant needs. -/
theorem live_to_l1 (h : SysVEntry L state block rspEntry frameSize m) :
    ∃ mid, Reaches L.exit m mid ∧ L1Inv L state block rspEntry m 0 mid := by
  obtain ⟨sb, hsb⟩ := h.stateReads
  obtain ⟨m1, r1, p1⟩ := prologue h hsb
  obtain ⟨m2, r2, a2, e2⟩ := blockA0 (by rw [p1.regs .rsi (by decide)]; exact h.argBlock)
    (by rw [p1.regs .rdi (by decide)]; exact h.argState) p1
  refine ⟨m2, r1.trans r2, ?_⟩
  refine { bound := by omega, at_ := ?_, frame := ?_, reads := ?_, words := ?_, saved := ?_, stwords := ?_ }
  · simpa using a2
  · rw [e2]; exact p1.frame
  · intro j hj; rw [e2]; exact p1.blwords j hj
  · intro j hj; omega
  · intro j hj; rw [e2]; exact p1.pushed j hj (by simp only [frameSize]; omega)
  · intro j hj; rw [e2]; exact ⟨_, p1.stwords j hj⟩

set_option maxRecDepth 8000 in
/-- L1's exit, through block `50 … 64`, to L2's entry invariant. -/
theorem live_to_l2 (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} (hs : L1Inv L state block rspEntry m 16 cur) :
    ∃ mid, Reaches L.exit cur mid ∧ L2Inv L state rspEntry m 0 mid := by
  classical
  obtain ⟨v, hv⟩ := hs.words 0 (by omega)
  obtain ⟨m2, r2, a2, e2, _⟩ := blockA h hs (W := fun _ => v.setWidth 32) hv.norm32
  refine ⟨m2, r2, ?_⟩
  refine { bound := by omega, at_ := ?_, frame := ?_, words := ?_, saved := ?_, stwords := ?_ }
  · simpa using a2
  · rw [e2]; exact hs.frame
  · intro j hj; rw [e2]; exact hs.words j hj
  · intro j hj; rw [e2]; exact hs.saved j hj
  · intro j hj; rw [e2]; exact hs.stwords j hj

/-- **The entry, pinned.** The prologue and block `10 … 32`, carrying the
caller's `state[]` words forward. -/
theorem live_to_l1_at (h : SysVEntry L state block rspEntry frameSize m)
    {sb : List Silmaril.Process.Byte} (hsb : m.memory.readBytes state.toNat 32 = some sb) :
    ∃ mid, Reaches L.exit m mid ∧ L1Inv L state block rspEntry m 0 mid ∧
      StateWordsAt mid.memory state (fun j => leWordAt sb j) := by
  obtain ⟨m1, r1, p1⟩ := prologue h hsb
  obtain ⟨m2, r2, a2, e2⟩ := blockA0 (by rw [p1.regs .rsi (by decide)]; exact h.argBlock)
    (by rw [p1.regs .rdi (by decide)]; exact h.argState) p1
  refine ⟨m2, r1.trans r2, ?_, ?_⟩
  · refine { bound := by omega, at_ := ?_, frame := ?_, reads := ?_, words := ?_,
             saved := ?_, stwords := ?_ }
    · simpa using a2
    · rw [e2]; exact p1.frame
    · intro j hj; rw [e2]; exact p1.blwords j hj
    · intro j hj; omega
    · intro j hj; rw [e2]; exact p1.pushed j hj (by simp only [frameSize]; omega)
    · intro j hj; rw [e2]; exact ⟨_, p1.stwords j hj⟩
  · intro j hj; rw [e2]; exact p1.stwords j hj

/-- **The L1 → L2 join, pinned.** Carries L1's sixteen words across block
`50 … 64` and supplies the schedule loop's carried register from the `w[0]`
preload at offset 55.

No slot-value uniqueness is needed: the preload is given the *pinned* fact
directly rather than an arbitrary witness, so there are never two facts about
`w[0]` to identify. Pinning at the source is cheaper than reconciling
afterwards. -/
theorem live_to_l2_at (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} (hs : L1Inv L state block rspEntry m 16 cur)
    {W sv : Nat → SHA256.Kernel.Word}
    (hww : WWordsAt cur.memory rspEntry (fun j => (W j).setWidth 64) 16)
    (hsw : StateWordsAt cur.memory state sv) :
    ∃ mid, Reaches L.exit cur mid ∧ L2Inv L state rspEntry m 0 mid ∧
      WWordsAt mid.memory rspEntry (fun j => (W j).setWidth 64) 16 ∧
      read32 mid.core .rdx = W 0 ∧ StateWordsAt mid.memory state sv := by
  obtain ⟨m2, r2, a2, e2, hdx⟩ := blockA h hs (hww 0 (by omega))
  refine ⟨m2, r2, ?_, ?_, hdx, ?_⟩
  · refine { bound := by omega, at_ := ?_, frame := ?_, words := ?_, saved := ?_,
             stwords := ?_ }
    · simpa using a2
    · rw [e2]; exact hs.frame
    · intro j hj; rw [e2]; exact hs.words j hj
    · intro j hj; rw [e2]; exact hs.saved j hj
    · intro j hj; rw [e2]; exact hs.stwords j hj
  · intro j hj; rw [e2]; exact hww j hj
  · intro j hj; rw [e2]; exact hsw j hj

/-- `state[]` and the `K` table are disjoint. -/
theorem SysVEntry.state_disjoint_kTable (h : SysVEntry L state block rspEntry frameSize m) :
    Region.Disjoint (stateRegion state) (kTableRegion L) := by
  have hp := h.disjoint
  simp only [regions, List.pairwise_cons, List.mem_cons] at hp
  exact hp.1 _ (by simp)

/-- The `K` table and the callee's stack are disjoint. -/
theorem SysVEntry.kTable_disjoint_frame (h : SysVEntry L state block rspEntry frameSize m) :
    Region.Disjoint (kTableRegion L) (frameRegion rspEntry frameSize) := by
  have hp := h.disjoint
  simp only [regions, List.pairwise_cons, List.mem_cons] at hp
  exact hp.2.2.2.1 _ (by simp)

/-- The sixty-four `K` words read, straight from the contract's `kTable`
clause — which pins *contents*, so the `HoldsLE` witness is known and the
general bridge is not even needed here. -/
theorem kWordsHold_of_kTable (h : SysVEntry L state block rspEntry frameSize m) :
    KWordsHold m.memory L.rodataBase := by
  intro j hj
  exact ⟨_, Silmaril.X86.Ext.holdsLE_of_readBytes
    (Silmaril.X86.Ext.readWith_sub (access := .read) h.kTable (offset := 4 * j) (len := 4)
      (by omega) (by simp only [kSize]; omega)) (by omega)⟩

/-- `.rodata` is outside the footprint, so the `K` words survive the whole
function. -/
theorem KWordsHold.preserved (h : SysVEntry L state block rspEntry frameSize m)
    {before after : Memory}
    (hw : Memory.WritesWithin before after (Footprint state rspEntry frameSize))
    (hk : KWordsHold before L.rodataBase) : KWordsHold after L.rodataBase := by
  have hfits := h.frameFits
  rw [frameExtent_eq] at hfits
  have hd1 := h.state_disjoint_kTable
  have hd2 := h.kTable_disjoint_frame
  simp only [stateRegion, kTableRegion, frameRegion, Region.Disjoint, frameFloor_eq,
    frameExtent_eq, kSize] at hd1 hd2
  intro j hj
  obtain ⟨v, hv⟩ := hk j hj
  refine ⟨v, ?_⟩
  show after.readBytes _ 4 = _
  rw [Silmaril.Process.Memory.WritesWithin.readBytes hw ?_]
  · exact hv
  · intro o ho
    rintro (⟨hl, hr⟩ | ⟨hl, hr⟩)
    · simp only [stateRegion] at hl hr; omega
    · simp only [frameRegion, frameFloor_eq, frameExtent_eq] at hl hr; omega

/-- **`K[t]` by value, anywhere inside the function.** The table is disjoint
from both halves of the modifies set, so the constant is recovered from the
footprint rather than carried — the same rule as `blockBytes_preserved`. -/
theorem holdsLE_kWord_at (h : SysVEntry L state block rspEntry frameSize m)
    {after : Memory}
    (hw : Memory.WritesWithin m.memory after (Footprint state rspEntry frameSize))
    {t : Nat} (ht : t < 64) :
    Silmaril.X86.Ext.HoldsLE after (L.rodataBase.toNat + 4 * t) 4
      ((SHA256.Kernel.Ks.getD t 0).setWidth 64) := by
  have hfits := h.frameFits
  rw [frameExtent_eq] at hfits
  have hd1 := h.state_disjoint_kTable
  have hd2 := h.kTable_disjoint_frame
  simp only [stateRegion, kTableRegion, frameRegion, Region.Disjoint, frameFloor_eq,
    frameExtent_eq, kSize] at hd1 hd2
  have hv : Silmaril.X86.Ext.HoldsLE m.memory (L.rodataBase.toNat + 4 * t) 4
      ((SHA256.Kernel.Ks.getD t 0).setWidth 64) := by
    rw [← leWordAt_kBytes t ht]; exact holdsLE_kWord h (by omega)
  show after.readBytes _ 4 = _
  rw [Silmaril.Process.Memory.WritesWithin.readBytes hw ?_]
  · exact hv
  · intro o ho
    rintro (⟨hl, hr⟩ | ⟨hl, hr⟩)
    · simp only [stateRegion] at hl hr; omega
    · simp only [frameRegion, frameFloor_eq, frameExtent_eq] at hl hr; omega

set_option maxRecDepth 8000 in
/-- **The L2 → L3 join, pinned.** L2's exit, through block `150 … 224`, the
sixty-four rounds, and into block `374 … 441`, carrying the round state.

This is where `l3_loop_at`'s arbitrary `W` is instantiated — with L2's
schedule, whatever it is. The round loop never needed to know. -/
theorem live_to_blockC_at (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} (hs : L2Inv L state rspEntry m 48 cur)
    {W sv : Nat → SHA256.Kernel.Word}
    (hww : WWordsAt cur.memory rspEntry (fun j => (W j).setWidth 64) 64)
    (hstate : ∀ j, j < 8 → Silmaril.X86.Ext.HoldsLE cur.memory (state.toNat + 4 * j) 4
      ((sv j).setWidth 64)) :
    ∃ mid, Reaches L.exit cur mid ∧ CAt L state rspEntry 374 m mid ∧
      RoundState (SHA256.Kernel.roundsUpTo W
        (sv 0, sv 1, sv 2, sv 3, sv 4, sv 5, sv 6, sv 7) 64) mid ∧ RoundAlias mid ∧
      SpillPin mid.memory rspEntry sv := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hknw : L.rodataBase.toNat + 256 ≤ 2 ^ 64 := by
    have := h.noWrap (kTableRegion L) (by simp [regions])
    simpa [kTableRegion, kSize, Silmaril.Process.addressLimit] using this
  obtain ⟨m3, r3, b3, hrs, hsp⟩ := blockB h (cur := cur)
    { rip := by have := hs.at_.rip; simpa using this
      rdi := hs.at_.rdi, rsp := hs.at_.rsp, mem := rfl }
    hs.at_.loaded (sv := sv) hstate hs.frame (Wv := W) hww hs.saved
  obtain ⟨m4, r4, i4, hrs4, hal4⟩ := l3_loop_at (base := m3) (kBase := L.rodataBase)
    (W := W) (st0 := (sv 0, sv 1, sv 2, sv 3, sv 4, sv 5, sv 6, sv 7))
    hfits hknw b3.loaded
    (fun j hj => holdsLE_kWord_at h b3.frame hj)
    b3.words
    { bound := by omega
      at_ := { rip := by simpa using b3.rip, rax := by simpa using b3.rax,
               rcx := b3.rcx, rsp := b3.rsp, rdi := b3.rdi, mem := rfl } }
    hrs
  have hm : m4.memory = m3.memory := i4.at_.mem
  exact ⟨m4, r3.trans r4,
    { rip := by have := i4.at_.rip; simpa using this
      rdi := i4.at_.rdi, rsp := i4.at_.rsp
      frame := by rw [hm]; exact b3.frame
      spills := by rw [hm]; exact SpillsAt.toSpillSlots hfits b3.spills
      saved := by rw [hm]; exact b3.saved
      loaded := by rw [hm]; exact b3.loaded }, hrs4, hal4, by rw [hm]; exact hsp⟩

set_option maxRecDepth 8000 in
/-- L2's exit, through block `150 … 224`, L3, and into block `374 … 441`. -/
theorem live_to_blockC (h : SysVEntry L state block rspEntry frameSize m)
    {cur : MState} (hs : L2Inv L state rspEntry m 48 cur) :
    ∃ mid, Reaches L.exit cur mid ∧ CAt L state rspEntry 374 m mid := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hknw : L.rodataBase.toNat + 256 ≤ 2 ^ 64 := by
    have := h.noWrap (kTableRegion L) (by simp [regions])
    simpa [kTableRegion, kSize, Silmaril.Process.addressLimit] using this
  -- block 150 … 224
  classical
  have hsv : ∀ j, ∃ v : SHA256.Kernel.Word, j < 8 →
      Silmaril.X86.Ext.HoldsLE cur.memory (state.toNat + 4 * j) 4 (v.setWidth 64) := by
    intro j
    by_cases hj : j < 8
    · obtain ⟨v, hv⟩ := hs.stwords j hj
      exact ⟨v.setWidth 32, fun _ => hv.norm32⟩
    · exact ⟨0, fun hc => absurd hc hj⟩
  choose sv hsvw using hsv
  have hwv : ∀ j, ∃ v : SHA256.Kernel.Word, j < 64 →
      Silmaril.X86.Ext.HoldsLE cur.memory (rspEntry.toNat - 312 + 4 * j) 4 (v.setWidth 64) := by
    intro j
    by_cases hj : j < 64
    · obtain ⟨v, hv⟩ := hs.words j hj
      exact ⟨v.setWidth 32, fun _ => hv.norm32⟩
    · exact ⟨0, fun hc => absurd hc hj⟩
  choose Wv hWv using hwv
  obtain ⟨m3, r3, b3, _, _⟩ := blockB h
    (cur := cur)
    { rip := by have := hs.at_.rip; simpa using this
      rdi := hs.at_.rdi, rsp := hs.at_.rsp, mem := rfl }
    hs.at_.loaded (sv := sv) hsvw hs.frame (Wv := Wv) hWv hs.saved
  -- L3
  obtain ⟨m4, r4, i4⟩ := l3_loop (base := m3) (kBase := L.rodataBase) hfits hknw b3.loaded
    (KWordsHold.preserved h b3.frame (kWordsHold_of_kTable h)) b3.words.weaken
    { bound := by omega
      at_ := { rip := by simpa using b3.rip, rax := by simpa using b3.rax,
               rcx := b3.rcx, rsp := b3.rsp, rdi := b3.rdi, mem := rfl } }
  refine ⟨m4, r3.trans r4, ?_⟩
  have hm : m4.memory = m3.memory := i4.at_.mem
  exact { rip := by have := i4.at_.rip; simpa using this
          rdi := i4.at_.rdi, rsp := i4.at_.rsp
          frame := by rw [hm]; exact b3.frame
          spills := by rw [hm]; exact SpillsAt.toSpillSlots hfits b3.spills
          saved := by rw [hm]; exact b3.saved
          loaded := by rw [hm]; exact b3.loaded }

set_option maxRecDepth 8000 in
/-- `441`: `add $0xa8,%rsp`. -/
theorem epi_decode_441 : decode ((raw.drop 441).take 7)
    = some (.aluI .q .add (.reg .rsp) 0x000000a8#32, 7) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `448`: `pop %rbx`. -/
theorem epi_decode_448 : decode ((raw.drop 448).take 1)
    = some (.pop .rbx, 1) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `449`: `pop %r12`. -/
theorem epi_decode_449 : decode ((raw.drop 449).take 2)
    = some (.pop .r12, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `451`: `pop %r13`. -/
theorem epi_decode_451 : decode ((raw.drop 451).take 2)
    = some (.pop .r13, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `453`: `pop %r14`. -/
theorem epi_decode_453 : decode ((raw.drop 453).take 2)
    = some (.pop .r14, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `455`: `pop %r15`. -/
theorem epi_decode_455 : decode ((raw.drop 455).take 2)
    = some (.pop .r15, 2) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `457`: `pop %rbp`. -/
theorem epi_decode_457 : decode ((raw.drop 457).take 1)
    = some (.pop .rbp, 1) :=
  decode_raw (by decide +kernel)

set_option maxRecDepth 8000 in
/-- `458`: `ret`. -/
theorem epi_decode_458 : decode ((raw.drop 458).take 1)
    = some (Instr.ret, 1) :=
  decode_raw (by decide +kernel)

/-! ## A liveness-only epilogue

`epilogue` proves `Post.rsp` and `Post.saved`, so it needs the slots to hold
the *entry values*. Liveness needs only that each slot **reads** — a `pop`
into a callee-saved register cannot fault whatever it finds — so this variant
takes `SavedSlotsHold`, which is existential. Liveness wants existentials,
correctness wants values; stating both lets each consume what it needs. -/

set_option maxRecDepth 8000 in
/-- The epilogue runs to the `ret`, from backing alone. -/
theorem epilogue_live (h : SysVEntry L state block rspEntry frameSize m) {mid : MState}
    (hrip : mid.core.rip = L.textBase + BitVec.ofNat 64 441)
    (hrsp : mid.core.read .rsp = rspEntry - BitVec.ofNat 64 216)
    (hsaved : SavedSlotsHold mid.memory rspEntry)
    (hret : Silmaril.X86.Ext.HoldsLE mid.memory rspEntry.toNat 8 L.exit)
    (hloaded : Loaded mid.memory L.textBase (image L.textBase L.rodataBase)) :
    ∃ final, Returns L.exit mid final := by
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hsla : ∀ o l : Nat, relocOffset + 4 ≤ o →
      ((image L.textBase L.rodataBase).drop o).take l = (raw.drop o).take l :=
    fun o l hb => image_slice_above _ _ hb
  have himm : ((0x000000a8#32 : BitVec 32).signExtend 64) = BitVec.ofNat 64 168 := by decide
  obtain ⟨c0, s0, h0rip, h0w, _, h0mem⟩ :=
    Silmaril.X86.Ext.stepOpt_aluI_reg (exit := L.exit) (offset := 441) (len := 7)
      hloaded hrip (by rw [image_length]; decide)
      (by rw [hsla 441 7 (by decide)]; exact epi_decode_441) (by decide) rfl
  have hr0 : c0.core.read .rsp = rspEntry - BitVec.ofNat 64 48 := by
    rw [h0w.target]
    simp only [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.Sz.read_q, hrsp]
    show BitVec.setWidth 64 (rspEntry - BitVec.ofNat 64 216
        + (0x000000a8#32 : BitVec 32).signExtend 64) = rspEntry - BitVec.ofNat 64 48
    rw [himm, BitVec.setWidth_eq, sub_add_ofNat _ (by omega)]
  have hm0 : c0.memory = mid.memory := h0mem
  obtain ⟨sv1, hsv1⟩ := hsaved 5 (by omega)
  have hn1 : (c0.core.read Reg.rsp).toNat = rspEntry.toNat - 48 := by
    rw [hr0]
    exact Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := 48) (by omega) (by omega)
  obtain ⟨p1, t1, p1rip, p1val, p1rsp, p1oth, _, p1mem⟩ :=
    Silmaril.X86.Ext.stepOpt_pop (exit := L.exit) (offset := 448) (len := 1)
      (by rw [hm0]; exact hloaded) h0rip (by rw [image_length]; decide)
      (by rw [hsla 448 1 (by decide)]; exact epi_decode_448)
      (by rw [hn1, hm0]; exact hsv1)
  have hq1 : p1.core.read Reg.rsp = rspEntry - BitVec.ofNat 64 40 := by
    rw [p1rsp (by decide : Reg.rbx ≠ Reg.rsp), hr0, sub_add_ofNat _ (by omega)]
  have hm1 : p1.memory = mid.memory := by rw [p1mem]; exact hm0
  obtain ⟨sv2, hsv2⟩ := hsaved 4 (by omega)
  have hn2 : (p1.core.read Reg.rsp).toNat = rspEntry.toNat - 40 := by
    rw [hq1]
    exact Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := 40) (by omega) (by omega)
  obtain ⟨p2, t2, p2rip, p2val, p2rsp, p2oth, _, p2mem⟩ :=
    Silmaril.X86.Ext.stepOpt_pop (exit := L.exit) (offset := 449) (len := 2)
      (by rw [hm1]; exact hloaded) p1rip (by rw [image_length]; decide)
      (by rw [hsla 449 2 (by decide)]; exact epi_decode_449)
      (by rw [hn2, hm1]; exact hsv2)
  have hq2 : p2.core.read Reg.rsp = rspEntry - BitVec.ofNat 64 32 := by
    rw [p2rsp (by decide : Reg.r12 ≠ Reg.rsp), hq1, sub_add_ofNat _ (by omega)]
  have hm2 : p2.memory = mid.memory := by rw [p2mem]; exact hm1
  obtain ⟨sv3, hsv3⟩ := hsaved 3 (by omega)
  have hn3 : (p2.core.read Reg.rsp).toNat = rspEntry.toNat - 32 := by
    rw [hq2]
    exact Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := 32) (by omega) (by omega)
  obtain ⟨p3, t3, p3rip, p3val, p3rsp, p3oth, _, p3mem⟩ :=
    Silmaril.X86.Ext.stepOpt_pop (exit := L.exit) (offset := 451) (len := 2)
      (by rw [hm2]; exact hloaded) p2rip (by rw [image_length]; decide)
      (by rw [hsla 451 2 (by decide)]; exact epi_decode_451)
      (by rw [hn3, hm2]; exact hsv3)
  have hq3 : p3.core.read Reg.rsp = rspEntry - BitVec.ofNat 64 24 := by
    rw [p3rsp (by decide : Reg.r13 ≠ Reg.rsp), hq2, sub_add_ofNat _ (by omega)]
  have hm3 : p3.memory = mid.memory := by rw [p3mem]; exact hm2
  obtain ⟨sv4, hsv4⟩ := hsaved 2 (by omega)
  have hn4 : (p3.core.read Reg.rsp).toNat = rspEntry.toNat - 24 := by
    rw [hq3]
    exact Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := 24) (by omega) (by omega)
  obtain ⟨p4, t4, p4rip, p4val, p4rsp, p4oth, _, p4mem⟩ :=
    Silmaril.X86.Ext.stepOpt_pop (exit := L.exit) (offset := 453) (len := 2)
      (by rw [hm3]; exact hloaded) p3rip (by rw [image_length]; decide)
      (by rw [hsla 453 2 (by decide)]; exact epi_decode_453)
      (by rw [hn4, hm3]; exact hsv4)
  have hq4 : p4.core.read Reg.rsp = rspEntry - BitVec.ofNat 64 16 := by
    rw [p4rsp (by decide : Reg.r14 ≠ Reg.rsp), hq3, sub_add_ofNat _ (by omega)]
  have hm4 : p4.memory = mid.memory := by rw [p4mem]; exact hm3
  obtain ⟨sv5, hsv5⟩ := hsaved 1 (by omega)
  have hn5 : (p4.core.read Reg.rsp).toNat = rspEntry.toNat - 16 := by
    rw [hq4]
    exact Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := 16) (by omega) (by omega)
  obtain ⟨p5, t5, p5rip, p5val, p5rsp, p5oth, _, p5mem⟩ :=
    Silmaril.X86.Ext.stepOpt_pop (exit := L.exit) (offset := 455) (len := 2)
      (by rw [hm4]; exact hloaded) p4rip (by rw [image_length]; decide)
      (by rw [hsla 455 2 (by decide)]; exact epi_decode_455)
      (by rw [hn5, hm4]; exact hsv5)
  have hq5 : p5.core.read Reg.rsp = rspEntry - BitVec.ofNat 64 8 := by
    rw [p5rsp (by decide : Reg.r15 ≠ Reg.rsp), hq4, sub_add_ofNat _ (by omega)]
  have hm5 : p5.memory = mid.memory := by rw [p5mem]; exact hm4
  obtain ⟨sv6, hsv6⟩ := hsaved 0 (by omega)
  have hn6 : (p5.core.read Reg.rsp).toNat = rspEntry.toNat - 8 := by
    rw [hq5]
    exact Silmaril.X86.Ext.toNat_sub_ofNat (x := rspEntry) (k := 8) (by omega) (by omega)
  obtain ⟨p6, t6, p6rip, p6val, p6rsp, p6oth, _, p6mem⟩ :=
    Silmaril.X86.Ext.stepOpt_pop (exit := L.exit) (offset := 457) (len := 1)
      (by rw [hm5]; exact hloaded) p5rip (by rw [image_length]; decide)
      (by rw [hsla 457 1 (by decide)]; exact epi_decode_457)
      (by rw [hn6, hm5]; exact hsv6)
  have hq6 : p6.core.read Reg.rsp = rspEntry - BitVec.ofNat 64 0 := by
    rw [p6rsp (by decide : Reg.rbp ≠ Reg.rsp), hq5, sub_add_ofNat _ (by omega)]
  have hm6 : p6.memory = mid.memory := by rw [p6mem]; exact hm5
  have hnr : (p6.core.read Reg.rsp).toNat = rspEntry.toNat := by
    rw [hq6]; simp
  obtain ⟨fin, hret', _⟩ :=
    Silmaril.X86.Ext.step_returned_ret (exit := L.exit) (offset := 458) (len := 1)
      (by rw [hm6]; exact hloaded) p6rip (by rw [image_length]; decide)
      (by rw [hsla 458 1 (by decide)]; exact epi_decode_458)
      (by rw [hnr, hm6]; exact hret)
  exact ⟨fin, Silmaril.X86.Ext.Returns.of_reaches (Reaches.cons s0 (Reaches.cons t1 (Reaches.cons t2 (Reaches.cons t3 (Reaches.cons t4 (Reaches.cons t5 (Reaches.one t6))))))) hret'⟩

/-- `state[]` and the return-address slot are disjoint. -/
theorem SysVEntry.state_disjoint_retSlot (h : SysVEntry L state block rspEntry frameSize m) :
    Region.Disjoint (stateRegion state) (returnSlot rspEntry) := by
  have hp := h.disjoint
  simp only [regions, List.pairwise_cons, List.mem_cons] at hp
  exact hp.1 _ (by simp)

/-- The return address survives the function: its slot is outside the
footprint, which is the point of leaving it out. -/
theorem retAddr_preserved (h : SysVEntry L state block rspEntry frameSize m)
    {before after : Memory}
    (hw : Memory.WritesWithin before after (Footprint state rspEntry frameSize))
    (hr : Silmaril.X86.Ext.HoldsLE before rspEntry.toNat 8 L.exit) :
    Silmaril.X86.Ext.HoldsLE after rspEntry.toNat 8 L.exit := by
  have hfits := h.frameFits
  rw [frameExtent_eq] at hfits
  have hd := h.state_disjoint_retSlot
  simp only [stateRegion, returnSlot, Region.Disjoint] at hd
  show after.readBytes _ 8 = _
  rw [Silmaril.Process.Memory.WritesWithin.readBytes hw ?_]
  · exact hr
  · intro o ho
    rintro (⟨hl, hrr⟩ | ⟨hl, hrr⟩)
    · simp only [stateRegion] at hl hrr; omega
    · simp only [frameRegion, frameFloor_eq, frameExtent_eq] at hl hrr; omega

/-- **The whole run, with its frame properties.**

This is the composition of everything above:
`prologue → blockA0 → L1 → blockA → L2 → blockB → L3 → blockC → epilogue`.

It is stated as a `Reaches` plus a returning `step` rather than as `Returns`
so that `Returns.eq_of_reaches` can be applied to it: liveness needs only that
*a* run exists, but the contract needs that this is *the* run. -/
theorem sha256_compress_O2_exec (h : SysVEntry L state block rspEntry frameSize m) :
    ∃ final mid, Silmaril.X86.Ext.Reaches L.exit m mid ∧
      Silmaril.X86.Ext.step L.exit mid = .returned final ∧
      final.core.read .rsp = rspEntry + 8#64 ∧
      sysv64.Preserved m.core.read final.core.read ∧
      Memory.WritesWithin m.memory final.memory (Footprint state rspEntry frameSize) := by
  obtain ⟨m1, r1, i1⟩ := live_to_l1 h
  obtain ⟨m2, r2, i2⟩ := l1_loop h i1
  obtain ⟨m3, r3, i3⟩ := live_to_l2 h i2
  obtain ⟨m4, r4, i4⟩ := l2_loop h i3
  obtain ⟨m5, r5, c5⟩ := live_to_blockC h i4
  obtain ⟨m6, r6, c6⟩ := blockC_weak h c5
  -- the epilogue's hypothesis, assembled from block C's exit invariant
  have hes : EpilogueState L state rspEntry m m6 :=
    { rip := c6.rip, rsp := c6.rsp, slots := c6.saved,
      retAddr := retAddr_preserved h c6.frame h.returnAddress, loaded := c6.loaded }
  obtain ⟨fin, hret, hrsp, hpres, hmem⟩ := epilogue h hes
  obtain ⟨n, mid, hrun, hstep⟩ := hret
  refine ⟨fin, mid, (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))).trans
    (Silmaril.X86.Ext.Reaches.of_runs hrun), hstep, hrsp, hpres, ?_⟩
  rw [hmem]
  exact c6.frame

/-- **`sha256_compress` at clang `-O2` is live.** From any System V entry
state the machine runs to the `ret` and returns to `L.exit`.

It retires the vacuity objection: `Contract` is no longer satisfiable by a
machine that never runs. -/
theorem sha256_compress_O2_live (L : Layout) : Live L frameSize := by
  intro st blk rsp0 m0 h
  obtain ⟨fin, mid, hreach, hstep, _, _, _⟩ := sha256_compress_O2_exec h
  exact ⟨fin, Silmaril.X86.Ext.Returns.of_reaches hreach hstep⟩

/-- **The footprint half of the contract, proved.**

Three of `Post`'s four fields do not depend on what the function computes, and
this is them: the stack pointer is restored, every callee-saved register comes
back, and nothing outside `state[] ∪ frame` is written.

`Contract` quantifies over *any* returning run, while `sha256_compress_O2_exec`
constructs *one*. `Returns.eq_of_reaches` closes that gap: the machine is a
function and a run cannot pass a returning step, so the constructed run is the
only one, and its properties transport to the quantified `final`. -/
theorem sha256_compress_O2_frame (L : Layout) :
    ∀ state block rspEntry initial final,
      SysVEntry L state block rspEntry frameSize initial →
      Silmaril.X86.Ext.Returns L.exit initial final →
      final.core.read .rsp = rspEntry + 8#64 ∧
      sysv64.Preserved initial.core.read final.core.read ∧
      Memory.WritesWithin initial.memory final.memory
        (Footprint state rspEntry frameSize) := by
  intro st blk rsp0 m0 fin h hret
  obtain ⟨fin0, mid, hreach, hstep, hrsp, hpres, hmem⟩ := sha256_compress_O2_exec h
  obtain rfl := Silmaril.X86.Ext.Returns.eq_of_reaches hreach hstep hret
  exact ⟨hrsp, hpres, hmem⟩

/-- Projection of the specification's eight-tuple round state. -/
def stateComp (s : SHA256.Kernel.State) : Nat → SHA256.Kernel.Word
  | 0 => s.1
  | 1 => s.2.1
  | 2 => s.2.2.1
  | 3 => s.2.2.2.1
  | 4 => s.2.2.2.2.1
  | 5 => s.2.2.2.2.2.1
  | 6 => s.2.2.2.2.2.2.1
  | _ => s.2.2.2.2.2.2.2

/-- `Sha256O2.compressBlock` in the form the rounds produce it: unfolding
`compress` into `SHA256.Kernel.compressBlock` applied to the sixteen
big-endian words, exactly as `blockMsg` packages them. -/
theorem compressBlock_eq (H : SHA256.Kernel.InitHash) (bs : List Silmaril.Process.Byte) :
    compressBlock H bs = SHA256.Kernel.compressBlock H (blockMsg bs) := rfl

set_option maxRecDepth 8000 in
/-- **The projection fix**, as a standalone lemma about *any* round state.
`SHA256.Kernel.compressBlock` destructures `let (a, …, h) := rounds …`, which
would force the sixty-four rounds to weak head normal form if closed by
`exact`/unification against a term built from `stateComp` projections.
Generalizing the round state to an opaque variable *before* destructuring
avoids that entirely: `rounds H.state (messageSchedule M)` is never unfolded,
only abstracted and then pattern-matched against itself. -/
theorem compressBlock_state_eq (H : SHA256.Kernel.InitHash) (M : List SHA256.Kernel.Word) :
    SHA256.Kernel.compressBlock H M =
      (⟨stateComp (SHA256.Kernel.rounds H.state (SHA256.Kernel.messageSchedule M)) 0 + H.h0,
        stateComp (SHA256.Kernel.rounds H.state (SHA256.Kernel.messageSchedule M)) 1 + H.h1,
        stateComp (SHA256.Kernel.rounds H.state (SHA256.Kernel.messageSchedule M)) 2 + H.h2,
        stateComp (SHA256.Kernel.rounds H.state (SHA256.Kernel.messageSchedule M)) 3 + H.h3,
        stateComp (SHA256.Kernel.rounds H.state (SHA256.Kernel.messageSchedule M)) 4 + H.h4,
        stateComp (SHA256.Kernel.rounds H.state (SHA256.Kernel.messageSchedule M)) 5 + H.h5,
        stateComp (SHA256.Kernel.rounds H.state (SHA256.Kernel.messageSchedule M)) 6 + H.h6,
        stateComp (SHA256.Kernel.rounds H.state (SHA256.Kernel.messageSchedule M)) 7 + H.h7⟩ :
          SHA256.Kernel.InitHash) := by
  rw [SHA256.Kernel.compressBlock]
  generalize SHA256.Kernel.rounds H.state (SHA256.Kernel.messageSchedule M) = X
  obtain ⟨a, b, c, d, e, f, g, h⟩ := X
  rfl

set_option maxHeartbeats 20000 in
set_option maxRecDepth 8000 in
/-- **The data invariant.** `state[]` holds `Spec.compress` of its entry words
and the sixteen big-endian words of `block[]`.

**The composition.** `live_to_l1_at → l1_loop_at → live_to_l2_at → l2_loop_at
→ live_to_blockC_at → blockC → epilogue`, carrying the actual entry words,
message schedule and round state the whole way — the value-carrying sibling
of `sha256_compress_O2_exec`'s liveness-only composition. `RoundAlias`
reconciles `blockC`'s `r10`/`r9`/`rbx` with `RoundState`'s `rsi`/`rbp`/`r14`,
and `compressBlock_state_eq` widens `SHA256.Kernel.compressBlock`'s `let`-bound
round state into `stateComp` projections without ever forcing `rounds`/
`roundsUpTo` to weak head normal form (see that lemma's doc comment).

**Measured cost: 4529 heartbeats, well under the 8,000,000 that blocked every
previous attempt at this theorem.** The actual obstruction was never the
mathematics — it was two elaboration pathologies that look identical to
"the rounds are too expensive to unfold" until isolated by bisection:

1. `l2_loop_at`'s `hsched` argument is a function equation whose conclusion
   applies the schedule `W` to `j - 2`, `j - 7`, `j - 15`, `j - 16` — not to a
   bound variable alone. Elaborating that argument before `W` is pinned (it is
   `l2_loop_at`'s first positional argument after `h`) makes solving for `W`
   a *non-pattern* higher-order unification problem, which can cost
   arbitrarily many heartbeats before either succeeding or giving up. Passing
   `(W := blockSchedule blockBytes)` explicitly turns it into a first-order
   check. This alone was responsible for minutes of elaboration time turning
   into "still running" at any budget tried.
2. `SpillPin` states each spill slot's address as `rspEntry.toNat - 216 - k`;
   `blockC` wants `rspEntry.toNat - 344 + 4 * i`. The two are equal, but
   `Nat` subtraction does not associate definitionally (it truncates), so
   unifying them is not a matter of unfolding anything — it needs
   `344 ≤ rspEntry.toNat` and `omega`, which `exact`/unification will never
   produce on its own. Composed with (1), Lean kept retrying the expensive
   higher-order problem first and never reached the point of failing fast on
   this one.

With both fixed, the proof is cheap, which is also why the `-O0` proof could
afford to look so much more direct: it has no loop whose join supplies an
argument in `hsched`'s shape. -/
theorem compressed_O2 (L : Layout) :
    ∀ state block rspEntry initial final,
      SysVEntry L state block rspEntry frameSize initial →
      Silmaril.X86.Ext.Returns L.exit initial final →
      ∀ stateBytes blockBytes,
        initial.memory.readBytes state.toNat 32 = some stateBytes →
        initial.memory.readBytes block.toNat 64 = some blockBytes →
        StateHolds final.memory state (compressBlock (stateOf stateBytes) blockBytes) := by
  intro state block rspEntry initial final h hret stateBytes blockBytes hsb hbb
  set sv : Nat → SHA256.Kernel.Word := fun j => leWordAt stateBytes j with hsvdef
  -- L1: the sixteen message words, and `state[]` carried through
  obtain ⟨m1, r1, i1, hsw1⟩ := live_to_l1_at h hsb
  obtain ⟨m2, r2, i2, hw2, hsw2⟩ := l1_loop_at h hbb i1 hsw1
  have hw2' : WWordsAt m2.memory rspEntry (fun j => (blockSchedule blockBytes j).setWidth 64) 16 :=
    fun j hj => by
      show HoldsLE m2.memory (rspEntry.toNat - 312 + 4 * j) 4
        ((blockSchedule blockBytes j).setWidth 64)
      rw [blockSchedule_lt blockBytes hj]; exact hw2 j hj
  -- L1 → L2 join
  obtain ⟨m3, r3, i3, hw3, hdx3, hsw3⟩ := live_to_l2_at h i2 hw2' hsw2
  -- L2: the rest of the schedule
  obtain ⟨m4, r4, i4, hw4, hsw4⟩ := l2_loop_at (W := blockSchedule blockBytes) h
    (fun j hj16 hj64 => blockSchedule_succ blockBytes hj16 hj64) i3 hw3 hdx3 hsw3
  -- L2 → L3 → block C join, carrying the round state and the spills
  obtain ⟨m5, r5, c5, hround5, halias5, hspill5⟩ := live_to_blockC_at h i4 hw4 hsw4
  obtain ⟨hsp0, hsp1, hsp2, hsp3, hsp4, hsp5, hsp6, hsp7⟩ := hspill5
  -- `SpillPin` states each slot as `rspEntry.toNat - 216 - k`; `blockC` wants
  -- `rspEntry.toNat - 344 + 4 * i`. The two are equal, but only propositionally
  -- (`Nat` subtraction does not associate definitionally without knowing
  -- `344 ≤ rspEntry.toNat`), so each slot needs an explicit `omega`-justified
  -- address rewrite rather than a bare `exact`.
  have hfits : (344 : Nat) ≤ rspEntry.toNat := by
    have := h.frameFits; rwa [frameExtent_eq] at this
  have hsp0 : HoldsLE m5.memory (rspEntry.toNat - 344 + 4 * 0) 4 ((sv 0).setWidth 64) := by
    rw [show rspEntry.toNat - 344 + 4 * 0 = rspEntry.toNat - 216 - 128 from by omega]; exact hsp0
  have hsp1 : HoldsLE m5.memory (rspEntry.toNat - 344 + 4 * 1) 4 ((sv 1).setWidth 64) := by
    rw [show rspEntry.toNat - 344 + 4 * 1 = rspEntry.toNat - 216 - 124 from by omega]; exact hsp1
  have hsp2 : HoldsLE m5.memory (rspEntry.toNat - 344 + 4 * 2) 4 ((sv 2).setWidth 64) := by
    rw [show rspEntry.toNat - 344 + 4 * 2 = rspEntry.toNat - 216 - 120 from by omega]; exact hsp2
  have hsp3 : HoldsLE m5.memory (rspEntry.toNat - 344 + 4 * 3) 4 ((sv 3).setWidth 64) := by
    rw [show rspEntry.toNat - 344 + 4 * 3 = rspEntry.toNat - 216 - 116 from by omega]; exact hsp3
  have hsp4 : HoldsLE m5.memory (rspEntry.toNat - 344 + 4 * 4) 4 ((sv 4).setWidth 64) := by
    rw [show rspEntry.toNat - 344 + 4 * 4 = rspEntry.toNat - 216 - 112 from by omega]; exact hsp4
  have hsp5 : HoldsLE m5.memory (rspEntry.toNat - 344 + 4 * 5) 4 ((sv 5).setWidth 64) := by
    rw [show rspEntry.toNat - 344 + 4 * 5 = rspEntry.toNat - 216 - 108 from by omega]; exact hsp5
  have hsp6 : HoldsLE m5.memory (rspEntry.toNat - 344 + 4 * 6) 4 ((sv 6).setWidth 64) := by
    rw [show rspEntry.toNat - 344 + 4 * 6 = rspEntry.toNat - 216 - 104 from by omega]; exact hsp6
  have hsp7 : HoldsLE m5.memory (rspEntry.toNat - 344 + 4 * 7) 4 ((sv 7).setWidth 64) := by
    rw [show rspEntry.toNat - 344 + 4 * 7 = rspEntry.toNat - 216 - 100 from by omega]; exact hsp7
  set R : SHA256.Kernel.State :=
    SHA256.Kernel.roundsUpTo (blockSchedule blockBytes)
      (sv 0, sv 1, sv 2, sv 3, sv 4, sv 5, sv 6, sv 7) 64 with hRdef
  have e0 : stateComp R 0 = read32 m5.core .r12 := by rw [hround5]; rfl
  have e1 : stateComp R 1 = read32 m5.core .r8 := by rw [hround5]; rfl
  have e2 : stateComp R 2 = read32 m5.core .rdx := by rw [hround5]; rfl
  have e3 : stateComp R 3 = read32 m5.core .r11 := by rw [hround5]; rfl
  have e4 : stateComp R 4 = read32 m5.core .r13 := by rw [hround5]; rfl
  have e5 : stateComp R 5 = read32 m5.core .rsi := by rw [hround5]; rfl
  have e6 : stateComp R 6 = read32 m5.core .rbp := by rw [hround5]; rfl
  have e7 : stateComp R 7 = read32 m5.core .r14 := by rw [hround5]; rfl
  have hr5 : read32 m5.core .r10 = stateComp R 5 := halias5.1.trans e5.symm
  have hr6 : read32 m5.core .r9 = stateComp R 6 := halias5.2.1.trans e6.symm
  have hr7 : read32 m5.core .rbx = stateComp R 7 := halias5.2.2.trans e7.symm
  -- block C: the feed-forward, by value
  obtain ⟨m6, r6, c6, fin0, fin1, fin2, fin3, fin4, fin5, fin6, fin7⟩ :=
    blockC h c5
      (stateComp R 0) (stateComp R 1) (stateComp R 2) (stateComp R 3)
      (stateComp R 4) (stateComp R 5) (stateComp R 6) (stateComp R 7)
      hsp0 hsp1 hsp2 hsp3 hsp4 hsp5 hsp6 hsp7
      e0.symm e1.symm e2.symm e3.symm e4.symm hr5 hr6 hr7
  have hsh : StateHolds m6.memory state
      ⟨stateComp R 0 + sv 0, stateComp R 1 + sv 1, stateComp R 2 + sv 2, stateComp R 3 + sv 3,
       stateComp R 4 + sv 4, stateComp R 5 + sv 5, stateComp R 6 + sv 6, stateComp R 7 + sv 7⟩ :=
    stateHolds_of_words (w := fun i => stateComp R i + sv i) (by
      intro j hj
      have hjc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
      rcases hjc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact fin0
      · exact fin1
      · exact fin2
      · exact fin3
      · exact fin4
      · exact fin5
      · exact fin6
      · exact fin7)
  -- the epilogue, and identifying `final` with the run just constructed
  have hes : EpilogueState L state rspEntry initial m6 :=
    { rip := c6.rip, rsp := c6.rsp, slots := c6.saved,
      retAddr := retAddr_preserved h c6.frame h.returnAddress, loaded := c6.loaded }
  obtain ⟨fin, hret', _, _, hmem'⟩ := epilogue h hes
  obtain ⟨n, mid, hrun, hstep⟩ := hret'
  obtain rfl := Silmaril.X86.Ext.Returns.eq_of_reaches
    ((r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))).trans
      (Silmaril.X86.Ext.Reaches.of_runs hrun)) hstep hret
  have hrounds : R = SHA256.Kernel.rounds (stateOf stateBytes).state
      (SHA256.Kernel.messageSchedule (blockMsg blockBytes)) := by
    rw [hRdef, show (stateOf stateBytes).state = (sv 0, sv 1, sv 2, sv 3, sv 4, sv 5, sv 6, sv 7)
      from rfl]
    exact SHA256.Kernel.roundsUpTo_64 _ _ _ (SHA256.Kernel.messageSchedule_length _)
      (fun j _ => blockSchedule_def blockBytes j)
  rw [hmem', compressBlock_eq, compressBlock_state_eq, ← hrounds]
  exact hsh

/-- **The pilot theorem**: the clang `-O2` image of `sha256_compress`, loaded
at any layout whose relocation fits, satisfies the System V contract at the
frame size its own prologue sets up.

`frameSize` is `6 * 8 + 0xa8 = 216`, tied to the bytes by
`Image.rawNat_prologue` and `Image.rawNat_epilogue`.

The statement is unchanged from the branch's first contract commit. Three of
its four fields are discharged here by `sha256_compress_O2_frame`; the fourth
is `compressed_O2`, proved above. -/
theorem sha256_compress_O2 (L : Layout) : Contract L frameSize := by
  intro st blk rsp0 m0 fin h hret
  obtain ⟨hrsp, hpres, hmem⟩ := sha256_compress_O2_frame L st blk rsp0 m0 fin h hret
  exact ⟨compressed_O2 L st blk rsp0 m0 fin h hret, hrsp, hpres, hmem⟩

end Silmaril.Crypto.X86.Sha256O2
