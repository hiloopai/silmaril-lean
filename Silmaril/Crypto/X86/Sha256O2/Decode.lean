module

public import Silmaril.Crypto.X86.Sha256O2.Image
public import Silmaril.X86.Ext.Decode

/-!
# `Ext.decode` consumes the clang `-O2` `sha256_compress` image end to end

The completeness check for #882 Track 3: every one of the 459 bytes of
`Sha256O2.raw` is consumed by `Silmaril.X86.Ext.decode`, in 133 instructions
whose lengths sum to exactly `0x1cb`.

`Sha256O2/Image.lean` deliberately makes no claim that its bytes decode; this
module is where that claim lives, so that the byte literal stays independent
of the instruction model.

## Built on Track 1's generic walk

`decodeLengths`, `decodeAll` and `Covered` live in `Silmaril/X86/Ext/Decode.lean`
(Track 1, #909) and are the Lean form of the check
`scripts/x86-crosscheck.py --images` performs at runtime. This module owns only
the facts about *this image*; it no longer carries its own walk.

## What this actually proves, and why it is stronger than "it parses"

`Ext.decode` is not just a parser: it re-encodes the instruction it has read
and requires the result to be a prefix of the input. So a successful walk says
more than "the model admits these bytes".

`raw_covered` is the sharp form, via Track 1's `Covered`: the 459 bytes are
**exactly** the concatenation of the canonical encodings of the 133
instructions read. Nothing is skipped, nothing is left over, and every
instruction is spelled the way `encode` spells it — so `decode` and `encode`
round-trip on every instruction clang 18.1.3 emitted here. A model that
decoded some of these bytes to an instruction it would have written
differently would fail the walk rather than pass it with a different answer.

These are `rfl`, so the kernel runs the decoder over the literal. The whole
file elaborates in a few seconds; there is no `native decision tactic` and no
`bv_decide` anywhere.

## Which instruction forms this exercises

All six forms Track 1's P1 band added for this function are covered by
`decodeLengths_raw`, and the named lemmas below pin the two that were
specifically in doubt:

* `decode_longNop` — `66 66 66 66 2E 0F 1F 84 00 00000000`, thirteen bytes,
  a four-`66` run followed by a `2E` CS override. This needed a prefix
  *stack* (`Raw.pNopPad`) and a new `Raw.Pfx.nopPad` constructor, not just an
  opcode row, and it is the instruction at which decoding previously stopped.
* `decode_cmpRaxImm32` — `48 3D 00 01 00 00`, `cmp $0x100,%rax`: the
  accumulator-immediate `CMP` **with** `REX.W`. The band summary called for
  `3D id` against `eAX`; the form this image actually uses is the 64-bit one.

`decode_movEaxImm32` covers the other correction: `B8+r id` is needed here
**without** `REX.W`, which an earlier `shape` rejected via a `w = true`
conjunct.

## Scope

Decoding is checked on `raw`, the unrelocated bytes, and on `image` at one
concrete layout. A relocation changes the *value* of a `disp32`, never the
*length* of an instruction, so the instruction boundaries are the same for
every layout; but that is an argument about `patch32`, and proving
`decodeLengths` layout-independent needs a lemma that patching four bytes
inside a `disp32` field preserves the decode. That lemma belongs with the
execution proof and is not claimed here — `decodeLengths_image` is a check at
one layout, not a theorem about all of them.
`Sha256O2/Listing.lean` now proves it: `image_decode` says the image decodes,
at every layout, to the lifted transcription with the relocated `lea`, through
the generic `Lift.decodeFrom_splice`.

This module previously carried its own copy of the walk. Track 1 has since
pulled it into `Ext/Decode.lean`, so the copy is gone and only the
image-specific theorems remain.
-/

@[expose] public section

namespace Silmaril.Crypto.X86.Sha256O2

open Silmaril.Process (Byte)
open Silmaril.X86 (Word)
open Silmaril.X86.Ext (decode decodeAll decodeLengths Covered)

/-- The lengths of the 133 instructions of `sha256_compress`, in order.

The shape is legible at both ends: `1, 2, 2, 2, 2, 1` are the six callee-saved
pushes (`push %rbp` is one byte, the five `r12`–`r15`/`rbx` forms take a REX
byte except `rbx`), `7` is `sub $0xa8,%rsp`, `2` is `xor %eax,%eax` and `13`
is the long NOP; the tail `7, 1, 2, 2, 2, 2, 1, 1` is `add $0xa8,%rsp`, the six
pops and `ret`. -/
def instructionLengths : List Nat :=
  [1, 2, 2, 2, 2, 1, 7, 2, 13, 3, 2, 4, 3, 4, 2, 5, 4, 5, 7, 4, 3, 4, 3, 4, 3, 3, 4, 3, 3, 2, 3, 3, 4, 3, 3, 3, 5, 3, 5, 3, 2, 4, 2, 3, 4, 3, 4, 4, 3, 3, 4, 2, 7, 5, 5, 4, 5, 5, 4, 4, 5, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5, 3, 3, 3, 3, 3, 3, 4, 2, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 4, 3, 3, 3, 6, 6, 5, 3, 5, 4, 4, 3, 5, 4, 5, 4, 5, 4, 5, 4, 4, 3, 7, 1, 2, 2, 2, 2, 1, 1]

/-- The number of instructions in `sha256_compress` at clang `-O2`.

133, not the 134 an `objdump | grep -c` reports: the 13-byte NOP is printed
across two lines and the continuation counts as an instruction if the bytes
are not summed. -/
def instructionCount : Nat := 133

set_option maxRecDepth 100000 in
/-- **The completeness check.** `Ext.decode` consumes all 459 bytes of the
function, one canonical instruction at a time. -/
theorem decodeLengths_raw : decodeLengths 600 raw = some instructionLengths := by
  rfl

set_option maxRecDepth 100000 in
/-- There are 133 instructions. -/
theorem instructionLengths_length : instructionLengths.length = instructionCount := by
  rfl

/-- Their lengths sum to the symbol size, `0x1cb` = 459: the decode covers the
function exactly, with no byte left over and none read past the end.

Derived from Track 1's `sum_decodeLengths` rather than recomputed, so the
arithmetic a reader checks against `readelf` is the general lemma applied to
this image. -/
theorem instructionLengths_sum : instructionLengths.sum = size := by
  rw [← raw_length]
  exact Silmaril.X86.Ext.sum_decodeLengths decodeLengths_raw

set_option maxRecDepth 100000 in
/-- **The sharp form.** The 459 bytes are exactly the concatenation of the
canonical encodings of the instructions read: nothing skipped, nothing left
over, and every instruction spelled the way `encode` spells it. -/
theorem raw_covered : Covered raw := by
  have h : (decodeAll 600 raw).isSome = true := by rfl
  obtain ⟨instrs, hi⟩ := Option.isSome_iff_exists.mp h
  exact Silmaril.X86.Ext.covered_of_decodeAll hi

set_option maxRecDepth 100000 in
/-- The same check on the relocated image, at one concrete layout. See the
module doc on why this is a check and not a theorem about all layouts. -/
theorem decodeLengths_image :
    decodeLengths 600 (image 0x401000#64 0x402000#64) = some instructionLengths := by
  rfl

/-! ### The forms that were in doubt

Each is the exact byte string as it appears in the image, with the function
offset at which it occurs. -/

/-- Function offset `0x13`: `66 66 66 66 2E 0F 1F 84 00 00000000`, a 13-byte
NOP behind a four-`66` run and a `2E` CS override. Decoding this needs a
prefix stack; it is where decoding stopped before Track 1's P1 band. -/
theorem decode_longNop :
    (decode ((([0x66, 0x66, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84,
                0x00, 0x00, 0x00, 0x00, 0x00] : List Nat)).map (BitVec.ofNat 8))).map
      Prod.snd = some 13 := by
  rfl

/-- Function offset `0x3b`: `0F 1F 44 00 00`, the plain five-byte `nopl`. -/
theorem decode_shortNop :
    (decode ((([0x0f, 0x1f, 0x44, 0x00, 0x00] : List Nat)).map (BitVec.ofNat 8))).map
      Prod.snd = some 5 := by
  rfl

/-- Function offset `0x16a`: `48 3D 00 01 00 00`, `cmp $0x100,%rax` — the
accumulator-immediate `CMP` **with** `REX.W`, which is the form this image
uses rather than the 32-bit `3D id` the band summary named. -/
theorem decode_cmpRaxImm32 :
    (decode ((([0x48, 0x3d, 0x00, 0x01, 0x00, 0x00] : List Nat)).map (BitVec.ofNat 8))).map
      Prod.snd = some 6 := by
  rfl

/-- Function offset `0x32`: `B8 10 00 00 00`, `mov $0x10,%eax` — `B8+r id`
**without** `REX.W`, the form an earlier `shape` rejected. -/
theorem decode_movEaxImm32 :
    (decode ((([0xb8, 0x10, 0x00, 0x00, 0x00] : List Nat)).map (BitVec.ofNat 8))).map
      Prod.snd = some 5 := by
  rfl

/-- Function offset `0x23`: `0F C9`, `bswap %ecx`, the message byte swap. -/
theorem decode_bswapEcx :
    (decode ((([0x0f, 0xc9] : List Nat)).map (BitVec.ofNat 8))).map Prod.snd = some 2 := by
  rfl

/-- Function offset `0x29`: `48 FF C0`, `inc %rax`, a loop counter. -/
theorem decode_incRax :
    (decode ((([0x48, 0xff, 0xc0] : List Nat)).map (BitVec.ofNat 8))).map Prod.snd = some 3 := by
  rfl

/-- Function offset `0x30`: `75 EE`, `jne` rel8, a loop backedge. -/
theorem decode_jneRel8 :
    (decode ((([0x75, 0xee] : List Nat)).map (BitVec.ofNat 8))).map Prod.snd = some 2 := by
  rfl

end Silmaril.Crypto.X86.Sha256O2
