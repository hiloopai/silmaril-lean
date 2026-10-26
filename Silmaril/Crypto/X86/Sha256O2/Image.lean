module

public import Silmaril.Process.Memory
public import Silmaril.X86.Basic

/-!
# The clang `-O2` `.text` image of `sha256_compress`

The 459 bytes of the `sha256_compress` symbol in `xcompile/`'s pinned
`x86_64/clang` `-O2` `sha256.o`, the one relocation that falls inside them,
and the 256 bytes of `sha256_compress.K` that the relocation reaches.

This is the `-O2` sibling of `Silmaril/Crypto/X86/Sha256O0/Image.lean` and
deliberately mirrors its shape, so that the two contracts differ only in their
constants.

## Provenance

* object: `x86_64/clang` `-O2` `sha256.o`, clang 18.1.3, flags as in
  `xcompile/build.sh`;
  SHA-256 `8f699c03531ebda895512e30a74ac73ac574ce1bae41cef0af08537ea46a78c7`,
  which is the `xcompile/manifest.json` entry for that cell, rebuilt on the
  pinned toolchain and matching bit-for-bit;
* symbol: `sha256_compress`, `.text + 0x20`, size `0x1cb` = 459 bytes,
  **133** instructions, `FUNC GLOBAL HIDDEN`. (133, not the 134 an `objdump |
  grep -c` reports: the 13-byte NOP at `0x33` is printed across two lines, and
  the continuation line counts as an instruction if the bytes are not summed.
  Decoding the 459 bytes linearly yields 133 instructions totalling exactly
  459 bytes.)
* SHA-256 of the 459 bytes themselves:
  `b40a9bb4fe1c44697d153444180bf4e534b8c7b28b0ee5223f8c61fc66d07d44`;
* SHA-256 of the 256 bytes of `sha256_compress.K`:
  `74ef7306e7452d6859b6463ce496b8df30925f69e1b2969e1f3f34bbc9c6af04`.

## `-fno-vectorize -fno-slp-vectorize` is a no-op here

#882 asks for this cell to be compiled with `-fno-vectorize
-fno-slp-vectorize` and the object checked for SSE. Rebuilding it with those
flags added produces a **byte-identical** object — the SHA-256 above, either
way — and `objdump` over `[0x20, 0x1eb)` finds no SIMD mnemonic of any kind.
So the pinned manifest entry already satisfies that instruction and these
bytes are the ones #882 asks about. The flags are clang's spelling; gcc
rejects them and spells the same thing `-fno-tree-vectorize
-fno-tree-slp-vectorize`, which matters for the gcc tracks but not here.

## The relocation, and the one that is not ours

`.rela.text` has twelve entries. Exactly **one** of them lies in
`[0x20, 0x1eb)`: `R_X86_64_PC32` at `.text` offset `0xd7` against `.rodata`
with addend `-4`. That is function offset `0xd7 - 0x20 = 0xb7`, the `disp32`
of `48 8d 0d <disp32>` = `lea 0x0(%rip), %rcx` at function offset `0xb4`,
which materialises the address of `sha256_compress.K` (`.rodata + 0`). In the
object the four bytes are zero; `image` fills them in.

The object also contains `R_X86_64_PC32` relocations against `.LCPI0_0` and
`.LCPI0_1` in `.rodata.cst16`, at `.text` offsets `0x20e` and `0x219`. Those
are **past the end of this symbol** and belong to other functions in the
translation unit (the inlined `memcpy`/byte-swap code of `xc_sha256`'s
wrapper). They are not ingested here, and `sha256_compress` touches no
`.rodata.cst16` byte.

## Why the image is a function of two addresses

`sha256_compress` is **not** position-independent as a byte string: the
`disp32` above depends on where `.text` and `.rodata` land. `image textBase
rodataBase` is the relocated byte string, and it is what a contract about the
function must quote. Writing a contract over an *arbitrary* byte list would
not be a weaker theorem, it would be a false one; writing it over `raw` alone
would be a theorem about code with a dangling zero displacement.

`R_X86_64_PC32` computes `S + A - P`, with `S` the symbol address
(`rodataBase`), `A` the addend (`-4`) and `P` the address of the relocated
field (`textBase + 0xb7`). The result is truncated to 32 bits. The RIP-relative
effective address is then
`(textBase + 0xbb) + (rodataBase - textBase - 0xbb) = rodataBase`, as it
should be.

## Frame size, and why the red-zone term is exactly saturated

The prologue is six one- or two-byte pushes and a `sub`:

```
  20:  55              push %rbp          -- an ordinary callee-saved GPR here:
  21:  41 57           push %r15             there is no `mov %rsp,%rbp` anywhere
  23:  41 56           push %r14             in the function and no `%rbp`-based
  25:  41 55           push %r13             memory operand. The function has no
  27:  41 54           push %r12             frame pointer.
  29:  53              push %rbx
  2a:  48 81 ec a8..   sub  $0xa8,%rsp
```

and the epilogue undoes it exactly (`add $0xa8,%rsp`, six pops, `ret`). There
is no other `%rsp` arithmetic, no further `push`/`pop` and no `call`: the
function is a leaf. So `frameSize = 6 * 8 + 0xa8 = 48 + 168 = 216` measured
from the entry `%rsp`, and `%rsp` in the body is `rsp_entry - 216`.

Every memory operand in the body is `%rsp`-relative. The stack map is:

| region | addresses | contents |
| --- | --- | --- |
| working copy of `a…h` | `[rsp-128, rsp-96)` | eight `uint32`, `-0x80(%rsp) … -0x64(%rsp)` |
| `uint32_t w[64]` | `[rsp-96, rsp+160)` | `w[t]` at `-0x60(%rsp,%rax,4)` |
| frame from `sub` | `[rsp, rsp+168)` | the top 164 bytes of `w[]` |

The lowest byte the function touches is therefore `rsp - 128`, from
`mov %r12d,-0x80(%rsp)`, which is
`rsp_entry - 216 - 128 = rsp_entry - 344`. **#882's footprint floor
`rsp_entry − F − 128` is `rsp_entry - 344` — exactly equal.** At `-O2` the red
zone is saturated to the byte: drop the `-128` term and the theorem is false,
where at `-O0` it had four bytes to spare.

Three operands have a displacement that *looks* lower than `-0x80` —
`-0x9c(%rsp,%rax,4)`, `-0x7c(%rsp,%rax,4)` and `-0x68(%rsp,%rax,4)`, which are
`w[t-15]`, `w[t-7]` and `w[t-2]`. They are all read inside the schedule loop,
where the invariant gives `16 ≤ t`, so the lowest address any of them forms is
`rsp - 156 + 4 * 16 = rsp - 92`, above the floor. The bound above is a claim
about the loop invariants, not about the displacements alone.

## The instruction forms this image needs

The 133 instructions use 32 distinct opcode/digit forms. Beyond what
`Silmaril.X86.Ext` already models and the P0 band (RIP-relative addressing,
base-less addressing, ALU direction-1, `83 /digit ib`, `98`), exactly six
forms are required, and they are narrower than the full P1 band. **All six are
now in the model**, and `Sha256O2/Decode.lean` checks each one individually as
well as the whole image:

| form | count | where |
| --- | --- | --- |
| `0F C8+r` BSWAP r32 (no REX.W) | 1 | `0x43` `0f c9`, the message byte swap |
| `75 cb` JNE rel8 | 2 | `0x50`, `0xb4`, the two inner loop backedges |
| `REX.W FF /0` INC r/m64 | 2 | `0x49`, `0xab` `48 ff c0`, the loop counters |
| `B8+r id` MOV r32, imm32, **no REX.W** | 1 | `0x52` `b8 10 00 00 00` |
| `REX.W 3D id` CMP rAX, imm32 | 1 | `0x18a` `48 3d 00 01 00 00` |
| `0F 1F /0` NOP | 2 | `0x5b` (disp8) and `0x33` (disp32, prefixed) |

Three things this list says that the band summary does not:

* `EB cb` JMP rel8, `FF /1` DEC, `FF /6` PUSH r/m and the accumulator forms
  `05 0D 25 2D 35 A9` **do not occur here**. Only `3D` does, and only with
  REX.W.
* `B8+r id` is needed in its **non-REX.W** form, which zero-extends to 64 bits.
* The NOP at `0x33` is `66 66 66 66 2E 0F 1F 84 00 00 00 00 00` — thirteen
  bytes, **four** `66` operand-size prefixes followed by a `2E` CS segment
  override. Decoding it needs a prefix *stack* rather than a single optional
  prefix, and needs `2E` to be a recognised (and, for a NOP, semantically
  inert) prefix. That is a structural change to prefix parsing, not one more
  opcode row, and it is the single hardest decoding requirement in this image.

No instruction here is `8B /r` with `mod = 11`, and the only `8D` is
`48 8d 0d` with REX.W, so the two known restrictions in the current encoder —
`8B` being load-only and `LEA` being 64-bit-only — do not bite.

## Scope

This module contains bytes and a relocation, nothing else, and deliberately
does not import the instruction model: the byte literal stays independent of
`Silmaril.X86.Ext`.

That the bytes **do** decode is proved next door, in
`Silmaril/Crypto/X86/Sha256O2/Decode.lean`: `Ext.decode` consumes all 459
bytes in 133 canonical instructions (`decodeLengths_raw`). What they *compute*
is stated in `Silmaril/Crypto/X86/Sha256O2.lean`.
-/

@[expose] public section

namespace Silmaril.Crypto.X86.Sha256O2

open Silmaril.Process (Byte)
open Silmaril.X86 (Word)

/-- The `.text` bytes of `sha256_compress` as they appear in the object, with
the relocated `disp32` still zero. Written as naturals so that the literal
elaborates as numerals rather than through 459 `OfNat (BitVec 8)` instance
searches. -/
def rawNat : List Nat :=
[
  0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81,
  0xec, 0xa8, 0x00, 0x00, 0x00, 0x31, 0xc0, 0x66, 0x66, 0x66, 0x66, 0x2e,
  0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x0c, 0x86, 0x0f,
  0xc9, 0x89, 0x4c, 0x84, 0xa0, 0x48, 0xff, 0xc0, 0x48, 0x83, 0xf8, 0x10,
  0x75, 0xee, 0xb8, 0x10, 0x00, 0x00, 0x00, 0x8b, 0x54, 0x24, 0xa0, 0x0f,
  0x1f, 0x44, 0x00, 0x00, 0x8b, 0x8c, 0x84, 0x64, 0xff, 0xff, 0xff, 0x8b,
  0x74, 0x84, 0x98, 0x41, 0x89, 0xc8, 0x41, 0xc1, 0xc0, 0x19, 0x41, 0x89,
  0xc9, 0x41, 0xc1, 0xc1, 0x0e, 0x45, 0x31, 0xc1, 0x41, 0x89, 0xc8, 0x41,
  0xc1, 0xe8, 0x03, 0x45, 0x31, 0xc8, 0x41, 0x01, 0xd0, 0x89, 0xf2, 0xc1,
  0xc2, 0x0f, 0x41, 0x89, 0xf1, 0x41, 0xc1, 0xc1, 0x0d, 0x41, 0x31, 0xd1,
  0xc1, 0xee, 0x0a, 0x44, 0x31, 0xce, 0x44, 0x03, 0x44, 0x84, 0x84, 0x41,
  0x01, 0xf0, 0x44, 0x89, 0x44, 0x84, 0xa0, 0x48, 0xff, 0xc0, 0x89, 0xca,
  0x48, 0x83, 0xf8, 0x40, 0x75, 0xaa, 0x44, 0x8b, 0x27, 0x44, 0x8b, 0x47,
  0x04, 0x8b, 0x57, 0x08, 0x44, 0x8b, 0x5f, 0x0c, 0x44, 0x8b, 0x6f, 0x10,
  0x8b, 0x77, 0x14, 0x8b, 0x6f, 0x18, 0x44, 0x8b, 0x77, 0x1c, 0x31, 0xc0,
  0x48, 0x8d, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x44, 0x89, 0x64, 0x24, 0x80,
  0x44, 0x89, 0x44, 0x24, 0x84, 0x89, 0x54, 0x24, 0x88, 0x44, 0x89, 0x5c,
  0x24, 0x8c, 0x44, 0x89, 0x74, 0x24, 0x9c, 0x89, 0x6c, 0x24, 0x98, 0x89,
  0x74, 0x24, 0x94, 0x44, 0x89, 0x6c, 0x24, 0x90, 0x45, 0x89, 0xea, 0x41,
  0x89, 0xf1, 0x89, 0xeb, 0x45, 0x89, 0xdd, 0x41, 0x89, 0xd3, 0x44, 0x89,
  0xc2, 0x44, 0x89, 0xd6, 0xc1, 0xc6, 0x1a, 0x44, 0x89, 0xd5, 0xc1, 0xc5,
  0x15, 0x31, 0xf5, 0x44, 0x89, 0xd6, 0xc1, 0xc6, 0x07, 0x31, 0xee, 0x44,
  0x89, 0xcd, 0x44, 0x21, 0xd5, 0x44, 0x01, 0xf5, 0x45, 0x89, 0xd6, 0x41,
  0xf7, 0xd6, 0x41, 0x21, 0xde, 0x41, 0x01, 0xee, 0x41, 0x01, 0xf6, 0x44,
  0x03, 0x34, 0x08, 0x44, 0x03, 0x74, 0x04, 0xa0, 0x45, 0x89, 0xe0, 0x44,
  0x89, 0xe6, 0xc1, 0xc6, 0x1e, 0x44, 0x89, 0xe5, 0xc1, 0xc5, 0x13, 0x45,
  0x89, 0xe7, 0x41, 0xc1, 0xc7, 0x0a, 0x31, 0xf5, 0x41, 0x31, 0xef, 0x89,
  0xd6, 0x44, 0x31, 0xde, 0x44, 0x21, 0xe6, 0x41, 0x89, 0xd4, 0x45, 0x21,
  0xdc, 0x41, 0x31, 0xf4, 0x45, 0x01, 0xfc, 0x45, 0x01, 0xf5, 0x45, 0x01,
  0xf4, 0x48, 0x83, 0xc0, 0x04, 0x41, 0x89, 0xde, 0x44, 0x89, 0xcd, 0x44,
  0x89, 0xd6, 0x48, 0x3d, 0x00, 0x01, 0x00, 0x00, 0x0f, 0x85, 0x6a, 0xff,
  0xff, 0xff, 0x44, 0x03, 0x64, 0x24, 0x80, 0x44, 0x89, 0x27, 0x44, 0x03,
  0x44, 0x24, 0x84, 0x44, 0x89, 0x47, 0x04, 0x03, 0x54, 0x24, 0x88, 0x89,
  0x57, 0x08, 0x44, 0x03, 0x5c, 0x24, 0x8c, 0x44, 0x89, 0x5f, 0x0c, 0x44,
  0x03, 0x6c, 0x24, 0x90, 0x44, 0x89, 0x6f, 0x10, 0x44, 0x03, 0x54, 0x24,
  0x94, 0x44, 0x89, 0x57, 0x14, 0x44, 0x03, 0x4c, 0x24, 0x98, 0x44, 0x89,
  0x4f, 0x18, 0x03, 0x5c, 0x24, 0x9c, 0x89, 0x5f, 0x1c, 0x48, 0x81, 0xc4,
  0xa8, 0x00, 0x00, 0x00, 0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41,
  0x5f, 0x5d, 0xc3
]

/-- The unrelocated image. -/
def raw : List Byte := rawNat.map (BitVec.ofNat 8)

set_option maxRecDepth 8000 in
theorem rawNat_length : rawNat.length = 459 := by rfl

/-- The size of `sha256_compress`, in bytes. -/
def size : Nat := 459

@[simp] theorem raw_length : raw.length = size := by
  rw [raw, List.length_map, rawNat_length]; rfl

/-- The function-relative offset of the single `R_X86_64_PC32` field:
`.text` offset `0xd7` less the `0x20` at which the symbol starts. -/
def relocOffset : Nat := 0xb7

/-- The relocation addend, as the psABI records it. -/
def relocAddend : Int := -4

/-- The frame size, measured from the entry `%rsp`: the `0xa8` of the `sub`
plus the `6 * 8` bytes the six callee-saved pushes took. See the module
doc. -/
def frameSize : Nat := 6 * 8 + 0xa8

@[simp] theorem frameSize_eq : frameSize = 216 := rfl

/-! ### Checks on the bytes

These are `rfl`, so the claims the module doc makes about the prologue, the
epilogue and the relocation site are machine-checked against the literal
rather than asserted in prose. -/

set_option maxRecDepth 8000 in
/-- `push %rbp; push %r15; push %r14; push %r13; push %r12; push %rbx;
sub $0xa8,%rsp`. This is where `frameSize` comes from: `0xa8` from the `sub`,
plus eight bytes for each of the six pushes. -/
theorem rawNat_prologue :
    rawNat.take 17 =
      [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53,
       0x48, 0x81, 0xec, 0xa8, 0x00, 0x00, 0x00] := by
  rfl

set_option maxRecDepth 8000 in
/-- `add $0xa8,%rsp; pop %rbx; pop %r12; pop %r13; pop %r14; pop %r15;
pop %rbp; ret`: the `sub` is undone exactly and the six pushes are popped in
reverse order, so the `%rsp` at the `ret` is the entry `%rsp` and all six
callee-saved registers are restored. -/
theorem rawNat_epilogue :
    rawNat.drop (size - 18) =
      [0x48, 0x81, 0xc4, 0xa8, 0x00, 0x00, 0x00,
       0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d, 0xc3] := by
  rfl

set_option maxRecDepth 8000 in
/-- The relocation site: `48 8d 0d` is `lea disp32(%rip), %rcx`, and the four
displacement bytes are zero in the object, as an unresolved `R_X86_64_PC32`
field must be. -/
theorem rawNat_relocSite :
    (rawNat.drop (relocOffset - 3)).take 7 = [0x48, 0x8d, 0x0d, 0x00, 0x00, 0x00, 0x00] := by
  rfl

/-! ### The `K` table

`sha256_compress.K` is a function-static `uint32_t K[64]`, emitted at
`.rodata + 0` and reached only through the `lea` above. Its 256 bytes are
recorded here because the *contents* are a precondition of the contract, not
just the permission to read them: the compiled code reads `K[t]` out of
`.rodata` and adds it to the round, so a layout whose `.rodata` held different
bytes would compute something that is not SHA-256. See
`Silmaril/Crypto/X86/Sha256O2.lean`.

`kRawNat_eq_spec` checks, by `rfl`, that these bytes are the little-endian
encodings of `Silmaril.Crypto.SHA256.Kernel.K0 … K63` — i.e. that the object's table
really is the FIPS 180-4 constant schedule and not merely 256 plausible bytes.
That check is done in the contract module, which imports the spec; this module
imports only `Process.Memory` and `X86.Basic`. -/

/-- The 256 bytes of `sha256_compress.K` at `.rodata + 0`, little-endian. -/
def kRawNat : List Nat :=
[
  0x98, 0x2f, 0x8a, 0x42, 0x91, 0x44, 0x37, 0x71, 0xcf, 0xfb, 0xc0, 0xb5,
  0xa5, 0xdb, 0xb5, 0xe9, 0x5b, 0xc2, 0x56, 0x39, 0xf1, 0x11, 0xf1, 0x59,
  0xa4, 0x82, 0x3f, 0x92, 0xd5, 0x5e, 0x1c, 0xab, 0x98, 0xaa, 0x07, 0xd8,
  0x01, 0x5b, 0x83, 0x12, 0xbe, 0x85, 0x31, 0x24, 0xc3, 0x7d, 0x0c, 0x55,
  0x74, 0x5d, 0xbe, 0x72, 0xfe, 0xb1, 0xde, 0x80, 0xa7, 0x06, 0xdc, 0x9b,
  0x74, 0xf1, 0x9b, 0xc1, 0xc1, 0x69, 0x9b, 0xe4, 0x86, 0x47, 0xbe, 0xef,
  0xc6, 0x9d, 0xc1, 0x0f, 0xcc, 0xa1, 0x0c, 0x24, 0x6f, 0x2c, 0xe9, 0x2d,
  0xaa, 0x84, 0x74, 0x4a, 0xdc, 0xa9, 0xb0, 0x5c, 0xda, 0x88, 0xf9, 0x76,
  0x52, 0x51, 0x3e, 0x98, 0x6d, 0xc6, 0x31, 0xa8, 0xc8, 0x27, 0x03, 0xb0,
  0xc7, 0x7f, 0x59, 0xbf, 0xf3, 0x0b, 0xe0, 0xc6, 0x47, 0x91, 0xa7, 0xd5,
  0x51, 0x63, 0xca, 0x06, 0x67, 0x29, 0x29, 0x14, 0x85, 0x0a, 0xb7, 0x27,
  0x38, 0x21, 0x1b, 0x2e, 0xfc, 0x6d, 0x2c, 0x4d, 0x13, 0x0d, 0x38, 0x53,
  0x54, 0x73, 0x0a, 0x65, 0xbb, 0x0a, 0x6a, 0x76, 0x2e, 0xc9, 0xc2, 0x81,
  0x85, 0x2c, 0x72, 0x92, 0xa1, 0xe8, 0xbf, 0xa2, 0x4b, 0x66, 0x1a, 0xa8,
  0x70, 0x8b, 0x4b, 0xc2, 0xa3, 0x51, 0x6c, 0xc7, 0x19, 0xe8, 0x92, 0xd1,
  0x24, 0x06, 0x99, 0xd6, 0x85, 0x35, 0x0e, 0xf4, 0x70, 0xa0, 0x6a, 0x10,
  0x16, 0xc1, 0xa4, 0x19, 0x08, 0x6c, 0x37, 0x1e, 0x4c, 0x77, 0x48, 0x27,
  0xb5, 0xbc, 0xb0, 0x34, 0xb3, 0x0c, 0x1c, 0x39, 0x4a, 0xaa, 0xd8, 0x4e,
  0x4f, 0xca, 0x9c, 0x5b, 0xf3, 0x6f, 0x2e, 0x68, 0xee, 0x82, 0x8f, 0x74,
  0x6f, 0x63, 0xa5, 0x78, 0x14, 0x78, 0xc8, 0x84, 0x08, 0x02, 0xc7, 0x8c,
  0xfa, 0xff, 0xbe, 0x90, 0xeb, 0x6c, 0x50, 0xa4, 0xf7, 0xa3, 0xf9, 0xbe,
  0xf2, 0x78, 0x71, 0xc6
]

/-- The `K` table as bytes. -/
def kBytes : List Byte := kRawNat.map (BitVec.ofNat 8)

set_option maxRecDepth 8000 in
theorem kRawNat_length : kRawNat.length = 256 := by rfl

/-- The size of `sha256_compress.K`, in bytes. -/
def kSize : Nat := 256

@[simp] theorem kBytes_length : kBytes.length = kSize := by
  rw [kBytes, List.length_map, kRawNat_length]; rfl

/-! ### Relocation -/

/-- Replace the four bytes at `offset` with the little-endian encoding of
`value`. -/
def patch32 (bytes : List Byte) (offset : Nat) (value : BitVec 32) : List Byte :=
  bytes.take offset ++
    [value.setWidth 8, (value >>> 8).setWidth 8,
     (value >>> 16).setWidth 8, (value >>> 24).setWidth 8] ++
    bytes.drop (offset + 4)

/-- The `.text` image of `sha256_compress` once loaded at `textBase` with its
`.rodata` (and hence `sha256_compress.K`) at `rodataBase`: `raw` with
`S + A - P` written into the single relocated field. -/
def image (textBase rodataBase : Word) : List Byte :=
  patch32 raw relocOffset
    ((rodataBase - textBase - BitVec.ofNat 64 (relocOffset + 4)).setWidth 32)

/-- Relocation does not change the size of the image. -/
@[simp] theorem image_length (textBase rodataBase : Word) :
    (image textBase rodataBase).length = size := by
  simp only [image, patch32, List.length_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil, raw_length, size, relocOffset]
  omega

end Silmaril.Crypto.X86.Sha256O2
