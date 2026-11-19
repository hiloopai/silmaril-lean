module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.X86.Ladder.ZlibChecksums.Defs
public import Silmaril.X86.Open.Thms

/-!
# ABI conformance of zlib's checksum functions: prototypes, C specs and code

The four checksum entry points of zlib 1.3.1, as `zlib.h` declares them (`uLong` is
`unsigned long`, `uInt` `unsigned int`, `z_size_t` `unsigned long` under `Z_SOLO` and `size_t`
otherwise; both are 8-byte unsigned under LP64, so the INTEGER-fragment prototypes coincide):

| function | prototype | `sysvInt` prototype |
| --- | --- | --- |
| `crc32_z` | `uLong crc32_z(uLong crc, const Bytef *buf, z_size_t len)` | `(u64, ptr, u64) → u64` |
| `crc32` | `uLong crc32(uLong crc, const Bytef *buf, uInt len)` | `(u64, ptr, u32) → u64` |
| `adler32_z` | `uLong adler32_z(uLong adler, const Bytef *buf, z_size_t len)` | `(u64, ptr, u64) → u64` |
| `adler32` | `uLong adler32(uLong adler, const Bytef *buf, uInt len)` | `(u64, ptr, u32) → u64` |

**C specs** (`CallSpec`), the functions' documented behaviour over the bytes they are given:
* the caller-visible object is the buffer `[buf, buf + len)` (`objects`), which the stack the ABI
  gives the callee must avoid; nothing caller-visible is written;
* a non-null buffer lies in user space (`userBuf`: `buf + len ≤ 2^47`), so that every call the
  precondition admits has room for the ABI's stack (`Conforms.enterable`);
* `crc32_z`/`crc32`: a null `buf` returns 0 (zlib's "required initial value"); otherwise the
  buffer is readable and the result is the reflected CRC-32 (`ZlibChecksums.crc32`) of its bytes from the
  incoming value's low 32 bits, zero-extended;
* `adler32_z`/`adler32`: a null `buf` returns 1; otherwise the buffer is readable and the result is
  `ZlibChecksums.adler32` of the incoming value. The precondition restricts the incoming value to valid
  Adler-32 checksums (both halves below 65521) and excludes `buf = NULL` with `len = 1` (zlib
  reads `buf[0]` before testing `buf`): outside that domain zlib's result is not a checksum, and
  the spec makes no claim.

**Code** in the pinned static `examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums` (gcc
13.3 `-O2 -DZ_SOLO`): each region with its entry offset, and `crc_table`'s 2048 bytes at
`0x4021e0` as read-only data of the CRC functions. The wrappers tail-call (`jmp`) into the `_z`
functions, so their regions span both, with the gap bytes between them.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Zlib

open Silmaril.X86 (Word Byte)
open Silmaril.C.Api (Scalar)
open Silmaril.X86.Ladder.ZlibChecksums
open Silmaril.Machine.Abi.Conformance

/-- `(u64, ptr, u64) → u64`: `crc32_z`, `adler32_z`. -/
def zProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨⟨[.uint64, .pointer, .uint64], some .uint64⟩, by decide⟩

/-- `(u64, ptr, u32) → u64`: `crc32`, `adler32`. -/
def wProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨⟨[.uint64, .pointer, .uint32], some .uint64⟩, by decide⟩

/-- The buffer of a `(u64, ptr, len)` call, as address and length. -/
def zBuf : sysvInt.V.Args zProto → Nat × Nat
  | .cons _ (.cons b (.cons n .nil)) => ((b : Word).toNat, (n : Word).toNat)

def wBuf : sysvInt.V.Args wProto → Nat × Nat
  | .cons _ (.cons b (.cons n .nil)) => ((b : Word).toNat, (n : BitVec 32).toNat)

/-- The incoming checksum. -/
def zIn : sysvInt.V.Args zProto → Word
  | .cons c _ => c

def wIn : sysvInt.V.Args wProto → Word
  | .cons c _ => c

/-- The bytes `[a, a + n)` of a memory (`TableFold.bytesAt`). -/
abbrev bytes := Silmaril.X86.Stencils.TableFold.bytesAt

/-- The buffer `(b, n)` lies in the lower canonical half of the address space (x86-64 Linux user
space, `b + n ≤ 2^47`). Without a bound the buffer could cover all memory but the stack's room, and
no call would be admitted (`Conforms.enterable`); the bound is stated, not hidden in `Admit`. -/
def userBuf (bn : Nat × Nat) : Prop := bn.1 + bn.2 ≤ 2 ^ 47

/-- A CRC spec over the buffer `(b, n)` and incoming value `c`. -/
def crcSpec {p : Silmaril.Machine.Abi.SystemV.Proto} (bufOf : sysvInt.V.Args p → Nat × Nat)
    (inOf : sysvInt.V.Args p → Word) (hr : sysvInt.V.Ret p = Word) : CallSpec sysvInt.V p where
  objects a _ x := (bufOf a).1 ≠ 0 ∧ (bufOf a).1 ≤ x ∧ x < (bufOf a).1 + (bufOf a).2
  pre a mem := (bufOf a).1 ≠ 0 → userBuf (bufOf a) ∧
    Silmaril.X86.Stencils.ByteLoop.Readable mem (bufOf a).1 (bufOf a).2
  post a s r _ := cast hr r = if (bufOf a).1 = 0 then 0
    else (Silmaril.X86.Ladder.ZlibChecksums.crc32 ((inOf a).setWidth 32) (bytes s.machine.memory (bufOf a).1 (bufOf a).2)).setWidth 64

/-- An Adler-32 spec over the buffer `(b, n)` and incoming value `c`. -/
def adlerSpec {p : Silmaril.Machine.Abi.SystemV.Proto} (bufOf : sysvInt.V.Args p → Nat × Nat)
    (inOf : sysvInt.V.Args p → Word) (hr : sysvInt.V.Ret p = Word) : CallSpec sysvInt.V p where
  objects a _ x := (bufOf a).1 ≠ 0 ∧ (bufOf a).1 ≤ x ∧ x < (bufOf a).1 + (bufOf a).2
  pre a mem := (inOf a).toNat % 65536 < Silmaril.X86.Ladder.ZlibChecksums.BASE ∧ (inOf a).toNat / 65536 % 65536 < Silmaril.X86.Ladder.ZlibChecksums.BASE ∧
    ((bufOf a).1 = 0 → (bufOf a).2 ≠ 1) ∧
    ((bufOf a).1 ≠ 0 → userBuf (bufOf a) ∧
      Silmaril.X86.Stencils.ByteLoop.Readable mem (bufOf a).1 (bufOf a).2)
  post a s r _ := cast hr r = if (bufOf a).1 = 0 then 1
    else BitVec.ofNat 64 (Silmaril.X86.Ladder.ZlibChecksums.adler32 (inOf a).toNat (bytes s.machine.memory (bufOf a).1 (bufOf a).2))

def crc32zS : CallSpec sysvInt.V zProto := crcSpec zBuf zIn rfl
def crc32S : CallSpec sysvInt.V wProto := crcSpec wBuf wIn rfl
def adler32zS : CallSpec sysvInt.V zProto := adlerSpec zBuf zIn rfl
def adler32S : CallSpec sysvInt.V wProto := adlerSpec wBuf wIn rfl

/-! ## Code in the pinned binary -/

/-- The bytes between `crc32_z`'s end (`0x401ab3`) and `crc32` (`0x401ac0`): alignment padding. -/
def crcGap : List Byte := [0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x00]

/-- The byte between `adler32_z`'s end (`0x40187f`) and `adler32` (`0x401880`). -/
def adlerGap : List Byte := [0x90]

/-- `crc_table` (2048 bytes at `0x4021e0`) as read-only data. -/
def crcData : List (Word × List Byte) := [(0x4021e0, crcTableBytes)]

/-- The image of the pinned file: its `PT_LOAD` ranges. -/
def image : List (Word × Nat) :=
  [(0x400000, 344), (0x401000, 3804), (0x402000, 2616), (0x403000, 20032)]

/-- `crc32_z`: `0x401990`, 291 bytes. -/
def crc32zCode : Code := ⟨0x401990, Silmaril.X86.Ladder.ZlibChecksums.crc32zCode, 0, 291, crcData, image⟩

/-- `crc32`: `0x401ac0`, 7 bytes, a `jmp` to `crc32_z`; the region starts at `crc32_z`. -/
def crc32Code : Code :=
  ⟨0x401990, Silmaril.X86.Ladder.ZlibChecksums.crc32zCode ++ crcGap ++ crc32WrapCode, 0x130, 7, crcData, image⟩

/-- `adler32_z`: `0x401410`, 1135 bytes. -/
def adler32zCode : Code := ⟨0x401410, Silmaril.X86.Ladder.ZlibChecksums.adler32zCode, 0, 1135, [], image⟩

/-- `adler32`: `0x401880`, 7 bytes, a `jmp` to `adler32_z`; the region starts at `adler32_z`. -/
def adler32Code : Code :=
  ⟨0x401410, Silmaril.X86.Ladder.ZlibChecksums.adler32zCode ++ adlerGap ++ adler32WrapCode, 0x470, 7, [], image⟩

end Silmaril.Machine.Abi.Conformance.Zlib

end
