module

public import Silmaril.Machine.Abi.Conformance.Zlib.Defs

/-!
# The rest of zlib's checksum API: prototypes and C specs

The seven declarations of the zlib 1.3.1 excerpt (`examples/headers/zlib-1.3.1/zlib.h`) beside
the four checksum entry points of `Silmaril.Machine.Abi.Conformance.Zlib`, with prototypes as
the `sysvInt` lowering gives them (`uLong` 8 bytes, `z_off_t` a signed 8-byte `long`, pointers)
and C specs from zlib's documentation:

| function | prototype | spec |
| --- | --- | --- |
| `crc32_combine` | `uLong (uLong, uLong, z_off_t)` | `crc32_combine(crc32(0,A), crc32(0,B), len(B)) = crc32(0, A ++ B)`, for every `A`, `B` (zlib.h:1758) |
| `adler32_combine` | `uLong (uLong, uLong, z_off_t)` | the same for Adler-32 with initial value 1 (zlib.h:1720) |
| `crc32_combine_gen` | `uLong (z_off_t)` | an operator `op` with `multmodp(op, crc32(0,A)) ^ crc32(0,B) = crc32(0, A ++ B)` whenever `len(B)` is the argument, 32 bits wide (zlib.h:1763) |
| `crc32_combine_op` | `uLong (uLong, uLong, uLong)` | for an operator whose low 32 bits are not 0, `multmodp(op, crc1) ^ crc2` on the low 32 bits (zlib.h:1771): with the previous row, the combination. **Partial domain**: zlib's `multmodp` never returns when the low 32 bits of `op` are 0 (its loop ends only at a set bit), so the precondition excludes those operators (`0`, `0x100000000`, …); every operator `crc32_combine_gen` returns for a nonnegative length is nonzero (`x^(8n) mod p`; on a negative length the binary returns 0) |
| `get_crc_table` | `const z_crc_t * (void)` | a pointer to 1024 readable bytes, the 256 table entries `crcEntry i` little-endian (zlib.h:1916) |
| `zlibVersion` | `const char * (void)` | a pointer to the library's version string, NUL-terminated, readable (zlib.h:220); the string is a parameter: each binary has its own |
| `zlibCompileFlags` | `uLong (void)` | its low byte encodes the sizes of `uInt`, `uLong`, `voidpf` and `z_off_t` (zlib.h:1150-1155), computed here from the data model with `z_off_t` as `long` (`flagsLow`; a large-file build makes `z_off_t` an 8-byte `off_t`: `flagsLowOff`) |

These are the 11 declarations of the zlib.h checksum **excerpt**; zlib.h also declares the
large-file variants (`crc32_combine64`, `adler32_combine64`, `crc32_combine_gen64`), which the
excerpt omits. The combine specs characterize the result by what it is for (`∀ A B`), not by zlib's algorithm;
they say nothing when the arguments are not checksums of some data. A negative length (zlib
returns a sentinel) is excluded by the precondition. `multmodp` (GF(2) multiplication modulo the
reflected CRC-32 polynomial) is the one operation the `_op`/`_gen` pair is defined through.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Zlib.Api

open Silmaril.X86 (Word Byte)
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib (bytes)
open Silmaril.X86.Ladder.ZlibChecksums (crc32 crcEntry adler32)

/-! ## Prototypes -/

/-- `(u64, u64, i64) → u64`: `crc32_combine`, `adler32_combine`. -/
def combineProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨⟨[.uint64, .uint64, .int64], some .uint64⟩, by decide⟩

/-- `(i64) → u64`: `crc32_combine_gen`. -/
def genProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨⟨[.int64], some .uint64⟩, by decide⟩

/-- `(u64, u64, u64) → u64`: `crc32_combine_op`. -/
def opProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨⟨[.uint64, .uint64, .uint64], some .uint64⟩, by decide⟩

/-- `() → ptr`: `get_crc_table`, `zlibVersion`. -/
def ptrProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨⟨[], some .pointer⟩, by decide⟩

/-- `() → u64`: `zlibCompileFlags`. -/
def flagsProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨⟨[], some .uint64⟩, by decide⟩

/-! ## Reference operations -/

/-- The low 32 bits (a `z_crc_t` taken from a `uLong`). -/
def lo32 (w : Word) : BitVec 32 := w.setWidth 32

/-- **GF(2) multiplication modulo the CRC-32 polynomial, bit-reflected** (zlib's `multmodp`,
crc32.c): for each bit of `a` from the most significant, add `b` when it is set, then multiply
`b` by `x` (shift right, reduce by `0xedb88320`). -/
def multmodp (a b : BitVec 32) : BitVec 32 :=
  ((List.range 32).foldl (fun (pb : BitVec 32 × BitVec 32) i =>
    let p := if a.getLsbD (31 - i) then pb.1 ^^^ pb.2 else pb.1
    (p, if pb.2.getLsbD 0 then (pb.2 >>> 1) ^^^ 0xedb88320#32 else pb.2 >>> 1)) (0, b)).1

/-- `z_off_t` is signed: a length is admitted when it is not negative. -/
def NonNeg (w : Word) : Prop := w.msb = false

/-- The 256 CRC-32 table entries, little-endian: what `get_crc_table` points to. -/
def crcTableBytes : List Byte :=
  (List.range 256).flatMap fun i => (List.range 4).map fun k => (crcEntry i).extractLsb' (8 * k) 8

/-- zlib's two-bit size code (zlib.h:1150): 0 for 16 bits, 1 for 32, 2 for 64, 3 otherwise. -/
def sizeCode : Option Silmaril.Data.Layout.Shape → Nat
  | some ⟨2, _⟩ => 0 | some ⟨4, _⟩ => 1 | some ⟨8, _⟩ => 2 | _ => 3

/-- **The low byte of `zlibCompileFlags`** under a data model, with `z_off_t` of shape `zOff`:
`uInt` (`unsigned int`), `uLong` (`unsigned long`), `voidpf` (a pointer) and `z_off_t` size
codes, two bits each. -/
def flagsLowOff (dm : Silmaril.Data.Layout.DataModel) (zOff : Option Silmaril.Data.Layout.Shape) : Nat :=
  sizeCode (dm.intShape .int) + 4 * sizeCode (dm.intShape .long) + 16 * sizeCode (some dm.ptr) +
    64 * sizeCode zOff

/-- **The low byte of `zlibCompileFlags`** with `z_off_t` = `long` (zconf.h without
`Z_HAVE_UNISTD_H`, or a platform where `off_t` is `long`): an assumption of this spec, exposed.
A large-file build (`_FILE_OFFSET_BITS=64` on ILP32) has an 8-byte `z_off_t`: `flagsLowOff`. -/
def flagsLow (dm : Silmaril.Data.Layout.DataModel) : Nat := flagsLowOff dm (dm.intShape .long)

/-! ## Arguments -/

def comb1 : sysvInt.V.Args combineProto → Word | .cons c _ => c
def comb2 : sysvInt.V.Args combineProto → Word | .cons _ (.cons c _) => c
def combLen : sysvInt.V.Args combineProto → Word | .cons _ (.cons _ (.cons n .nil)) => n
def genLen : sysvInt.V.Args genProto → Word | .cons n .nil => n
def op1 : sysvInt.V.Args opProto → Word | .cons c _ => c
def op2 : sysvInt.V.Args opProto → Word | .cons _ (.cons c _) => c
def opOp : sysvInt.V.Args opProto → Word | .cons _ (.cons _ (.cons o .nil)) => o

/-! ## Specs -/

/-- `crc32_combine`. -/
def crc32CombineS : CallSpec sysvInt.V combineProto where
  pre a _ := NonNeg (combLen a)
  post a _ r _ := ∀ A B : List Byte, B.length = (combLen a).toNat →
    lo32 (comb1 a) = crc32 0 A → lo32 (comb2 a) = crc32 0 B →
    (r : Word) = (crc32 0 (A ++ B)).setWidth 64

/-- `adler32_combine`. -/
def adler32CombineS : CallSpec sysvInt.V combineProto where
  pre a _ := NonNeg (combLen a)
  post a _ r _ := ∀ A B : List Byte, B.length = (combLen a).toNat →
    (comb1 a).toNat = adler32 1 A → (comb2 a).toNat = adler32 1 B →
    (r : Word).toNat = adler32 1 (A ++ B)

/-- `crc32_combine_gen`. -/
def crc32CombineGenS : CallSpec sysvInt.V genProto where
  pre a _ := NonNeg (genLen a)
  post a _ r _ := (r : Word).toNat < 2 ^ 32 ∧ ∀ A B : List Byte, B.length = (genLen a).toNat →
    multmodp (lo32 r) (crc32 0 A) ^^^ crc32 0 B = crc32 0 (A ++ B)

/-- `crc32_combine_op`, for operators whose low 32 bits are not 0 (zlib's `multmodp` does not
return on 0: the precondition is the domain on which the function is total). -/
def crc32CombineOpS : CallSpec sysvInt.V opProto where
  pre a _ := lo32 (opOp a) ≠ 0
  post a _ r _ := (r : Word) = (multmodp (lo32 (opOp a)) (lo32 (op1 a)) ^^^ lo32 (op2 a)).setWidth 64

/-- `get_crc_table`. -/
def getCrcTableS : CallSpec sysvInt.V ptrProto where
  pre _ _ := True
  post _ _ r t := t.machine.memory.Permitted .read (r : Word).toNat 1024 ∧
    bytes t.machine.memory (r : Word).toNat 1024 = crcTableBytes

/-- `zlibVersion` of a library whose version string is `v`. -/
def zlibVersionS (v : String) : CallSpec sysvInt.V ptrProto where
  pre _ _ := True
  post _ _ r t := t.machine.memory.Permitted .read (r : Word).toNat (v.utf8ByteSize + 1) ∧
    bytes t.machine.memory (r : Word).toNat (v.utf8ByteSize + 1) =
      v.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat) ++ [0]

/-- `zlibCompileFlags` under the data model `dm`. -/
def zlibCompileFlagsS (dm : Silmaril.Data.Layout.DataModel) : CallSpec sysvInt.V flagsProto where
  pre _ _ := True
  post _ _ r _ := (r : Word).toNat % 256 = flagsLow dm

end Silmaril.Machine.Abi.Conformance.Zlib.Api

end
