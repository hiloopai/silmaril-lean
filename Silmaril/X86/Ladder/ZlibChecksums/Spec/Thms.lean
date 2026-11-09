module

public import Silmaril.X86.Ladder.ZlibChecksums.Spec.Defs
public import Silmaril.X86.Stencils.TableFold.Thms
public import Silmaril.X86.Stencils.AccumFold.Thms
import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Crc

/-!
# zlib checksums: reference theorems

**CRC-32**
* `crcByte_table`: one bitwise byte step is a shift and a table lookup,
  `crcByte c b = (c >>> 8) ^^^ crcEntry ((c ^ b) & 0xff)` (linearity of the shift register);
* `step_crcT`, `fold_crcT`: the table-fold stencil's 64-bit `step`/`fold` with the table
  `crcT` computes the bitwise CRC (zero-extended);
* `crcTable_correct`: every entry of the table transcribed from the binary is `crcEntry i`
  (kernel `decide`); `tableAt_of_readBytes`: a memory that holds those 2048 bytes satisfies the
  stencil's `TableAt`;
* `crc32_check`, `crcEntry_one`: the published check value `crc32(0, "123456789") = 0xcbf43926`
  and `crc_table[1] = 0x77073096`, as the rung's self-test checks.

**Adler-32**
* `adler32Chunked_eq`: zlib's deferred reduction (any input, `NMAX` chunks) equals the per-byte
  reference;
* `nmax_bound`, `nmax_tight`: `NMAX = 5552` keeps the raw sums of one chunk below `2^32`
  (zlib's comment "the largest n such that 255n(n+1)/2 + (n+1)(BASE-1) <= 2^32-1"), and
  `5553` does not;
* `adler32_check`: `adler32(1, "Wikipedia") = 0x11e60398`.
-/

@[expose] public section

namespace Silmaril.X86.Ladder.ZlibChecksums

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Stencils

theorem crcByte_table (c : BitVec 32) (b : Byte) :
    crcByte c b = (c >>> 8) ^^^ crcEntry (c.setWidth 8 ^^^ b).toNat :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.crcByte_table c b

theorem step_crcT (c : BitVec 32) (b : Byte) :
    TableFold.step crcT (c.setWidth 64) b = (crcByte c b).setWidth 64 :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.step_crcT c b

theorem fold_crcT (c : BitVec 32) (bs : List Byte) :
    TableFold.fold crcT (c.setWidth 64) bs = (bs.foldl crcByte c).setWidth 64 :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.fold_crcT c bs

theorem crcTable_correct :
    ∀ i < 256, Silmaril.X86.Ext.leValue ((crcTableBytes.drop (8 * i)).take 8) = (crcEntry i).toNat :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.crcTable_correct

theorem tableAt_of_readBytes {mem : Memory} {tbl : Nat}
    (h : mem.readBytes tbl 2048 = some crcTableBytes) : TableFold.TableAt mem tbl 256 crcT :=
  Silmaril.Proofs.X86.Ladder.ZlibChecksums.tableAt_of_readBytes h

theorem crcEntry_one : crcEntry 1 = 0x77073096#32 := by decide +kernel

/-- The ASCII bytes of `"123456789"`. -/
def nine : List Byte := [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

theorem crc32_check : crc32 0 nine = 0xcbf43926#32 := by decide +kernel

/-- The ASCII bytes of `"Wikipedia"`. -/
def wikipedia : List Byte := [0x57, 0x69, 0x6b, 0x69, 0x70, 0x65, 0x64, 0x69, 0x61]

theorem adler32_check : adler32 1 wikipedia = 0x11e60398 := by decide +kernel

theorem adler32Chunked_eq (a : Nat) (bs : List Byte) : adler32Chunked a bs = adler32 a bs := by
  simp only [adler32Chunked, adler32, AccumFold.chunked_eq_modFold, adlerStart]
  congr 2
  simp [AccumFold.red]

theorem nmax_bound : AccumFold.RawBound BASE NMAX 32 := by
  unfold AccumFold.RawBound BASE NMAX; decide

theorem nmax_tight : ¬ AccumFold.RawBound BASE (NMAX + 1) 32 := by
  unfold AccumFold.RawBound BASE NMAX; decide

end Silmaril.X86.Ladder.ZlibChecksums
