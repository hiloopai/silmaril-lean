module

public import Silmaril.X86.Ladder.Pinned.Defs
public import Silmaril.X86.Ladder.Pinned.MemLoops
public import Silmaril.X86.Ladder.Pinned.ZlibChecksums
public import Silmaril.X86.Ladder.LibMini.Transcript
public import Silmaril.X86.Ladder.LibMini.StrlenTranscript
public import Silmaril.X86.Ladder.ZlibChecksums.Defs
import Silmaril.Proofs.X86.Ladder.Pinned

/-! # Binary ties: every transcribed ladder literal is a slice of a pinned executable

For each ladder rung, the literals below are proved, by kernel evaluation of the public LPS
loader on the committed executable, to be the bytes loaded at their addresses
(`LoadedAt exe perms addr code`, `Pinned/Defs.lean`). One `decide +kernel` per rung
(`checkAll`) parses the file once and checks all its slices.

| rung | pinned file | literals |
| --- | --- | --- |
| 02 | `02-mem-loops/pinned/mem-loops` | `LibMini.Transcript.region`, `LibMini.StrlenTranscript.region` |
| 03 | `03-zlib-checksums/pinned/zlib-checksums` | `crc32zCode`, `adler32zCode`, `crc32WrapCode`, `adler32WrapCode`, `crcTableBytes` (`.rodata`) |

Every literal derived from these by `take`/`drop` (`LibMini.memcpyCode`, `memsetCode`,
`strlenCode`) is therefore a slice of the pinned file too; `LibMini.memcpyCode_eq`, … give the
offsets.

**Not vacuous** (`rejects_*`): the same literal one byte off, in the wrong segment kind,
against the other rung's file, or with one byte flipped is rejected.
-/

@[expose] public section

namespace Silmaril.X86.Ladder.Pinned

open Silmaril.X86.Link
open Silmaril.X86.Ladder

theorem check_sound {exe : Blob} {perms : String} {addr : Nat} {code : List (BitVec 8)}
    (h : check exe perms addr code = true) : LoadedAt exe perms addr code :=
  Silmaril.Proofs.X86.Ladder.Pinned.check_sound h

theorem checkAll_sound {exe : Blob} {slices : List (String × Nat × List (BitVec 8))}
    (h : checkAll exe slices = true) {perms : String} {addr : Nat} {code : List (BitVec 8)}
    (mem : (perms, addr, code) ∈ slices) : LoadedAt exe perms addr code :=
  Silmaril.Proofs.X86.Ladder.Pinned.checkAll_sound h mem

/-! ## Rung 02 -/

def memLoopsSlices : List (String × Nat × List (BitVec 8)) :=
  [("rx", LibMini.Transcript.region.base, LibMini.Transcript.region.bytes),
   ("rx", LibMini.StrlenTranscript.region.base, LibMini.StrlenTranscript.region.bytes)]

set_option maxRecDepth 100000 in
theorem memLoops_checked : checkAll MemLoops.exe memLoopsSlices = true := by decide +kernel

theorem memLoops_region :
    LoadedAt MemLoops.exe "rx" LibMini.Transcript.region.base LibMini.Transcript.region.bytes :=
  checkAll_sound memLoops_checked (by simp [memLoopsSlices])

theorem memLoops_strlen :
    LoadedAt MemLoops.exe "rx" LibMini.StrlenTranscript.region.base
      LibMini.StrlenTranscript.region.bytes :=
  checkAll_sound memLoops_checked (by simp [memLoopsSlices])

/-! ## Rung 03 -/

def zlibSlices : List (String × Nat × List (BitVec 8)) :=
  [("rx", ZlibChecksums.crc32zAddr.toNat, ZlibChecksums.crc32zCode),
   ("rx", 0x401410, ZlibChecksums.adler32zCode),
   ("rx", 0x401ac0, ZlibChecksums.crc32WrapCode),
   ("rx", 0x401880, ZlibChecksums.adler32WrapCode),
   ("r", ZlibChecksums.crcTblAddr.toNat, ZlibChecksums.crcTableBytes)]

set_option maxRecDepth 100000 in
theorem zlib_checked : checkAll ZlibChecksums.exe zlibSlices = true := by decide +kernel

theorem zlib_crc32z :
    LoadedAt ZlibChecksums.exe "rx" ZlibChecksums.crc32zAddr.toNat ZlibChecksums.crc32zCode :=
  checkAll_sound zlib_checked (by simp [zlibSlices])

theorem zlib_adler32z : LoadedAt ZlibChecksums.exe "rx" 0x401410 ZlibChecksums.adler32zCode :=
  checkAll_sound zlib_checked (by simp [zlibSlices])

theorem zlib_crc32Wrap : LoadedAt ZlibChecksums.exe "rx" 0x401ac0 ZlibChecksums.crc32WrapCode :=
  checkAll_sound zlib_checked (by simp [zlibSlices])

theorem zlib_adler32Wrap :
    LoadedAt ZlibChecksums.exe "rx" 0x401880 ZlibChecksums.adler32WrapCode :=
  checkAll_sound zlib_checked (by simp [zlibSlices])

theorem zlib_crcTable :
    LoadedAt ZlibChecksums.exe "r" ZlibChecksums.crcTblAddr.toNat ZlibChecksums.crcTableBytes :=
  checkAll_sound zlib_checked (by simp [zlibSlices])

/-! ## The check is not vacuous -/

set_option maxRecDepth 100000 in
theorem rejects_shifted :
    check ZlibChecksums.exe "rx" 0x401ac1 ZlibChecksums.crc32WrapCode = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rejects_wrong_perms :
    check ZlibChecksums.exe "r" 0x401ac0 ZlibChecksums.crc32WrapCode = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rejects_wrong_file :
    check MemLoops.exe "rx" 0x401ac0 ZlibChecksums.crc32WrapCode = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rejects_flipped :
    check ZlibChecksums.exe "rx" 0x401ac0 (ZlibChecksums.crc32WrapCode.set 1 0xd3) = false := by
  decide +kernel

end Silmaril.X86.Ladder.Pinned
