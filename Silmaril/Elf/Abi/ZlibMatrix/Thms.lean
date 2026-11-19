module

public import Silmaril.Elf.Abi.ZlibMatrix.Defs
public import Silmaril.Elf.Abi.Zlib.Thms
public import Silmaril.Elf.Abi.ZlibLibz.Thms
import Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211
import Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc
import Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang

/-! # The zlib library matrix: theorems

PROVED (standard axioms), proofs in `Silmaril.Proofs.Elf.Abi.ZlibMatrix.*`, for each of
`Libz1211`, `Libz131Gcc`, `Libz131Clang`:

* `*_code`: the claimed code is the file's function (`CodeOf`: ld.so's versioned lookup in
  `.dynsym`, an `STT_FUNC` entry, the code bytes in the executable `PT_LOAD`, the CRC tables in
  the read-only one, the image);
* `*_untouched`: the file is x86-64 and its dynamic relocations are 8-byte types only
  (`reloc_kinds`: `GLOB_DAT`, `JUMP_SLOT`, `RELATIVE`) none of which writes the code or its data;
* `placement_zero`: each file is `ET_DYN` and admits the load base `0`;
* `*_declared`: the shared header (zlib 1.3.1 excerpt, hosted) declares each prototype;
* `coverage_check` and the exclusions: every `absent` declaration is absent from every table of
  the file in any version (`Libz1211`: `crc32_combine_gen`, `crc32_combine_op`, added in 1.2.12),
  every `unclaimed` one present;
* `Libz1211.crc32z_ifunc`: **negative**: Ubuntu's 1.2.11 exports `crc32_z` as an
  `STT_GNU_IFUNC`, and no code is that function of the file;
* `*_of`, `header_of`: each row, and the partial header row, from its open conformance task.

OPEN: the conformance of each claimed function at every load base (`Task.*`).
-/

@[expose] public section

namespace Silmaril.Elf.Abi.ZlibMatrix

open Silmaril.Elf
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib (zProto wProto)

namespace Libz1211

open Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz1211
open Silmaril.Elf.Staged.Pinned.ZlibLibz1211 (F)

theorem adler32z_code : CodeOf F (.dynsym (some zlib129)) "adler32_z" adler32zCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.adler32z_code
theorem adler32z_untouched : Untouched F adler32zCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.adler32z_untouched
theorem adler32z_declared : Declares sysvInt hdr "adler32_z" zProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.adler32z_declared
theorem adler32z_of (h : Task.adler32z) : silmaril.elf.abi.zlib_libz_1_2_11.adler32_z := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.adler32z_of h
theorem adler32_code : CodeOf F (.dynsym none) "adler32" adler32Code := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.adler32_code
theorem adler32_untouched : Untouched F adler32Code := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.adler32_untouched
theorem adler32_declared : Declares sysvInt hdr "adler32" wProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.adler32_declared
theorem adler32_of (h : Task.adler32) : silmaril.elf.abi.zlib_libz_1_2_11.adler32 := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.adler32_of h
theorem placement_zero : Placement F 0 := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.placement_zero_ok
theorem coverage_check : coverage.check sysvInt hdr = true := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.coverage_check
theorem header_of (h0 : Task.adler32z) (h1 : Task.adler32) :
    silmaril.elf.abi.zlib_libz_1_2_11.zlib_h := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.header_of h0 h1

/-- **Negative**: `crc32_z` is an `STT_GNU_IFUNC` in Ubuntu's 1.2.11; no code is the file's
`crc32_z` (the loader would choose it by running the resolver). -/
theorem crc32z_ifunc (c : Code) : ¬ CodeOf F (.dynsym (some zlib129)) "crc32_z" c :=
  Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211.crc32z_ifunc c

/-- The 1.2.11 version gap: `crc32_combine_gen` and `crc32_combine_op` are absent. -/
theorem version_gap : Absent F "crc32_combine_gen" ∧ Absent F "crc32_combine_op" :=
  ⟨Silmaril.Proofs.Elf.Abi.ZlibMatrix.absent_of Silmaril.Elf.Staged.Pinned.ZlibLibz1211.parses (by decide +kernel),
    Silmaril.Proofs.Elf.Abi.ZlibMatrix.absent_of Silmaril.Elf.Staged.Pinned.ZlibLibz1211.parses (by decide +kernel)⟩

end Libz1211

namespace Libz131Gcc

open Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Gcc
open Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc (F)

theorem crc32z_code : CodeOf F (.dynsym (some zlib129)) "crc32_z" crc32zCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.crc32z_code
theorem crc32z_untouched : Untouched F crc32zCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.crc32z_untouched
theorem crc32z_declared : Declares sysvInt hdr "crc32_z" zProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.crc32z_declared
theorem crc32z_of (h : Task.crc32z) : silmaril.elf.abi.zlib_libz_1_3_1_gcc.crc32_z := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.crc32z_of h
theorem adler32z_code : CodeOf F (.dynsym (some zlib129)) "adler32_z" adler32zCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.adler32z_code
theorem adler32z_untouched : Untouched F adler32zCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.adler32z_untouched
theorem adler32z_declared : Declares sysvInt hdr "adler32_z" zProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.adler32z_declared
theorem adler32z_of (h : Task.adler32z) : silmaril.elf.abi.zlib_libz_1_3_1_gcc.adler32_z := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.adler32z_of h
theorem placement_zero : Placement F 0 := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.placement_zero_ok
theorem coverage_check : coverage.check sysvInt hdr = true := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.coverage_check
theorem header_of (h0 : Task.crc32z) (h1 : Task.adler32z) :
    silmaril.elf.abi.zlib_libz_1_3_1_gcc.zlib_h := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc.header_of h0 h1

end Libz131Gcc

namespace Libz131Clang

open Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Clang
open Silmaril.Elf.Staged.Pinned.ZlibLibz131Clang (F)

theorem crc32z_code : CodeOf F (.dynsym (some zlib129)) "crc32_z" crc32zCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.crc32z_code
theorem crc32z_untouched : Untouched F crc32zCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.crc32z_untouched
theorem crc32z_declared : Declares sysvInt hdr "crc32_z" zProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.crc32z_declared
theorem crc32z_of (h : Task.crc32z) : silmaril.elf.abi.zlib_libz_1_3_1_clang.crc32_z := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.crc32z_of h
theorem adler32z_code : CodeOf F (.dynsym (some zlib129)) "adler32_z" adler32zCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.adler32z_code
theorem adler32z_untouched : Untouched F adler32zCode := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.adler32z_untouched
theorem adler32z_declared : Declares sysvInt hdr "adler32_z" zProto := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.adler32z_declared
theorem adler32z_of (h : Task.adler32z) : silmaril.elf.abi.zlib_libz_1_3_1_clang.adler32_z := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.adler32z_of h
theorem placement_zero : Placement F 0 := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.placement_zero_ok
theorem coverage_check : coverage.check sysvInt hdr = true := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.coverage_check
theorem header_of (h0 : Task.crc32z) (h1 : Task.adler32z) :
    silmaril.elf.abi.zlib_libz_1_3_1_clang.zlib_h := Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Clang.header_of h0 h1

end Libz131Clang

end Silmaril.Elf.Abi.ZlibMatrix

end

silmaril group silmaril.abi.zlib_libz_1_2_11
  (title := "ABI conformance: zlib's checksum API (shared zlib.h excerpt, hosted) in libz.so.1.2.11 (Ubuntu zlib1g 1:1.2.11.dfsg-2ubuntu9.2), at every load base")
  (children := [silmaril.elf.abi.zlib_libz_1_2_11.adler32_z, silmaril.elf.abi.zlib_libz_1_2_11.adler32, silmaril.elf.abi.zlib_libz_1_2_11.zlib_h])
silmaril group silmaril.abi.zlib_libz_1_3_1_gcc
  (title := "ABI conformance: zlib's checksum API (shared zlib.h excerpt, hosted) in libz.so.1.3.1 (GCC 13.3 -O2), at every load base")
  (children := [silmaril.elf.abi.zlib_libz_1_3_1_gcc.crc32_z, silmaril.elf.abi.zlib_libz_1_3_1_gcc.adler32_z, silmaril.elf.abi.zlib_libz_1_3_1_gcc.zlib_h])
silmaril group silmaril.abi.zlib_libz_1_3_1_clang
  (title := "ABI conformance: zlib's checksum API (shared zlib.h excerpt, hosted) in libz.so.1.3.1 (Clang 18.1 -O2), at every load base")
  (children := [silmaril.elf.abi.zlib_libz_1_3_1_clang.crc32_z, silmaril.elf.abi.zlib_libz_1_3_1_clang.adler32_z, silmaril.elf.abi.zlib_libz_1_3_1_clang.zlib_h])
silmaril group silmaril.abi.zlib_matrix
  (title := "ABI conformance: zlib's checksum API across versions (1.2.11, 1.3, 1.3.1) and compilers (GCC, Clang)")
  (children := [silmaril.abi.zlib, silmaril.abi.zlib_libz, silmaril.abi.zlib_libz_1_2_11,
    silmaril.abi.zlib_libz_1_3_1_gcc, silmaril.abi.zlib_libz_1_3_1_clang])
