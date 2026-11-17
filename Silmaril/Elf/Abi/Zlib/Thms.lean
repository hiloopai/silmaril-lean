module

public import Silmaril.Elf.Abi.Zlib.Defs
public import Silmaril.Elf.Abi.Thms
import Silmaril.Proofs.Elf.Abi.ZlibRows

/-! # zlib-checksums rows: what is proved, what is open

PROVED (standard axioms), proofs in `Silmaril.Proofs.Elf.Abi.{Zlib,ZlibRows}`:

* `crc32z_code`, `crc32_code`, `adler32z_code`, `adler32_code`: the code is the file's
  (`CodeOf`: `.symtab` `STT_FUNC` symbol at the entry with the function's size, the code bytes
  mapped read-only executable, `crc_table` mapped read-only, the image the file's `PT_LOAD`s);
* `crc32z_declared` …: the shared zlib.h excerpt (`Z_SOLO`) declares each prototype;
* `coverage_check`: the coverage is checked against the header;
* `crc32z_of`, `crc32_of`, `adler32z_of`, `adler32_of`, `header_of`: **each row follows from its
  open conformance task** (`Task.crc32z` …), the rest being proved (no dynamic relocation, the
  only load base 0, the absent functions absent, the unclaimed ones present).

OPEN: `Task.crc32z`, `Task.crc32`, `Task.adler32z`, `Task.adler32` (conformance on `Open9`).
-/

@[expose] public section

namespace Silmaril.Elf.Abi.Zlib

open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib
open Silmaril.Elf.Staged.Pinned.ZlibChecksums (F)

theorem crc32z_code : CodeOf F .symtab "crc32_z" crc32zCode := Silmaril.Proofs.Elf.Abi.Zlib.crc32z_code
theorem crc32_code : CodeOf F .symtab "crc32" crc32Code := Silmaril.Proofs.Elf.Abi.Zlib.crc32_code
theorem adler32z_code : CodeOf F .symtab "adler32_z" adler32zCode := Silmaril.Proofs.Elf.Abi.Zlib.adler32z_code
theorem adler32_code : CodeOf F .symtab "adler32" adler32Code := Silmaril.Proofs.Elf.Abi.Zlib.adler32_code

theorem crc32z_declared : Declares sysvInt hdr "crc32_z" zProto := Silmaril.Proofs.Elf.Abi.ZlibRows.crc32z_declared
theorem crc32_declared : Declares sysvInt hdr "crc32" wProto := Silmaril.Proofs.Elf.Abi.ZlibRows.crc32_declared
theorem adler32z_declared : Declares sysvInt hdr "adler32_z" zProto := Silmaril.Proofs.Elf.Abi.ZlibRows.adler32z_declared
theorem adler32_declared : Declares sysvInt hdr "adler32" wProto := Silmaril.Proofs.Elf.Abi.ZlibRows.adler32_declared

theorem coverage_check : coverage.check sysvInt hdr = true := Silmaril.Proofs.Elf.Abi.ZlibRows.coverage_check

theorem crc32z_of (h : Task.crc32z) : silmaril.elf.abi.zlib_checksums.crc32_z :=
  Silmaril.Proofs.Elf.Abi.ZlibRows.crc32z_of h
theorem crc32_of (h : Task.crc32) : silmaril.elf.abi.zlib_checksums.crc32 :=
  Silmaril.Proofs.Elf.Abi.ZlibRows.crc32_of h
theorem adler32z_of (h : Task.adler32z) : silmaril.elf.abi.zlib_checksums.adler32_z :=
  Silmaril.Proofs.Elf.Abi.ZlibRows.adler32z_of h
theorem adler32_of (h : Task.adler32) : silmaril.elf.abi.zlib_checksums.adler32 :=
  Silmaril.Proofs.Elf.Abi.ZlibRows.adler32_of h

theorem header_of (h1 : Task.crc32z) (h2 : Task.crc32) (h3 : Task.adler32z) (h4 : Task.adler32) :
    silmaril.elf.abi.zlib_checksums.zlib_h :=
  Silmaril.Proofs.Elf.Abi.ZlibRows.header_of h1 h2 h3 h4

end Silmaril.Elf.Abi.Zlib

end

silmaril group silmaril.abi.zlib
  (title := "ABI conformance: zlib's checksum API (shared zlib.h excerpt) in the pinned zlib-checksums")
  (children := [silmaril.elf.abi.zlib_checksums.crc32_z, silmaril.elf.abi.zlib_checksums.crc32,
    silmaril.elf.abi.zlib_checksums.adler32_z, silmaril.elf.abi.zlib_checksums.adler32,
    silmaril.elf.abi.zlib_checksums.zlib_h])
