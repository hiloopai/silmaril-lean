module

public import Silmaril.Elf.Abi.ZlibLibz.Defs
public import Silmaril.Elf.Abi.Thms
import Silmaril.Proofs.Elf.Abi.ZlibLibzRows

/-! # libz.so.1.3 rows: what is proved, what is open

PROVED (standard axioms), proofs in `Silmaril.Proofs.Elf.Abi.{ZlibLibz,ZlibLibzRows}`:

* `crc32z_code`, `crc32_code`, `adler32z_code`, `adler32_code`: the code is the file's
  (`CodeOf`): ld.so's lookup in `.dynsym` (`ZLIB_1.2.9` for the `_z` functions, unversioned for
  the base-version `crc32`, `adler32`) finds an `STT_FUNC` at the entry with the function's size;
  the code bytes are mapped read-only executable; the read-only `PT_LOAD` at `0x14000` (CRC
  tables) is mapped read-only; the image is the file's four `PT_LOAD`s;
* `crc32z_unversioned`, `adler32z_unversioned`: without `ZLIB_1.2.9`, ld.so's lookup of a `_z`
  function has no answer (so the version in the binding is needed);
* `crc32z_untouched` …: no dynamic relocation (`.rela.dyn`, `.rela.plt`) writes the code or the
  read-only segment. The file is x86-64 and its relocations are `RELATIVE`, `JUMP_SLOT`
  and `GLOB_DAT` only (`reloc_kinds`), 8 bytes each by `relocWidth` (any other type would be refused);
* `placement_zero`: the file (`ET_DYN`) admits the load base `0`;
* `crc32z_declared` …: the shared zlib.h excerpt (hosted) declares each prototype;
* `coverage_check`: the coverage is checked against the header;
* `crc32z_of`, `crc32_of`, `adler32z_of`, `adler32_of`, `header_of`: **each row follows from its
  open conformance task** (`Task.crc32z` …: conformance at every admitted load base), the rest
  being proved (the seven unclaimed functions present in `.dynsym`).

OPEN: `Task.crc32z`, `Task.crc32`, `Task.adler32z`, `Task.adler32` (conformance on `Open9` of the
code rebased to every load base the file admits).
-/

@[expose] public section

namespace Silmaril.Elf.Abi.ZlibLibz

open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib (zProto wProto)
open Silmaril.Machine.Abi.Conformance.ZlibLibz
open Silmaril.Elf.Staged.Pinned.ZlibLibz (F)

theorem crc32z_code : CodeOf F (.dynsym (some zlib129)) "crc32_z" crc32zCode :=
  Silmaril.Proofs.Elf.Abi.ZlibLibz.crc32z_code
theorem crc32_code : CodeOf F (.dynsym none) "crc32" crc32Code :=
  Silmaril.Proofs.Elf.Abi.ZlibLibz.crc32_code
theorem adler32z_code : CodeOf F (.dynsym (some zlib129)) "adler32_z" adler32zCode :=
  Silmaril.Proofs.Elf.Abi.ZlibLibz.adler32z_code
theorem adler32_code : CodeOf F (.dynsym none) "adler32" adler32Code :=
  Silmaril.Proofs.Elf.Abi.ZlibLibz.adler32_code

/-- The version is needed: an unversioned lookup of `crc32_z` or `adler32_z` has no answer. -/
theorem crc32z_unversioned (d : Option Silmaril.Elf.Def) :
    ¬ Silmaril.Elf.Lookup F ((Binding.dynsym none).sel "crc32_z") d :=
  Silmaril.Proofs.Elf.Abi.ZlibLibz.crc32z_unversioned d
theorem adler32z_unversioned (d : Option Silmaril.Elf.Def) :
    ¬ Silmaril.Elf.Lookup F ((Binding.dynsym none).sel "adler32_z") d :=
  Silmaril.Proofs.Elf.Abi.ZlibLibz.adler32z_unversioned d

theorem crc32z_untouched : Untouched F crc32zCode := Silmaril.Proofs.Elf.Abi.ZlibLibz.crc32z_untouched
theorem crc32_untouched : Untouched F crc32Code := Silmaril.Proofs.Elf.Abi.ZlibLibz.crc32_untouched
theorem adler32z_untouched : Untouched F adler32zCode := Silmaril.Proofs.Elf.Abi.ZlibLibz.adler32z_untouched
theorem adler32_untouched : Untouched F adler32Code := Silmaril.Proofs.Elf.Abi.ZlibLibz.adler32_untouched

theorem placement_zero : Placement F 0 := Silmaril.Proofs.Elf.Abi.ZlibLibz.placement_zero_ok

theorem crc32z_declared : Declares sysvInt hdr "crc32_z" zProto := Silmaril.Proofs.Elf.Abi.ZlibLibzRows.crc32z_declared
theorem crc32_declared : Declares sysvInt hdr "crc32" wProto := Silmaril.Proofs.Elf.Abi.ZlibLibzRows.crc32_declared
theorem adler32z_declared : Declares sysvInt hdr "adler32_z" zProto := Silmaril.Proofs.Elf.Abi.ZlibLibzRows.adler32z_declared
theorem adler32_declared : Declares sysvInt hdr "adler32" wProto := Silmaril.Proofs.Elf.Abi.ZlibLibzRows.adler32_declared

theorem coverage_check : coverage.check sysvInt hdr = true := Silmaril.Proofs.Elf.Abi.ZlibLibzRows.coverage_check

theorem crc32z_of (h : Task.crc32z) : silmaril.elf.abi.zlib_libz.crc32_z :=
  Silmaril.Proofs.Elf.Abi.ZlibLibzRows.crc32z_of h
theorem crc32_of (h : Task.crc32) : silmaril.elf.abi.zlib_libz.crc32 :=
  Silmaril.Proofs.Elf.Abi.ZlibLibzRows.crc32_of h
theorem adler32z_of (h : Task.adler32z) : silmaril.elf.abi.zlib_libz.adler32_z :=
  Silmaril.Proofs.Elf.Abi.ZlibLibzRows.adler32z_of h
theorem adler32_of (h : Task.adler32) : silmaril.elf.abi.zlib_libz.adler32 :=
  Silmaril.Proofs.Elf.Abi.ZlibLibzRows.adler32_of h

theorem header_of (h1 : Task.crc32z) (h2 : Task.crc32) (h3 : Task.adler32z) (h4 : Task.adler32) :
    silmaril.elf.abi.zlib_libz.zlib_h :=
  Silmaril.Proofs.Elf.Abi.ZlibLibzRows.header_of h1 h2 h3 h4

end Silmaril.Elf.Abi.ZlibLibz

end

silmaril group silmaril.abi.zlib_libz
  (title := "ABI conformance: zlib's checksum API (shared zlib.h excerpt, hosted) in Ubuntu's libz.so.1.3, at every load base")
  (children := [silmaril.elf.abi.zlib_libz.crc32_z, silmaril.elf.abi.zlib_libz.crc32,
    silmaril.elf.abi.zlib_libz.adler32_z, silmaril.elf.abi.zlib_libz.adler32,
    silmaril.elf.abi.zlib_libz.zlib_h])
