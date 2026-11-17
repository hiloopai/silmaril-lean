module

public import Silmaril.Elf.Abi.Defs
public import Silmaril.Elf.Staged.Pinned.ZlibChecksums.Bytes
public import Silmaril.Machine.Abi.Conformance.Zlib.Defs
public import Silmaril.Data.Layout.Header.Zlib.Defs

/-! # ABI conformance rows: zlib's checksum API and the pinned static `zlib-checksums`

The header is the shared zlib 1.3.1 excerpt (`examples/headers/zlib-1.3.1/zlib.h`) in its
`Z_SOLO` configuration (`Silmaril.Data.Layout.Header.Zlib.solo`), as `zlib-checksums` is built
(`-DZ_SOLO`). The file is `examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums` (gcc 13.3
`-O2`, static, `.symtab`). The prototypes, specs and code are
`Silmaril.Machine.Abi.Conformance.Zlib`.

| row | machine | mode, frame | status |
| --- | --- | --- | --- |
| `silmaril.elf.abi.zlib_checksums.crc32_z` | `Open9` | total, 0 | open (`Task.crc32z`) |
| `silmaril.elf.abi.zlib_checksums.crc32` | `Open9` | total, 0 | open (`Task.crc32`) |
| `silmaril.elf.abi.zlib_checksums.adler32_z` | `Open9` | total, 96 | open (`Task.adler32z`) |
| `silmaril.elf.abi.zlib_checksums.adler32` | `Open9` | total, 96 | open (`Task.adler32`) |
| `silmaril.elf.abi.zlib_checksums.zlib_h` | `Open9` | partial header | open (from the four) |

Everything but the conformance itself is proved (`Thms`): the code is the file's (`CodeOf`),
untouched by relocations, at the file's only load base; the header declares each prototype;
the coverage is checked, with the absent functions absent and the unclaimed ones present. All rows
are on `Open9`: `adler32_z`'s code uses `Ext9` forms (its existing contract is on `Open9`), and
`Open9` also decodes the CRC code (whose existing contract is on `Open`); one machine lets the
header row claim all four. The frame of 96 bytes is the stack `adler32_z` writes below `rsp` (its red zone use).
The existing contracts (`Silmaril.X86.Ladder.ZlibChecksums`) are total (`Spec.Total`), not
first-return, and assume more than these rows admit, so they do not close the rows. -/

@[expose] public section

namespace Silmaril.Elf.Abi.Zlib

open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib

/-- The header, as the binary is built. -/
abbrev hdr : HeaderSrc := Silmaril.Data.Layout.Header.Zlib.solo

/-- The coverage of the excerpt by `zlib-checksums`: the four checksum entry points claimed; the
functions the static link left out absent; the rest present and unclaimed. -/
def coverage : Coverage where
  claimed := ["crc32_z", "crc32", "adler32_z", "adler32"]
  excluded :=
    [("adler32_combine", .unclaimed "present; no conformance row yet"),
     ("crc32_combine", .unclaimed "present; no conformance row yet"),
     ("get_crc_table", .unclaimed "present; no conformance row yet"),
     ("crc32_combine_gen", .absent "not linked into zlib-checksums"),
     ("crc32_combine_op", .absent "not linked into zlib-checksums"),
     ("zlibVersion", .absent "not linked into zlib-checksums (zutil.c not built)"),
     ("zlibCompileFlags", .absent "not linked into zlib-checksums (zutil.c not built)")]

/-- The implementations claimed: code, frame, spec and mode. -/
def impl : String → Option (Impl sysvInt)
  | "crc32_z" => some ⟨zProto, crc32zCode, 0, crc32zS, .total⟩
  | "crc32" => some ⟨wProto, crc32Code, 0, crc32S, .total⟩
  | "adler32_z" => some ⟨zProto, adler32zCode, 96, adler32zS, .total⟩
  | "adler32" => some ⟨wProto, adler32Code, 96, adler32S, .total⟩
  | _ => none

/-- The `.symtab` binding of every name. -/
def bind (_ : String) : Binding := .symtab

/-- **Open**: `crc32_z` conforms on `Open9` (the file part is proved, `Thms.crc32z_of`). -/
def Task.crc32z : Prop :=
  Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "crc32_z" zProto crc32zCode 0 crc32zS

def Task.crc32 : Prop :=
  Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "crc32" wProto crc32Code 0 crc32S

def Task.adler32z : Prop :=
  Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "adler32_z" zProto adler32zCode 96 adler32zS

def Task.adler32 : Prop :=
  Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "adler32" wProto adler32Code 96 adler32S

end Silmaril.Elf.Abi.Zlib

end

silmaril instance silmaril.elf.abi.zlib_checksums.crc32_z
    (title := "zlib-checksums crc32_z conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it: total, frame 0 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.Zlib.hdr)
    (f := "crc32_z") (p := Silmaril.Machine.Abi.Conformance.Zlib.zProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibChecksums.F) (b := .symtab)
    (c := Silmaril.Machine.Abi.Conformance.Zlib.crc32zCode) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.crc32zS)
silmaril instance silmaril.elf.abi.zlib_checksums.crc32
    (title := "zlib-checksums crc32 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it: total, frame 0 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.Zlib.hdr)
    (f := "crc32") (p := Silmaril.Machine.Abi.Conformance.Zlib.wProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibChecksums.F) (b := .symtab)
    (c := Silmaril.Machine.Abi.Conformance.Zlib.crc32Code) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.crc32S)
silmaril instance silmaril.elf.abi.zlib_checksums.adler32_z
    (title := "zlib-checksums adler32_z conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it: total, frame 96 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.Zlib.hdr)
    (f := "adler32_z") (p := Silmaril.Machine.Abi.Conformance.Zlib.zProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibChecksums.F) (b := .symtab)
    (c := Silmaril.Machine.Abi.Conformance.Zlib.adler32zCode) (frame := 96)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.adler32zS)
silmaril instance silmaril.elf.abi.zlib_checksums.adler32
    (title := "zlib-checksums adler32 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it: total, frame 96 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.Zlib.hdr)
    (f := "adler32") (p := Silmaril.Machine.Abi.Conformance.Zlib.wProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibChecksums.F) (b := .symtab)
    (c := Silmaril.Machine.Abi.Conformance.Zlib.adler32Code) (frame := 96)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.adler32S)
silmaril instance silmaril.elf.abi.zlib_checksums.zlib_h
    (title := "zlib-checksums satisfies part of zlib.h (4 checksum functions claimed, total) under System V AMD64 on Open9 (open)") :=
  silmaril.shapes.elf.abi_header_sat_partial (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open9.isa) (hdr := Silmaril.Elf.Abi.Zlib.hdr)
    (cov := Silmaril.Elf.Abi.Zlib.coverage) (F := Silmaril.Elf.Staged.Pinned.ZlibChecksums.F)
    (bind := Silmaril.Elf.Abi.Zlib.bind) (impl := Silmaril.Elf.Abi.Zlib.impl)
