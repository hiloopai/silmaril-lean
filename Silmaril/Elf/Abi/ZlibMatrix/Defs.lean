module

public import Silmaril.Elf.Abi.Defs
public import Silmaril.Machine.Abi.Conformance.Zlib.Defs
public import Silmaril.Data.Layout.Header.Zlib.Defs
public import Silmaril.Elf.Abi.ZlibLibz.Defs
public import Silmaril.Elf.Staged.Pinned.ZlibLibz1211.Bytes
public import Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz1211.Defs
public import Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc.Bytes
public import Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Gcc.Defs
public import Silmaril.Elf.Staged.Pinned.ZlibLibz131Clang.Bytes
public import Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Clang.Defs

/-! # ABI conformance rows: zlib's checksum API across versions and compilers

The zlib checksum rows of `Silmaril.Elf.Abi.Zlib` (static, `-DZ_SOLO`) and
`Silmaril.Elf.Abi.ZlibLibz` (Ubuntu's `libz.so.1.3`), extended to three more shared libraries:
the same header (the zlib 1.3.1 excerpt, hosted: `Silmaril.Data.Layout.Header.Zlib.hosted`), the
same prototypes and C specs (`Silmaril.Machine.Abi.Conformance.Zlib`), different files and code.

| binary | file | claimed | excluded, with checked reasons |
| --- | --- | --- | --- |
| `Libz1211` | `examples/elf/pinned/zlib-libz.so.1.2.11`, Ubuntu zlib1g 1:1.2.11.dfsg-2ubuntu9.2, stripped | `adler32_z`, `adler32` (a direct `jmp`) | `crc32_z` is an `STT_GNU_IFUNC` (`CodeOf` refuses it: `crc32z_ifunc`); `crc32` tail-calls it through the PLT; `crc32_combine_gen`, `crc32_combine_op` **absent** (added in zlib 1.2.12; `Absent`, checked in every table); the rest present, unclaimed |
| `Libz131Gcc` | `examples/libs/zlib/pinned/libz.so.1.3.1-gcc-13`, GCC 13.3 `-O2` from the release tarball, reproducible | `crc32_z`, `adler32_z` | `crc32`, `adler32` tail-call through the PLT (an upstream build keeps semantic interposition, unlike Ubuntu's); the rest present, unclaimed |
| `Libz131Clang` | `examples/libs/zlib/pinned/libz.so.1.3.1-clang-18`, Clang 18.1 `-O2`, same tarball | `crc32_z`, `adler32_z` | as GCC's |

Every row is on `Open9`, total, with a 256-byte frame (a declared requirement; the code's own
use is below it), at **every load base** the file admits, bound through ld.so's versioned
lookup (`crc32_z`, `adler32_z` at `ZLIB_1.2.9`; the wrappers unversioned). The header rows are
**partial** (`abi_header_sat_partial`): each binary leaves functions unclaimed. Everything but
the conformance itself is proved (`Thms`); the conformance is the open `Task`s. -/

@[expose] public section

namespace Silmaril.Elf.Abi.ZlibMatrix

open Silmaril.Elf
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib (zProto wProto crc32zS crc32S adler32zS adler32S)

/-- The header, as a shared library is built (hosted). -/
abbrev hdr : HeaderSrc := Silmaril.Data.Layout.Header.Zlib.hosted

/-- The version `ZLIB_1.2.9` as a reference requests it (`Silmaril.Elf.Abi.ZlibLibz.zlib129`). -/
abbrev zlib129 : Ver := Silmaril.Elf.Abi.ZlibLibz.zlib129

/-- ld.so's lookup in `.dynsym`: versioned for the `_z` functions, unversioned otherwise. -/
def bind : String → Binding
  | "crc32_z" => .dynsym (some zlib129)
  | "adler32_z" => .dynsym (some zlib129)
  | _ => .dynsym none

/-- The stack requirement of every row: 256 bytes below `rsp`. -/
def frame : Nat := 256

namespace Libz1211

open Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz1211
open Silmaril.Elf.Staged.Pinned.ZlibLibz1211 (F)

/-- The coverage of the header by `libz.so.1.2.11` (Ubuntu zlib1g 1:1.2.11.dfsg-2ubuntu9.2). -/
def coverage : Coverage where
  claimed := ["adler32_z", "adler32"]
  excluded :=
    [("crc32_z", .unclaimed "STT_GNU_IFUNC in .dynsym: the loader runs a resolver to choose the code, and CodeOf accepts only a plain STT_FUNC"),
    ("crc32", .unclaimed "a tail call through the PLT to the IFUNC crc32_z: the jump reads a GOT slot ld.so fills (JUMP_SLOT)"),
    ("adler32_combine", .unclaimed "present in .dynsym; no conformance row yet"),
    ("crc32_combine", .unclaimed "present in .dynsym; no conformance row yet"),
    ("get_crc_table", .unclaimed "present in .dynsym; no conformance row yet"),
    ("crc32_combine_gen", .absent "added in zlib 1.2.12: a version gap of this 1.2.11 library"),
    ("crc32_combine_op", .absent "added in zlib 1.2.12: a version gap of this 1.2.11 library"),
    ("zlibVersion", .unclaimed "present in .dynsym; no conformance row yet"),
    ("zlibCompileFlags", .unclaimed "present in .dynsym; no conformance row yet")]

/-- The implementations claimed: code (at link-time addresses), frame, spec and mode. -/
def impl : String → Option (Impl sysvInt)
  | "adler32_z" => some ⟨zProto, adler32zCode, frame, adler32zS, .total⟩
  | "adler32" => some ⟨wProto, adler32Code, frame, adler32S, .total⟩
  | _ => none

/-- **Open**: at every load base the file admits, `adler32_z` conforms on `Open9`. -/
def Task.adler32z : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt (Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa) .total hdr "adler32_z" zProto (adler32zCode.rebase base) frame adler32zS

/-- **Open**: at every load base the file admits, `adler32` conforms on `Open9`. -/
def Task.adler32 : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt (Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa) .total hdr "adler32" wProto (adler32Code.rebase base) frame adler32S

end Libz1211

namespace Libz131Gcc

open Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Gcc
open Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc (F)

/-- The coverage of the header by `libz.so.1.3.1` (GCC 13.3 -O2 build of the zlib 1.3.1 tarball). -/
def coverage : Coverage where
  claimed := ["crc32_z", "adler32_z"]
  excluded :=
    [("crc32", .unclaimed "a tail call through the PLT to crc32_z (an upstream build keeps semantic interposition): the jump reads a GOT slot ld.so fills (JUMP_SLOT)"),
    ("adler32", .unclaimed "a tail call through the PLT to adler32_z (semantic interposition): the jump reads a GOT slot ld.so fills (JUMP_SLOT)"),
    ("adler32_combine", .unclaimed "present in .dynsym; no conformance row yet"),
    ("crc32_combine", .unclaimed "present in .dynsym; no conformance row yet"),
    ("get_crc_table", .unclaimed "present in .dynsym; no conformance row yet"),
    ("crc32_combine_gen", .unclaimed "present in .dynsym; no conformance row yet"),
    ("crc32_combine_op", .unclaimed "present in .dynsym; no conformance row yet"),
    ("zlibVersion", .unclaimed "present in .dynsym; no conformance row yet"),
    ("zlibCompileFlags", .unclaimed "present in .dynsym; no conformance row yet")]

/-- The implementations claimed: code (at link-time addresses), frame, spec and mode. -/
def impl : String → Option (Impl sysvInt)
  | "crc32_z" => some ⟨zProto, crc32zCode, frame, crc32zS, .total⟩
  | "adler32_z" => some ⟨zProto, adler32zCode, frame, adler32zS, .total⟩
  | _ => none

/-- **Open**: at every load base the file admits, `crc32_z` conforms on `Open9`. -/
def Task.crc32z : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt (Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa) .total hdr "crc32_z" zProto (crc32zCode.rebase base) frame crc32zS

/-- **Open**: at every load base the file admits, `adler32_z` conforms on `Open9`. -/
def Task.adler32z : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt (Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa) .total hdr "adler32_z" zProto (adler32zCode.rebase base) frame adler32zS

end Libz131Gcc

namespace Libz131Clang

open Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Clang
open Silmaril.Elf.Staged.Pinned.ZlibLibz131Clang (F)

/-- The coverage of the header by `libz.so.1.3.1` (Clang 18.1 -O2 build of the zlib 1.3.1 tarball). -/
def coverage : Coverage where
  claimed := ["crc32_z", "adler32_z"]
  excluded :=
    [("crc32", .unclaimed "a tail call through the PLT to crc32_z (an upstream build keeps semantic interposition): the jump reads a GOT slot ld.so fills (JUMP_SLOT)"),
    ("adler32", .unclaimed "a tail call through the PLT to adler32_z (semantic interposition): the jump reads a GOT slot ld.so fills (JUMP_SLOT)"),
    ("adler32_combine", .unclaimed "present in .dynsym; no conformance row yet"),
    ("crc32_combine", .unclaimed "present in .dynsym; no conformance row yet"),
    ("get_crc_table", .unclaimed "present in .dynsym; no conformance row yet"),
    ("crc32_combine_gen", .unclaimed "present in .dynsym; no conformance row yet"),
    ("crc32_combine_op", .unclaimed "present in .dynsym; no conformance row yet"),
    ("zlibVersion", .unclaimed "present in .dynsym; no conformance row yet"),
    ("zlibCompileFlags", .unclaimed "present in .dynsym; no conformance row yet")]

/-- The implementations claimed: code (at link-time addresses), frame, spec and mode. -/
def impl : String → Option (Impl sysvInt)
  | "crc32_z" => some ⟨zProto, crc32zCode, frame, crc32zS, .total⟩
  | "adler32_z" => some ⟨zProto, adler32zCode, frame, adler32zS, .total⟩
  | _ => none

/-- **Open**: at every load base the file admits, `crc32_z` conforms on `Open9`. -/
def Task.crc32z : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt (Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa) .total hdr "crc32_z" zProto (crc32zCode.rebase base) frame crc32zS

/-- **Open**: at every load base the file admits, `adler32_z` conforms on `Open9`. -/
def Task.adler32z : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt (Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa) .total hdr "adler32_z" zProto (adler32zCode.rebase base) frame adler32zS

end Libz131Clang

end Silmaril.Elf.Abi.ZlibMatrix

end

silmaril instance silmaril.elf.abi.zlib_libz_1_2_11.adler32_z
    (title := "libz.so.1.2.11 (Ubuntu zlib1g 1:1.2.11.dfsg-2ubuntu9.2) adler32_z@@ZLIB_1.2.9 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibMatrix.hdr)
    (f := "adler32_z") (p := Silmaril.Machine.Abi.Conformance.Zlib.zProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz1211.F) (b := (.dynsym (some Silmaril.Elf.Abi.ZlibMatrix.zlib129)))
    (c := Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz1211.adler32zCode) (frame := Silmaril.Elf.Abi.ZlibMatrix.frame)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.adler32zS)
silmaril instance silmaril.elf.abi.zlib_libz_1_2_11.adler32
    (title := "libz.so.1.2.11 (Ubuntu zlib1g 1:1.2.11.dfsg-2ubuntu9.2) adler32 (base version) conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibMatrix.hdr)
    (f := "adler32") (p := Silmaril.Machine.Abi.Conformance.Zlib.wProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz1211.F) (b := (.dynsym none))
    (c := Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz1211.adler32Code) (frame := Silmaril.Elf.Abi.ZlibMatrix.frame)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.adler32S)
silmaril instance silmaril.elf.abi.zlib_libz_1_2_11.zlib_h
    (title := "libz.so.1.2.11 (Ubuntu zlib1g 1:1.2.11.dfsg-2ubuntu9.2) satisfies part of zlib.h (2 checksum functions claimed, total, at every load base) under System V AMD64 on Open9 (open)") :=
  silmaril.shapes.elf.abi_header_sat_partial (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := (Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa)) (hdr := Silmaril.Elf.Abi.ZlibMatrix.hdr)
    (cov := Silmaril.Elf.Abi.ZlibMatrix.Libz1211.coverage) (F := Silmaril.Elf.Staged.Pinned.ZlibLibz1211.F)
    (bind := Silmaril.Elf.Abi.ZlibMatrix.bind) (impl := Silmaril.Elf.Abi.ZlibMatrix.Libz1211.impl)
silmaril instance silmaril.elf.abi.zlib_libz_1_3_1_gcc.crc32_z
    (title := "libz.so.1.3.1 (GCC 13.3 -O2 build of the zlib 1.3.1 tarball) crc32_z@@ZLIB_1.2.9 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibMatrix.hdr)
    (f := "crc32_z") (p := Silmaril.Machine.Abi.Conformance.Zlib.zProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc.F) (b := (.dynsym (some Silmaril.Elf.Abi.ZlibMatrix.zlib129)))
    (c := Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Gcc.crc32zCode) (frame := Silmaril.Elf.Abi.ZlibMatrix.frame)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.crc32zS)
silmaril instance silmaril.elf.abi.zlib_libz_1_3_1_gcc.adler32_z
    (title := "libz.so.1.3.1 (GCC 13.3 -O2 build of the zlib 1.3.1 tarball) adler32_z@@ZLIB_1.2.9 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibMatrix.hdr)
    (f := "adler32_z") (p := Silmaril.Machine.Abi.Conformance.Zlib.zProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc.F) (b := (.dynsym (some Silmaril.Elf.Abi.ZlibMatrix.zlib129)))
    (c := Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Gcc.adler32zCode) (frame := Silmaril.Elf.Abi.ZlibMatrix.frame)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.adler32zS)
silmaril instance silmaril.elf.abi.zlib_libz_1_3_1_gcc.zlib_h
    (title := "libz.so.1.3.1 (GCC 13.3 -O2 build of the zlib 1.3.1 tarball) satisfies part of zlib.h (2 checksum functions claimed, total, at every load base) under System V AMD64 on Open9 (open)") :=
  silmaril.shapes.elf.abi_header_sat_partial (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := (Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa)) (hdr := Silmaril.Elf.Abi.ZlibMatrix.hdr)
    (cov := Silmaril.Elf.Abi.ZlibMatrix.Libz131Gcc.coverage) (F := Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc.F)
    (bind := Silmaril.Elf.Abi.ZlibMatrix.bind) (impl := Silmaril.Elf.Abi.ZlibMatrix.Libz131Gcc.impl)
silmaril instance silmaril.elf.abi.zlib_libz_1_3_1_clang.crc32_z
    (title := "libz.so.1.3.1 (Clang 18.1 -O2 build of the zlib 1.3.1 tarball) crc32_z@@ZLIB_1.2.9 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibMatrix.hdr)
    (f := "crc32_z") (p := Silmaril.Machine.Abi.Conformance.Zlib.zProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz131Clang.F) (b := (.dynsym (some Silmaril.Elf.Abi.ZlibMatrix.zlib129)))
    (c := Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Clang.crc32zCode) (frame := Silmaril.Elf.Abi.ZlibMatrix.frame)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.crc32zS)
silmaril instance silmaril.elf.abi.zlib_libz_1_3_1_clang.adler32_z
    (title := "libz.so.1.3.1 (Clang 18.1 -O2 build of the zlib 1.3.1 tarball) adler32_z@@ZLIB_1.2.9 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibMatrix.hdr)
    (f := "adler32_z") (p := Silmaril.Machine.Abi.Conformance.Zlib.zProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz131Clang.F) (b := (.dynsym (some Silmaril.Elf.Abi.ZlibMatrix.zlib129)))
    (c := Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Clang.adler32zCode) (frame := Silmaril.Elf.Abi.ZlibMatrix.frame)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.adler32zS)
silmaril instance silmaril.elf.abi.zlib_libz_1_3_1_clang.zlib_h
    (title := "libz.so.1.3.1 (Clang 18.1 -O2 build of the zlib 1.3.1 tarball) satisfies part of zlib.h (2 checksum functions claimed, total, at every load base) under System V AMD64 on Open9 (open)") :=
  silmaril.shapes.elf.abi_header_sat_partial (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := (Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa)) (hdr := Silmaril.Elf.Abi.ZlibMatrix.hdr)
    (cov := Silmaril.Elf.Abi.ZlibMatrix.Libz131Clang.coverage) (F := Silmaril.Elf.Staged.Pinned.ZlibLibz131Clang.F)
    (bind := Silmaril.Elf.Abi.ZlibMatrix.bind) (impl := Silmaril.Elf.Abi.ZlibMatrix.Libz131Clang.impl)
