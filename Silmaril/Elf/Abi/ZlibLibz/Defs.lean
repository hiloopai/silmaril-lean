module

public import Silmaril.Elf.Abi.Defs
public import Silmaril.Elf.Staged.Pinned.ZlibLibz.Bytes
public import Silmaril.Machine.Abi.Conformance.Zlib.Defs
public import Silmaril.Machine.Abi.Conformance.ZlibLibz.Defs
public import Silmaril.Data.Layout.Header.Zlib.Defs

/-! # ABI conformance rows: zlib's checksum API and Ubuntu's `libz.so.1.3`

The second binary of the zlib checksum header. The header is the same zlib 1.3.1 excerpt
(`examples/headers/zlib-1.3.1/zlib.h`) as the static rows (`Silmaril.Elf.Abi.Zlib`), in its
**hosted** configuration (`Silmaril.Data.Layout.Header.Zlib.hosted`: `z_size_t` is `size_t`), as
a distribution library is built; the prototypes and C specs are the same values
(`Silmaril.Machine.Abi.Conformance.Zlib`). The file is the pinned
`examples/elf/pinned/zlib-libz.so.1.3` (zlib 1.3, Ubuntu zlib1g 1:1.3.dfsg-3.1ubuntu2.3,
`ET_DYN`, stripped: `.dynsym` only, versioned); its code is
`Silmaril.Machine.Abi.Conformance.ZlibLibz`.

| row | machine | mode, frame | binding | status |
| --- | --- | --- | --- | --- |
| `silmaril.elf.abi.zlib_libz.crc32_z` | `Open9` | total, 256 | `.dynsym`, `ZLIB_1.2.9` | open (`Task.crc32z`) |
| `silmaril.elf.abi.zlib_libz.crc32` | `Open9` | total, 256 | `.dynsym`, unversioned | open (`Task.crc32`) |
| `silmaril.elf.abi.zlib_libz.adler32_z` | `Open9` | total, 256 | `.dynsym`, `ZLIB_1.2.9` | open (`Task.adler32z`) |
| `silmaril.elf.abi.zlib_libz.adler32` | `Open9` | total, 256 | `.dynsym`, unversioned | open (`Task.adler32`) |
| `silmaril.elf.abi.zlib_libz.zlib_h` | `Open9` | partial header | | open (from the four) |

**Bindings.** `crc32_z` and `adler32_z` are defined as `…@@ZLIB_1.2.9` (version index 14), so a
reference built against this library asks ld.so for version `ZLIB_1.2.9` with its ELF hash
(`zlib129`). `crc32` and `adler32` have the base version (index 1, `*global*`): the static
linker records no version need for a base-version definition, and ld.so looks such a reference
up unversioned (`ver = none`; `File.checkMatch` accepts index 1 without a version).

**Every load base.** The file is `ET_DYN`: it admits every page-aligned base that keeps its
`PT_LOAD`s below `2^47` (`Placement`). Each open task is the whole quantified statement: the
rebased code (`Code.rebase`) conforms at **every** admitted base. Nothing claims a result at
link-time addresses only. The code is position independent (`%rip`-relative table addresses) and
no dynamic relocation writes it or the read-only segment (`Untouched`, proved), so the rebased
code has the same bytes.

**Frame.** 256 bytes for every function: a declared stack requirement of the rows (the callee is
given 256 bytes below `rsp`), not a measured bound. The code's own use, from its listing, is
below it (`crc32_z` 64 bytes below the entry `rsp`, `adler32_z` 104).

Everything but the conformance itself is proved (`Thms`). -/

@[expose] public section

namespace Silmaril.Elf.Abi.ZlibLibz

open Silmaril.Elf
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib (zProto wProto crc32zS crc32S adler32zS adler32S)
open Silmaril.Machine.Abi.Conformance.ZlibLibz
open Silmaril.Elf.Staged.Pinned.ZlibLibz (F)

/-- The header, as a hosted library is built. -/
abbrev hdr : HeaderSrc := Silmaril.Data.Layout.Header.Zlib.hosted

/-- The version `ZLIB_1.2.9` as a reference requests it: name, ELF hash (`vna_hash`), not hidden. -/
def zlib129 : Ver := ⟨nameOf "ZLIB_1.2.9", 136832457, false⟩

/-- How each function is found: ld.so's lookup in `.dynsym`, versioned for the `_z` functions,
unversioned for the base-version ones. -/
def bind : String → Binding
  | "crc32_z" => .dynsym (some zlib129)
  | "adler32_z" => .dynsym (some zlib129)
  | _ => .dynsym none

/-- The stack requirement of every row: 256 bytes below `rsp`. -/
def frame : Nat := 256

/-- The coverage of the excerpt by `libz.so.1.3`: the four checksum entry points claimed; the
other seven declarations are defined in the library (in `.dynsym`) and unclaimed. -/
def coverage : Coverage where
  claimed := ["crc32_z", "crc32", "adler32_z", "adler32"]
  excluded :=
    [("adler32_combine", .unclaimed "present in .dynsym; no conformance row yet"),
     ("crc32_combine", .unclaimed "present in .dynsym; no conformance row yet"),
     ("get_crc_table", .unclaimed "present in .dynsym; no conformance row yet"),
     ("crc32_combine_gen", .unclaimed "present in .dynsym; no conformance row yet"),
     ("crc32_combine_op", .unclaimed "present in .dynsym; no conformance row yet"),
     ("zlibVersion", .unclaimed "present in .dynsym; no conformance row yet"),
     ("zlibCompileFlags", .unclaimed "present in .dynsym; no conformance row yet")]

/-- The implementations claimed: code (at link-time addresses), frame, spec and mode. -/
def impl : String → Option (Impl sysvInt)
  | "crc32_z" => some ⟨zProto, crc32zCode, frame, crc32zS, .total⟩
  | "crc32" => some ⟨wProto, crc32Code, frame, crc32S, .total⟩
  | "adler32_z" => some ⟨zProto, adler32zCode, frame, adler32zS, .total⟩
  | "adler32" => some ⟨wProto, adler32Code, frame, adler32S, .total⟩
  | _ => none

/-- **Open**: at every load base the file admits, `crc32_z` conforms on `Open9` (the file part
is proved, `Thms.crc32z_of`). -/
def Task.crc32z : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "crc32_z" zProto (crc32zCode.rebase base) frame crc32zS

def Task.crc32 : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "crc32" wProto (crc32Code.rebase base) frame crc32S

def Task.adler32z : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "adler32_z" zProto (adler32zCode.rebase base) frame adler32zS

def Task.adler32 : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "adler32" wProto (adler32Code.rebase base) frame adler32S

end Silmaril.Elf.Abi.ZlibLibz

end

silmaril instance silmaril.elf.abi.zlib_libz.crc32_z
    (title := "libz.so.1.3 crc32_z@@ZLIB_1.2.9 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "crc32_z") (p := Silmaril.Machine.Abi.Conformance.Zlib.zProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := .dynsym (some Silmaril.Elf.Abi.ZlibLibz.zlib129))
    (c := Silmaril.Machine.Abi.Conformance.ZlibLibz.crc32zCode) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.crc32zS)
silmaril instance silmaril.elf.abi.zlib_libz.crc32
    (title := "libz.so.1.3 crc32 (base version) conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "crc32") (p := Silmaril.Machine.Abi.Conformance.Zlib.wProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := .dynsym none)
    (c := Silmaril.Machine.Abi.Conformance.ZlibLibz.crc32Code) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.crc32S)
silmaril instance silmaril.elf.abi.zlib_libz.adler32_z
    (title := "libz.so.1.3 adler32_z@@ZLIB_1.2.9 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "adler32_z") (p := Silmaril.Machine.Abi.Conformance.Zlib.zProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := .dynsym (some Silmaril.Elf.Abi.ZlibLibz.zlib129))
    (c := Silmaril.Machine.Abi.Conformance.ZlibLibz.adler32zCode) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.adler32zS)
silmaril instance silmaril.elf.abi.zlib_libz.adler32
    (title := "libz.so.1.3 adler32 (base version) conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "adler32") (p := Silmaril.Machine.Abi.Conformance.Zlib.wProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := .dynsym none)
    (c := Silmaril.Machine.Abi.Conformance.ZlibLibz.adler32Code) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := Silmaril.Machine.Abi.Conformance.Zlib.adler32S)
silmaril instance silmaril.elf.abi.zlib_libz.zlib_h
    (title := "libz.so.1.3 satisfies part of zlib.h (4 checksum functions claimed, total, at every load base) under System V AMD64 on Open9 (open)") :=
  silmaril.shapes.elf.abi_header_sat_partial (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open9.isa) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (cov := Silmaril.Elf.Abi.ZlibLibz.coverage) (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F)
    (bind := Silmaril.Elf.Abi.ZlibLibz.bind) (impl := Silmaril.Elf.Abi.ZlibLibz.impl)
