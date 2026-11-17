module

public import Silmaril.Elf.Abi.ZlibLibz.Defs
public import Silmaril.Machine.Abi.Conformance.Zlib.Api.Defs
public import Silmaril.Machine.Abi.Conformance.ZlibApi.Defs

/-! # ABI conformance rows: the 11-declaration zlib.h checksum excerpt in Ubuntu's `libz.so.1.3`

The seven declarations of the zlib.h excerpt beside the four checksum entry points
(`Silmaril.Elf.Abi.ZlibLibz`), with the specs of `Silmaril.Machine.Abi.Conformance.Zlib.Api`, on
the same file and in the same (hosted) header configuration. With them every declaration of the
excerpt is claimed, so the header row here is **complete** header satisfaction
(`abi_header_sat_complete`: nothing unclaimed, nothing absent), for the surface the
`sysvInt` fragment expresses, on `Open9`. It is open: it holds once the eleven conformance tasks
do. Each row is total with a 256-byte frame, at every load base, bound through a structural model of
ld.so's versioned lookup (`Lookup` on this file's `.dynsym` and version tables, after glibc's
`check_match`; not global scope, interposition or `LD_PRELOAD`):

| function | binding |
| --- | --- |
| `crc32_combine`, `adler32_combine` | `ZLIB_1.2.2` |
| `crc32_combine_gen`, `crc32_combine_op` | `ZLIB_1.2.12` |
| `zlibCompileFlags` | `ZLIB_1.2.0.2` |
| `get_crc_table`, `zlibVersion` | unversioned (base version) |

`zlibVersion`'s spec is this library's string, `"1.3"` (its `zlib.h` would say `ZLIB_VERSION`);
`zlibCompileFlags`'s is the low byte the data model gives (`0xa9`). Everything but the
conformance is proved (`Thms`). -/

@[expose] public section

namespace Silmaril.Elf.Abi.ZlibMatrix.Api

open Silmaril.Elf
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib.Api
open Silmaril.Machine.Abi.Conformance.ZlibApi
open Silmaril.Elf.Abi.ZlibLibz (hdr frame)
open Silmaril.Elf.Staged.Pinned.ZlibLibz (F)

/-- The version `ZLIB_1.2.2` as a reference requests it: name, ELF hash, not hidden. -/
def zlib122 : Ver := ⟨nameOf "ZLIB_1.2.2", 136832450, false⟩

/-- The version `ZLIB_1.2.12` as a reference requests it: name, ELF hash, not hidden. -/
def zlib1212 : Ver := ⟨nameOf "ZLIB_1.2.12", 41835714, false⟩

/-- The version `ZLIB_1.2.0.2` as a reference requests it: name, ELF hash, not hidden. -/
def zlib1202 : Ver := ⟨nameOf "ZLIB_1.2.0.2", 132500274, false⟩

/-- ld.so's lookup in `.dynsym`, at each function's version (the four checksum entry points as
`ZlibLibz.bind`). -/
def bind : String → Binding
  | "crc32_combine" => .dynsym (some zlib122)
  | "adler32_combine" => .dynsym (some zlib122)
  | "crc32_combine_gen" => .dynsym (some zlib1212)
  | "crc32_combine_op" => .dynsym (some zlib1212)
  | "zlibCompileFlags" => .dynsym (some zlib1202)
  | f => Silmaril.Elf.Abi.ZlibLibz.bind f

/-- Every declaration of the excerpt claimed: nothing excluded. -/
def coverage : Coverage where
  claimed := ["crc32_z", "crc32", "adler32_z", "adler32", "crc32_combine", "adler32_combine", "crc32_combine_gen", "crc32_combine_op", "get_crc_table", "zlibVersion", "zlibCompileFlags"]
  excluded := []

/-- The implementations: the four of `ZlibLibz`, and the seven here. -/
def impl : String → Option (Impl sysvInt)
  | "crc32_combine" => some ⟨combineProto, crc32CombineCode, frame, crc32CombineS, .total⟩
  | "adler32_combine" => some ⟨combineProto, adler32CombineCode, frame, adler32CombineS, .total⟩
  | "crc32_combine_gen" => some ⟨genProto, crc32CombineGenCode, frame, crc32CombineGenS, .total⟩
  | "crc32_combine_op" => some ⟨opProto, crc32CombineOpCode, frame, crc32CombineOpS, .total⟩
  | "get_crc_table" => some ⟨ptrProto, getCrcTableCode, frame, getCrcTableS, .total⟩
  | "zlibVersion" => some ⟨ptrProto, zlibVersionCode, frame, zlibVersionS "1.3", .total⟩
  | "zlibCompileFlags" => some ⟨flagsProto, zlibCompileFlagsCode, frame, zlibCompileFlagsS sysvInt.dm, .total⟩
  | f => Silmaril.Elf.Abi.ZlibLibz.impl f

/-- **Open**: at every load base, `crc32_combine` conforms on `Open9`. -/
def Task.crc32Combine : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "crc32_combine" combineProto (crc32CombineCode.rebase base) frame (crc32CombineS)

/-- **Open**: at every load base, `adler32_combine` conforms on `Open9`. -/
def Task.adler32Combine : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "adler32_combine" combineProto (adler32CombineCode.rebase base) frame (adler32CombineS)

/-- **Open**: at every load base, `crc32_combine_gen` conforms on `Open9`. -/
def Task.crc32CombineGen : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "crc32_combine_gen" genProto (crc32CombineGenCode.rebase base) frame (crc32CombineGenS)

/-- **Open**: at every load base, `crc32_combine_op` conforms on `Open9`. -/
def Task.crc32CombineOp : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "crc32_combine_op" opProto (crc32CombineOpCode.rebase base) frame (crc32CombineOpS)

/-- **Open**: at every load base, `get_crc_table` conforms on `Open9`. -/
def Task.getCrcTable : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "get_crc_table" ptrProto (getCrcTableCode.rebase base) frame (getCrcTableS)

/-- **Open**: at every load base, `zlibVersion` conforms on `Open9`. -/
def Task.zlibVersion : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "zlibVersion" ptrProto (zlibVersionCode.rebase base) frame (zlibVersionS "1.3")

/-- **Open**: at every load base, `zlibCompileFlags` conforms on `Open9`. -/
def Task.zlibCompileFlags : Prop :=
  ∀ base, Placement F base →
    Conforms sysvInt Silmaril.X86.Open9.isa .total hdr "zlibCompileFlags" flagsProto (zlibCompileFlagsCode.rebase base) frame (zlibCompileFlagsS sysvInt.dm)

end Silmaril.Elf.Abi.ZlibMatrix.Api

end

silmaril instance silmaril.elf.abi.zlib_libz.crc32_combine
    (title := "libz.so.1.3 crc32_combine@@ZLIB_1.2.2 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "crc32_combine") (p := Silmaril.Machine.Abi.Conformance.Zlib.Api.combineProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := (.dynsym (some Silmaril.Elf.Abi.ZlibMatrix.Api.zlib122)))
    (c := Silmaril.Machine.Abi.Conformance.ZlibApi.crc32CombineCode) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := (Silmaril.Machine.Abi.Conformance.Zlib.Api.crc32CombineS))
silmaril instance silmaril.elf.abi.zlib_libz.adler32_combine
    (title := "libz.so.1.3 adler32_combine@@ZLIB_1.2.2 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "adler32_combine") (p := Silmaril.Machine.Abi.Conformance.Zlib.Api.combineProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := (.dynsym (some Silmaril.Elf.Abi.ZlibMatrix.Api.zlib122)))
    (c := Silmaril.Machine.Abi.Conformance.ZlibApi.adler32CombineCode) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := (Silmaril.Machine.Abi.Conformance.Zlib.Api.adler32CombineS))
silmaril instance silmaril.elf.abi.zlib_libz.crc32_combine_gen
    (title := "libz.so.1.3 crc32_combine_gen@@ZLIB_1.2.12 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "crc32_combine_gen") (p := Silmaril.Machine.Abi.Conformance.Zlib.Api.genProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := (.dynsym (some Silmaril.Elf.Abi.ZlibMatrix.Api.zlib1212)))
    (c := Silmaril.Machine.Abi.Conformance.ZlibApi.crc32CombineGenCode) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := (Silmaril.Machine.Abi.Conformance.Zlib.Api.crc32CombineGenS))
silmaril instance silmaril.elf.abi.zlib_libz.crc32_combine_op
    (title := "libz.so.1.3 crc32_combine_op@@ZLIB_1.2.12 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, for operators with nonzero low 32 bits (zlib loops on the others), at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "crc32_combine_op") (p := Silmaril.Machine.Abi.Conformance.Zlib.Api.opProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := (.dynsym (some Silmaril.Elf.Abi.ZlibMatrix.Api.zlib1212)))
    (c := Silmaril.Machine.Abi.Conformance.ZlibApi.crc32CombineOpCode) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := (Silmaril.Machine.Abi.Conformance.Zlib.Api.crc32CombineOpS))
silmaril instance silmaril.elf.abi.zlib_libz.get_crc_table
    (title := "libz.so.1.3 get_crc_table (base version) conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "get_crc_table") (p := Silmaril.Machine.Abi.Conformance.Zlib.Api.ptrProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := (.dynsym none))
    (c := Silmaril.Machine.Abi.Conformance.ZlibApi.getCrcTableCode) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := (Silmaril.Machine.Abi.Conformance.Zlib.Api.getCrcTableS))
silmaril instance silmaril.elf.abi.zlib_libz.zlib_version
    (title := "libz.so.1.3 zlibVersion (base version) conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "zlibVersion") (p := Silmaril.Machine.Abi.Conformance.Zlib.Api.ptrProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := (.dynsym none))
    (c := Silmaril.Machine.Abi.Conformance.ZlibApi.zlibVersionCode) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := (Silmaril.Machine.Abi.Conformance.Zlib.Api.zlibVersionS "1.3"))
silmaril instance silmaril.elf.abi.zlib_libz.zlib_compile_flags
    (title := "libz.so.1.3 zlibCompileFlags@@ZLIB_1.2.0.2 conforms to System V AMD64 (INTEGER fragment) on Open9 as zlib.h declares it, at every load base: total, frame 256 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open9 (mode := .total) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (f := "zlibCompileFlags") (p := Silmaril.Machine.Abi.Conformance.Zlib.Api.flagsProto)
    (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F) (b := (.dynsym (some Silmaril.Elf.Abi.ZlibMatrix.Api.zlib1202)))
    (c := Silmaril.Machine.Abi.Conformance.ZlibApi.zlibCompileFlagsCode) (frame := Silmaril.Elf.Abi.ZlibLibz.frame)
    (S := (Silmaril.Machine.Abi.Conformance.Zlib.Api.zlibCompileFlagsS Silmaril.Machine.Abi.Conformance.sysvInt.dm))
silmaril instance silmaril.elf.abi.zlib_libz.zlib_h_complete
    (title := "libz.so.1.3 satisfies all 11 declarations of the zlib.h checksum excerpt (none absent; total, at every load base) under System V AMD64 (INTEGER fragment) on Open9 (open)") :=
  silmaril.shapes.elf.abi_header_sat_complete (A := Silmaril.Machine.Abi.Conformance.sysvInt) (M := Silmaril.X86.Open9.isa) (hdr := Silmaril.Elf.Abi.ZlibLibz.hdr)
    (cov := Silmaril.Elf.Abi.ZlibMatrix.Api.coverage) (F := Silmaril.Elf.Staged.Pinned.ZlibLibz.F)
    (bind := Silmaril.Elf.Abi.ZlibMatrix.Api.bind) (impl := Silmaril.Elf.Abi.ZlibMatrix.Api.impl)
