import Lean
import Silmaril.Elf.Staged.Reader.Defs
import Silmaril.Elf.Staged.Pinned.HelloGcc.Defs
import Silmaril.Elf.Staged.Pinned.HelloClang.Defs
import Silmaril.Elf.Staged.Pinned.Sha256sum.Defs
import Silmaril.Elf.Staged.Pinned.LeafArith.Defs
-- loaded at run time (not in the Makefile's ELF_PINNED): imported so building elf-pages builds them
import Silmaril.Elf.Staged.Pinned.LeafArith.Thms
import Silmaril.Elf.Staged.Pinned.LeafArith.Functions
import Silmaril.Elf.Staged.Pinned.ZlibChecksums.Defs
import Silmaril.Elf.Staged.Pinned.ZlibLibz.Defs
-- The pages load each pinned file's `Thms` and `Functions` at run time; importing them here makes
-- `lake build elf-pages` build them, so no separate target list has to name them.
import Silmaril.Elf.Staged.Pinned.ZlibLibz1211.Defs
import Silmaril.Elf.Staged.Pinned.ZlibLibz1211.Thms
import Silmaril.Elf.Staged.Pinned.ZlibLibz1211.Functions
import Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc.Defs
import Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc.Thms
import Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc.Functions
import Silmaril.Elf.Staged.Pinned.ZlibLibz131Clang.Defs
import Silmaril.Elf.Staged.Pinned.ZlibLibz131Clang.Thms
import Silmaril.Elf.Staged.Pinned.ZlibLibz131Clang.Functions
import Silmaril.Elf.Staged.Pinned.GlibcLibm.Defs
import Silmaril.Elf.Staged.Pinned.GlibcLibc.Defs
import Silmaril.Crypto.SHA256
-- The CLI tab's modules (`cliModules`), loaded at run time: imported here so that building
-- `elf-pages` builds them, whatever the CI scope.
import Silmaril.Elf.CliExe.Start.Thms
import Silmaril.Elf.CliExe.Hello.Thms
import Silmaril.Elf.Link.Dyn.Hello.Thms
import Silmaril.Elf.Link.Dyn.LibMod.Hello.Thms
import Silmaril.Elf.Link.Dyn.Libc.Hello.Thms
import Silmaril.Elf.Link.Dyn.Program.Cli.Examples
import Silmaril.Process.LPS.Problems.GnuSha256sum.Close
import Silmaril.Process.LPS.Problems.Sha256Cli.EndToEnd
import Silmaril.Cli.Institution.Std.Thms
import Silmaril.Cli.Spec.Sha256sum.Thms
import Silmaril.Cli.Spec.WasmOpt.Thms
import Silmaril.Cli.Spec.Wac.Thms
import Silmaril.Cli.Spec.Jco.Thms
import Silmaril.Cli.Spec.Asyncify.Thms
import Silmaril.Cli.Spec.WasmTools.Thms
import Silmaril.Cli.Spec.WasmVerify.Thms
import Silmaril.Wasm.Binaryen.DriverSpec.Thms
-- The assembly tab's modules (`asmModules`), loaded at run time to locate the declarations that
-- `examples/elf-asm/samples.json` names. They bring the `binary_image … sha256 "…"` syntax
-- (Silmaril.Data.BinaryImage), so `sha256` is a keyword here: fields of that name are `«sha256»`.
import Silmaril.Elf.Asm.Example.Thms
import Silmaril.Elf.Asm.Example.Reloc.Thms
import Silmaril.Elf.Asm.Example.LeafArith.Thms
import Silmaril.Elf.Abi.Asm.LeafArith.Thms
import Silmaril.Elf.Abi.Asm.LeafArith.Decoys
import Silmaril.Elf.Pin.Examples

/-!
# `elf-pages`: the explorer's ELF tab data

```
lake env .lake/build/bin/elf-pages OUTDIR     write OUTDIR/elf/{index.json, f/SLUG.json, dis/SLUG.json, blob/SLUG.bin}
lake env .lake/build/bin/elf-pages --verify OUTDIR    re-derive everything and compare with OUTDIR/elf
lake env .lake/build/bin/elf-pages --self-test OUTDIR write, verify, and check that tampered pages are rejected
```

It also copies the assembly functions of `tools/elf-asm` (`examples/elf-asm/samples.json`,
schema `silmaril.elf.asm/1`) to `OUTDIR/elf/asm.json` unchanged, for the assembly tab; their
evidence is read from theorem statements and checked by `elf-asm --check` (`make elf-check`), not
re-derived here. Next to it, `elf/asm-decls.json` gives the module and source line of every
declaration the file names, each looked up in the checked environment (a name that is not there
stops the tool).

For each pinned file (`Silmaril.Elf.Staged.Pinned.*`) the tool

1. reads the file at its pinned path and checks its SHA-256 against the module's `sha256`;
2. **imports the checked theorem module** (`….Thms`, built by `lake build --wfail`) and, for every
   theorem in it, reads the statement: `PartIs F ws p v`, `ZerosAt F o n`, `LayoutIs F L` or
   `Parses F A`. Which part a theorem is about and which bytes it covers come **from the
   statement** (the reader `p`, the windows `ws`, the constant `v` and its place in `L`), never
   from the theorem's name or from any metadata; a statement of another form, or naming another
   file, stops the tool;
3. re-runs each statement's reader natively on the file restricted to its windows and compares
   with the claimed constant (a consistency check of this tool against the checked statement; the
   proof is the kernel's);
4. collects each theorem's axioms (`collectAxioms`) and declaration range;
5. derives the coverage of every byte of the file from the theorems' windows: `decoded` (inside
   a checked part's windows), `zeros` (a checked `ZerosAt`), `raw` (inside a section or segment
   but not decoded: payload kept as a byte range), `unknown` (anything else);
6. runs `objdump -d` (if present) for an **unverified** disassembly of the executable sections,
   and checks that each listed instruction's bytes are the file's bytes at that address. The
   listing is external output: nothing in Lean is about it.
-/

open Lean
open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Link.DynElf (Rd)
open Silmaril.Formats.ELF (Header ProgramHeader SectionHeader NameBytes ObjectSymbol Rela)

namespace ElfPages

/-! ## The pinned files -/

structure Pinned where
  slug : String
  ns : Name
  title : String
  path : String
  «sha256» : String
  size : Nat
  L : Layout
  bodies : List Body
  ld : Loader
  /-- `(label, text)` pairs; `url:` labels are links. -/
  provenance : List (String × String)

def pinned : List Pinned := [
  { slug := "hello-gcc", ns := `Silmaril.Elf.Staged.Pinned.HelloGcc
    title := "hello world (gcc 13.3 -O2), dynamically linked against glibc 2.39"
    path := Pinned.HelloGcc.path, «sha256» := Pinned.HelloGcc.sha256, size := Pinned.HelloGcc.size
    L := Pinned.HelloGcc.L, bodies := Pinned.HelloGcc.bodies, ld := Pinned.HelloGcc.ld
    provenance := [
      ("source", "examples/dyn/hello/hello.c (written for this repository)"),
      ("linked", "dynamically against glibc 2.39: PT_INTERP /lib64/ld-linux-x86-64.so.2, DT_NEEDED libc.so.6 (both read by the checked loader-view theorem)"),
      ("build", "gcc 13.3.0-6ubuntu2~24.04.1 -O2, default PIE, dynamic glibc 2.39; byte-for-byte reproducible (examples/dyn/pins.txt, examples/dyn/pin.sh --build)"),
      ("licence", "toolchain start-up objects: glibc crt (LGPL-2.1-or-later with the linking exception), GCC crtbeginS/crtendS (GPL-3.0-or-later with the GCC Runtime Library Exception); examples/dyn/README.md")] },
  { slug := "hello-clang", ns := `Silmaril.Elf.Staged.Pinned.HelloClang
    title := "hello world (clang 18.1 -O2), dynamically linked against glibc 2.39"
    path := Pinned.HelloClang.path, «sha256» := Pinned.HelloClang.sha256, size := Pinned.HelloClang.size
    L := Pinned.HelloClang.L, bodies := Pinned.HelloClang.bodies, ld := Pinned.HelloClang.ld
    provenance := [
      ("source", "examples/dyn/hello/hello.c (written for this repository)"),
      ("linked", "dynamically against glibc 2.39: PT_INTERP /lib64/ld-linux-x86-64.so.2, DT_NEEDED libc.so.6 (both read by the checked loader-view theorem)"),
      ("build", "clang 18.1.3 (1:18.1.3-1ubuntu1) -O2 with GCC 13's crt objects, default PIE; byte-for-byte reproducible (examples/dyn/pins.txt, examples/dyn/pin.sh --build)"),
      ("licence", "toolchain start-up objects: glibc crt (LGPL-2.1-or-later with the linking exception), GCC crtbeginS/crtendS (GPL-3.0-or-later with the GCC Runtime Library Exception); examples/dyn/README.md")] },
  { slug := "leaf-arith", ns := `Silmaril.Elf.Staged.Pinned.LeafArith
    title := "elf-ladder rung 01 leaf-arith (arith.c leaf functions, -O2, static, not stripped)"
    path := Pinned.LeafArith.path, «sha256» := Pinned.LeafArith.sha256, size := Pinned.LeafArith.size
    L := Pinned.LeafArith.L, bodies := Pinned.LeafArith.bodies, ld := Pinned.LeafArith.ld
    provenance := [
      ("source", "examples/elf-ladder/01-leaf-arith/arith.c, arith.h and main.c, with examples/elf-ladder/common (written for this repository)"),
      ("build", "examples/elf-ladder/01-leaf-arith/build.sh: GCC 13.3.0, GNU ld 2.42, -O2 (examples/elf-ladder/common/flags.sh), static, not stripped (.symtab present)"),
      ("abi conformance", "clamp_i32 and sat_add_u32 conform, as arith.h declares them, to the INTEGER fragment of the System V AMD64 psABI on the restricted open machine model Open (FP, vector and control state carried by the model, not proved for real x86); arith.h is satisfied only PARTIALLY (2 functions claimed, not header satisfaction): Silmaril.Elf.Abi.LeafArith (rows silmaril.elf.abi.leaf_arith.*, docs/projects/abi-conformance.md)"),
      ("licence", "this repository's MIT licence")] },
  { slug := "zlib-checksums", ns := `Silmaril.Elf.Staged.Pinned.ZlibChecksums
    title := "zlib 1.3.1 adler32.c + crc32.c (-DZ_SOLO -O2, static, not stripped)"
    path := Pinned.ZlibChecksums.path, «sha256» := Pinned.ZlibChecksums.sha256, size := Pinned.ZlibChecksums.size
    L := Pinned.ZlibChecksums.L, bodies := Pinned.ZlibChecksums.bodies, ld := Pinned.ZlibChecksums.ld
    provenance := [
      ("source", "zlib 1.3.1 adler32.c and crc32.c, unmodified, with examples/elf-ladder/03-zlib-checksums/main.c (release tarball sha256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23)"),
      ("build", "examples/elf-ladder/03-zlib-checksums/build.sh: GCC 13.3.0, binutils 2.42, -O2, static, not stripped (.symtab present)"),
      ("contracts", "crc32_z, crc32, adler32_z, adler32: Silmaril.X86.Ladder.ZlibChecksums, tied to this file by Silmaril.Elf.Staged.Pinned.ZlibChecksums.Contracts"),
      ("licence", "zlib licence (examples/elf-ladder/03-zlib-checksums/pinned/LICENSE.zlib, NOTICES/zlib)")] },
  { slug := "zlib-libz", ns := `Silmaril.Elf.Staged.Pinned.ZlibLibz
    title := "zlib 1.3 libz.so.1.3 (Ubuntu zlib1g 1:1.3.dfsg-3.1ubuntu2.3, amd64)"
    path := Pinned.ZlibLibz.path, «sha256» := Pinned.ZlibLibz.sha256, size := Pinned.ZlibLibz.size
    L := Pinned.ZlibLibz.L, bodies := Pinned.ZlibLibz.bodies, ld := Pinned.ZlibLibz.ld
    provenance := [
      ("package", "Ubuntu zlib1g 1:1.3.dfsg-3.1ubuntu2.3 (amd64), /usr/lib/x86_64-linux-gnu/libz.so.1.3, unmodified"),
      ("url:package", "https://launchpad.net/ubuntu/+archive/primary/+files/zlib1g_1.3.dfsg-3.1ubuntu2.3_amd64.deb"),
      ("package sha256", "376249c8de139568221dbb242318cc8cb8f02299e3a62b7432948e1754fbddf9"),
      ("fetch", "examples/elf/pin.sh --fetch (verifies the package and file hashes)"),
      ("symbols", "stripped: .dynsym only"),
      ("licence", "zlib licence (NOTICES/zlib)"),
      ("url:source", "https://launchpad.net/ubuntu/+source/zlib/1:1.3.dfsg-3.1ubuntu2.3")] },
  { slug := "zlib-libz-1.2.11", ns := `Silmaril.Elf.Staged.Pinned.ZlibLibz1211
    title := "zlib 1.2.11 libz.so.1.2.11 (Ubuntu zlib1g 1:1.2.11.dfsg-2ubuntu9.2, amd64)"
    path := Pinned.ZlibLibz1211.path, «sha256» := Pinned.ZlibLibz1211.sha256, size := Pinned.ZlibLibz1211.size
    L := Pinned.ZlibLibz1211.L, bodies := Pinned.ZlibLibz1211.bodies, ld := Pinned.ZlibLibz1211.ld
    provenance := [
      ("package", "Ubuntu 22.04 zlib1g 1:1.2.11.dfsg-2ubuntu9.2 (amd64), /lib/x86_64-linux-gnu/libz.so.1.2.11, unmodified"),
      ("url:package", "https://launchpad.net/ubuntu/+archive/primary/+files/zlib1g_1.2.11.dfsg-2ubuntu9.2_amd64.deb"),
      ("package sha256", "9dc17e51a1be2d9ed63b7b84ef0e4e29c5abe6f1bc62cb03e7181483cce8a2f2 (as in the jammy-updates Packages index)"),
      ("fetch", "examples/elf/pin.sh --fetch (verifies the package and file hashes)"),
      ("symbols", "stripped: .dynsym only; crc32_z is an STT_GNU_IFUNC"),
      ("licence", "zlib licence (NOTICES/zlib)"),
      ("url:source", "https://launchpad.net/ubuntu/+source/zlib/1:1.2.11.dfsg-2ubuntu9.2")] },
  { slug := "zlib-libz-1.3.1-gcc", ns := `Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc
    title := "zlib 1.3.1 libz.so.1.3.1 (GCC 13.3 -O2, release tarball)"
    path := Pinned.ZlibLibz131Gcc.path, «sha256» := Pinned.ZlibLibz131Gcc.sha256, size := Pinned.ZlibLibz131Gcc.size
    L := Pinned.ZlibLibz131Gcc.L, bodies := Pinned.ZlibLibz131Gcc.bodies, ld := Pinned.ZlibLibz131Gcc.ld
    provenance := [
      ("compiler", "GCC 13.3.0 (Ubuntu 13.3.0-6ubuntu2~24.04.1), GNU ld 2.42"),
      ("build", "examples/libs/zlib/build.sh: ./configure && make libz.so.1.3.1, CFLAGS -O2, in ubuntu:24.04 pinned by digest with the toolchain from the Ubuntu snapshot archive; byte-for-byte reproducible (build.sh --check)"),
      ("source", "zlib 1.3.1 release tarball, sha256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23"),
      ("url:source", "https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.gz"),
      ("symbols", ".symtab and .dynsym; crc32 and adler32 tail-call their _z functions through the PLT"),
      ("licence", "zlib licence (NOTICES/zlib)")] },
  { slug := "zlib-libz-1.3.1-clang", ns := `Silmaril.Elf.Staged.Pinned.ZlibLibz131Clang
    title := "zlib 1.3.1 libz.so.1.3.1 (Clang 18.1 -O2, release tarball)"
    path := Pinned.ZlibLibz131Clang.path, «sha256» := Pinned.ZlibLibz131Clang.sha256, size := Pinned.ZlibLibz131Clang.size
    L := Pinned.ZlibLibz131Clang.L, bodies := Pinned.ZlibLibz131Clang.bodies, ld := Pinned.ZlibLibz131Clang.ld
    provenance := [
      ("compiler", "Ubuntu clang 18.1.3 (1ubuntu1), GNU ld 2.42"),
      ("build", "examples/libs/zlib/build.sh: ./configure && make libz.so.1.3.1, CFLAGS -O2, in ubuntu:24.04 pinned by digest with the toolchain from the Ubuntu snapshot archive; byte-for-byte reproducible (build.sh --check)"),
      ("source", "zlib 1.3.1 release tarball, sha256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23"),
      ("url:source", "https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.gz"),
      ("symbols", ".symtab and .dynsym; crc32 and adler32 tail-call their _z functions through the PLT"),
      ("licence", "zlib licence (NOTICES/zlib)")] },
  { slug := "glibc-libm", ns := `Silmaril.Elf.Staged.Pinned.GlibcLibm
    title := "glibc 2.39 libm.so.6 (Ubuntu libc6 2.39-0ubuntu8.9, amd64)"
    path := Pinned.GlibcLibm.path, «sha256» := Pinned.GlibcLibm.sha256, size := Pinned.GlibcLibm.size
    L := Pinned.GlibcLibm.L, bodies := Pinned.GlibcLibm.bodies, ld := Pinned.GlibcLibm.ld
    provenance := [
      ("package", "Ubuntu libc6 2.39-0ubuntu8.9 (amd64), unmodified"),
      ("url:package", "https://launchpad.net/ubuntu/+archive/primary/+files/libc6_2.39-0ubuntu8.9_amd64.deb"),
      ("package sha256", "ff5557d99b51f761c4b7c92368b9cc45565eda17df9bf9eb4b134d09825008be"),
      ("fetch", "examples/elf/pin.sh --fetch (verifies the package and file hashes)"),
      ("symbols", "stripped: .dynsym only (no .symtab, no debug information)"),
      ("licence", "LGPL-2.1-or-later (NOTICES/glibc)"),
      ("url:source", "https://launchpad.net/ubuntu/+source/glibc/2.39-0ubuntu8.9")] },
  { slug := "glibc-libc", ns := `Silmaril.Elf.Staged.Pinned.GlibcLibc
    title := "glibc 2.39 libc.so.6 (Ubuntu libc6 2.39-0ubuntu8.9, amd64)"
    path := Pinned.GlibcLibc.path, «sha256» := Pinned.GlibcLibc.sha256, size := Pinned.GlibcLibc.size
    L := Pinned.GlibcLibc.L, bodies := Pinned.GlibcLibc.bodies, ld := Pinned.GlibcLibc.ld
    provenance := [
      ("package", "Ubuntu libc6 2.39-0ubuntu8.9 (amd64), unmodified"),
      ("url:package", "https://launchpad.net/ubuntu/+archive/primary/+files/libc6_2.39-0ubuntu8.9_amd64.deb"),
      ("package sha256", "ff5557d99b51f761c4b7c92368b9cc45565eda17df9bf9eb4b134d09825008be"),
      ("fetch", "examples/elf/pin.sh --fetch (verifies the package and file hashes)"),
      ("symbols", "stripped: .dynsym only (no .symtab, no debug information)"),
      ("licence", "LGPL-2.1-or-later (NOTICES/glibc)"),
      ("url:source", "https://launchpad.net/ubuntu/+source/glibc/2.39-0ubuntu8.9")] },
  { slug := "gnu-sha256sum", ns := `Silmaril.Elf.Staged.Pinned.Sha256sum
    title := "GNU coreutils 9.4 sha256sum (Ubuntu 9.4-3ubuntu6.3, amd64)"
    path := Pinned.Sha256sum.path, «sha256» := Pinned.Sha256sum.sha256, size := Pinned.Sha256sum.size
    L := Pinned.Sha256sum.L, bodies := Pinned.Sha256sum.bodies, ld := Pinned.Sha256sum.ld
    provenance := [
      ("package", "Ubuntu coreutils 9.4-3ubuntu6.3 (amd64), /usr/bin/sha256sum, unmodified"),
      ("url:package", "https://launchpad.net/ubuntu/+archive/primary/+files/coreutils_9.4-3ubuntu6.3_amd64.deb"),
      ("package sha256", "e1e9a17892be0cc83b7cea747edf331ffeb6d6c010b4db296e60d888e8e9274c"),
      ("fetch", "examples/elf/pin.sh --fetch (verifies the package and file hashes)"),
      ("licence", "GPL-3.0-or-later (NOTICES/effects-examples, NOTICES/GPLv3)"),
      ("url:source", "https://launchpad.net/ubuntu/+source/coreutils/9.4-3ubuntu6.3")] }]

/-! ## Small helpers -/

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def nameStr (n : NameBytes) : String := String.ofList (n.map fun b => Char.ofNat b.toNat)

def sha256Hex (b : ByteArray) : String :=
  String.join ((Silmaril.Crypto.SHA256.digest b.data.toList).map fun x =>
    let h := Nat.toDigits 16 x.toNat
    String.ofList (if h.length < 2 then '0' :: h else h))

def jn (n : Nat) : Json := toJson n
def js (s : String) : Json := toJson s
def spansJson (ws : List Span) : Json := Json.arr (ws.toArray.map fun s => Json.arr #[jn s.off, jn s.len])

/-! ## ELF names (display only) -/

def ptName (k : Nat) : String :=
  match k with
  | 0 => "NULL" | 1 => "LOAD" | 2 => "DYNAMIC" | 3 => "INTERP" | 4 => "NOTE" | 5 => "SHLIB"
  | 6 => "PHDR" | 7 => "TLS" | 0x6474e550 => "GNU_EH_FRAME" | 0x6474e551 => "GNU_STACK"
  | 0x6474e552 => "GNU_RELRO" | 0x6474e553 => "GNU_PROPERTY" | 0x6474e554 => "GNU_SFRAME"
  | k => hex k

def shtName (k : Nat) : String :=
  match k with
  | 0 => "NULL" | 1 => "PROGBITS" | 2 => "SYMTAB" | 3 => "STRTAB" | 4 => "RELA" | 5 => "HASH"
  | 6 => "DYNAMIC" | 7 => "NOTE" | 8 => "NOBITS" | 9 => "REL" | 11 => "DYNSYM"
  | 14 => "INIT_ARRAY" | 15 => "FINI_ARRAY" | 16 => "PREINIT_ARRAY" | 17 => "GROUP"
  | 18 => "SYMTAB_SHNDX" | 19 => "RELR" | 0x6ffffff6 => "GNU_HASH" | 0x6ffffffd => "GNU_verdef"
  | 0x6ffffffe => "GNU_verneed" | 0x6fffffff => "GNU_versym" | k => hex k

def etName (k : Nat) : String :=
  match k with
  | 0 => "NONE" | 1 => "REL" | 2 => "EXEC" | 3 => "DYN" | 4 => "CORE" | k => hex k

def machineName (k : Nat) : String :=
  match k with
  | 3 => "x86" | 40 => "ARM" | 62 => "x86-64" | 183 => "AArch64" | 243 => "RISC-V" | k => hex k

def dtName (k : Nat) : String :=
  match k with
  | 0 => "NULL" | 1 => "NEEDED" | 2 => "PLTRELSZ" | 3 => "PLTGOT" | 4 => "HASH" | 5 => "STRTAB"
  | 6 => "SYMTAB" | 7 => "RELA" | 8 => "RELASZ" | 9 => "RELAENT" | 10 => "STRSZ" | 11 => "SYMENT"
  | 12 => "INIT" | 13 => "FINI" | 14 => "SONAME" | 15 => "RPATH" | 16 => "SYMBOLIC" | 17 => "REL"
  | 18 => "RELSZ" | 19 => "RELENT" | 20 => "PLTREL" | 21 => "DEBUG" | 22 => "TEXTREL"
  | 23 => "JMPREL" | 24 => "BIND_NOW" | 25 => "INIT_ARRAY" | 26 => "FINI_ARRAY"
  | 27 => "INIT_ARRAYSZ" | 28 => "FINI_ARRAYSZ" | 29 => "RUNPATH" | 30 => "FLAGS"
  | 0x6ffffef5 => "GNU_HASH" | 0x6ffffff0 => "VERSYM" | 0x6ffffff9 => "RELACOUNT"
  | 0x6ffffffb => "FLAGS_1" | 0x6ffffffe => "VERNEED" | 0x6fffffff => "VERNEEDNUM"
  | 0x6ffffffc => "VERDEF" | 0x6ffffffd => "VERDEFNUM" | k => hex k

def symType (info : Nat) : String :=
  match info % 16 with
  | 0 => "NOTYPE" | 1 => "OBJECT" | 2 => "FUNC" | 3 => "SECTION" | 4 => "FILE" | 6 => "TLS"
  | 10 => "IFUNC" | k => toString k

def symBind (info : Nat) : String :=
  match info / 16 with
  | 0 => "LOCAL" | 1 => "GLOBAL" | 2 => "WEAK" | 10 => "UNIQUE" | k => toString k

def pflags (f : Nat) : String :=
  (if f &&& 4 != 0 then "R" else "-") ++ (if f &&& 2 != 0 then "W" else "-") ++
    (if f &&& 1 != 0 then "X" else "-")

def shflags (f : Nat) : String :=
  String.join ([(1, "W"), (2, "A"), (4, "X"), (0x10, "M"), (0x20, "S"), (0x40, "I"), (0x80, "L"),
    (0x200, "G"), (0x400, "T"), (0x800, "C")].filterMap fun (b, c) => if f &&& b != 0 then some c else none)

/-! ## Reading the checked statements -/

/-- A natural-number literal (`OfNat.ofNat Nat n _` or a raw literal). -/
partial def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then natLit? (e.getArg! 1)
    else none

/-- A list literal's elements. -/
partial def listLit? (e : Expr) : Option (List Expr) :=
  let e := e.consumeMData
  -- long list literals elaborate to `have x := [..]; a :: b :: x`
  if let .letE _ _ v b _ := e then listLit? (b.instantiate1 v)
  else if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then
    (listLit? (e.getArg! 2)).map (e.getArg! 1 :: ·)
  else none

def spanLit? (e : Expr) : Option Span :=
  let e := e.consumeMData
  if e.isAppOfArity ``Silmaril.Elf.Span.mk 2 then
    match natLit? (e.getArg! 0), natLit? (e.getArg! 1) with
    | some o, some l => some ⟨o, l⟩
    | _, _ => none
  else none

def constName? (e : Expr) : Option Name :=
  match e.consumeMData with
  | .const n _ => some n
  | _ => none

/-- What a theorem says (from its statement). -/
inductive Claim where
  | part (ws : List Span) (reader : Expr) (value : Name)
  | zeros (o n : Nat)
  | layout (L : Name)
  | parses (A : Expr)
  /-- `CodeAt F v code ∧ …`: code at `v`, with a contract (`Pinned.*.Contracts`). -/
  | contract (v : Nat) (code : Name) (loads : List Name)

def Claim.ofType? (F : Name) (t : Expr) : Except String Claim := do
  let t := t.consumeMData
  let fileIs (e : Expr) : Except String Unit :=
    if constName? e == some F then pure () else throw s!"names another file: {e}"
  if t.isAppOfArity ``Silmaril.Elf.Staged.Reader.PartIs 5 then
    fileIs (t.getArg! 1)
    let some ws := (listLit? (t.getArg! 2)).bind fun es => es.mapM spanLit?
      | throw "windows are not a literal list of spans"
    let some v := constName? (t.getArg! 4) | throw "the claimed value is not a constant"
    pure (.part ws (t.getArg! 3) v)
  else if t.isAppOfArity ``Silmaril.Elf.Staged.Reader.ZerosAt 3 then
    fileIs (t.getArg! 0)
    let (some o, some n) := (natLit? (t.getArg! 1), natLit? (t.getArg! 2))
      | throw "ZerosAt with non-literal range"
    pure (.zeros o n)
  else if t.isAppOfArity ``Silmaril.Elf.Staged.LayoutIs 2 then
    fileIs (t.getArg! 0)
    let some L := constName? (t.getArg! 1) | throw "LayoutIs of a non-constant"
    pure (.layout L)
  else if t.isAppOfArity ``Silmaril.Elf.Parses 2 then
    fileIs (t.getArg! 0)
    pure (.parses (t.getArg! 1))
  else if t.isAppOfArity ``And 2 && (t.getArg! 0).consumeMData.isAppOfArity `Silmaril.Elf.CodeAt 3 then
    let c := (t.getArg! 0).consumeMData
    fileIs (c.getArg! 0)
    let (some v, some code) := (natLit? (c.getArg! 1), constName? (c.getArg! 2))
      | throw "CodeAt with a non-literal address or code"
    -- the code constants the statement's identity conjunct requires the contract to load:
    -- every `Loaded _ _ c` in the rest of the statement
    let rec collect (e : Expr) (acc : List Name) : List Name :=
      match e with
      | .app f a =>
        let acc := if e.isAppOfArity `Silmaril.X86.Ext.Loaded 3 then
            (match constName? (e.getArg! 2) with | some c => c :: acc | none => acc) else acc
        collect a (collect f acc)
      | .lam _ t b _ | .forallE _ t b _ => collect b (collect t acc)
      | .letE _ t v b _ => collect b (collect v (collect t acc))
      | .mdata _ b => collect b acc
      | _ => acc
    pure (.contract v code (collect (t.getArg! 1) []))
  else throw s!"unrecognised statement: {t}"

/-- The role of a data constant: its place in the layout `L`, `bodies` or `ld`. -/
inductive Role where
  | header | phdr (i : Nat) | shdr (i : Nat) | name (i : Nat) | body (i : Nat) | loader | layout
  | symbol (sec i : Nat)
  deriving BEq, Repr

def Role.label : Role → String
  | .header => "ELF header" | .phdr i => s!"program header {i}" | .shdr i => s!"section header {i}"
  | .name i => s!"section name {i}" | .body i => s!"section body {i}" | .loader => "loader view"
  | .layout => "layout" | .symbol k i => s!"symbol {i} of section {k}"

def Role.key : Role → String
  | .header => "header" | .phdr i => s!"phdr/{i}" | .shdr i => s!"shdr/{i}" | .name i => s!"name/{i}"
  | .body i => s!"body/{i}" | .loader => "loader" | .layout => "layout"
  | .symbol k i => s!"sym/{k}/{i}"

/-- Roles from the **definitions** of `L`, `bodies` and `ld` in the environment. -/
def roles (env : Environment) (ns : Name) : Except String (List (Name × Role)) := do
  let val (n : Name) : Except String Expr :=
    match env.find? n with
    | some ci => match ci.value? (allowOpaque := true) with
      | some v => pure v
      | none => throw s!"{n} has no value"
    | none => throw s!"{n} not found"
  let Lv ← val (ns ++ `L)
  unless Lv.isAppOfArity ``Silmaril.Elf.Staged.Layout.mk 3 do throw "L is not a Layout literal"
  let some hdr := constName? (Lv.getArg! 0) | throw "L.header is not a constant"
  let some phs := (listLit? (Lv.getArg! 1)).bind (·.mapM constName?) | throw "L.phdrs"
  let some secs := listLit? (Lv.getArg! 2) | throw "L.sections"
  let secNames ← secs.mapM fun s => do
    unless s.isAppOfArity ``Silmaril.Elf.Staged.Sec.mk 2 do throw "a section is not Sec.mk"
    let (some h, some n) := (constName? (s.getArg! 0), constName? (s.getArg! 1)) | throw "Sec fields"
    pure (h, n)
  let some bs := (listLit? (← val (ns ++ `bodies))).bind (·.mapM constName?) | throw "bodies"
  let mut out : List (Name × Role) := [(hdr, .header), (ns ++ `ld, .loader), (ns ++ `L, .layout)]
  for (p, i) in phs.zipIdx do out := (p, .phdr i) :: out
  for ((h, n), i) in secNames.zipIdx do out := (h, .shdr i) :: (n, .name i) :: out
  for (b, i) in bs.zipIdx do
    out := (b, .body i) :: out
    -- a symbol table's body is `.symbols t [s₀, s₁, …]`: entry `j` is the constant `sⱼ`
    let bv ← val b
    if bv.isAppOfArity ``Silmaril.Elf.Body.symbols 2 then
      let some es := (listLit? (bv.getArg! 1)).bind (·.mapM constName?) | throw s!"{b}: entries"
      for (e, j) in es.zipIdx do out := (e, .symbol i j) :: out
  pure out

/-! ## Native re-check of a claim (consistency of this tool with the statement) -/

def bodyKind : Body → String
  | .null => "null" | .noBits => "nobits" | .progbits _ => "progbits" | .strtab _ => "strtab"
  | .symbols .symtab _ => "symtab" | .symbols .dynsym _ => "dynsym" | .relas _ => "rela"
  | .rels _ => "rel" | .relr _ => "relr" | .dynamic _ => "dynamic" | .gnuHash _ => "gnu_hash"
  | .hash _ => "hash" | .versym _ => "versym" | .verdef _ => "verdef" | .verneed _ => "verneed"
  | .notes _ => "notes" | .other _ => "other"

/-- Whether a body is decoded (a typed table) or kept as a byte range. -/
def bodyDecoded : Body → Bool
  | .progbits _ | .strtab _ | .other _ | .null | .noBits => false
  | _ => true

def recheck (P : Pinned) (src : Silmaril.Elf.Check.Src) (role : Role) (ws : List Span)
    (reader : Expr) : Except String Unit := do
  let w := window ws src
  let h := P.L.header
  let arg (i : Nat) := reader.getArg! i
  let ok (b : Bool) (what : String) : Except String Unit := unless b do throw what
  match role with
  | .header =>
    ok (reader.isConstOf ``Parse.header) "header: reader is not Parse.header"
    ok (Parse.header.run w == some h) "header: native run differs"
  | .phdr i =>
    let o := h.programOffset + 56 * i
    ok (reader.isAppOfArity ``Parse.phdr 1 && natLit? (arg 0) == some o) s!"phdr {i}: reader is not Parse.phdr {o}"
    ok ((Parse.phdr o).run w == P.L.phdrs[i]?) s!"phdr {i}: native run differs"
  | .shdr i =>
    let o := h.sectionOffset + 64 * i
    ok (reader.isAppOfArity ``Parse.shdr 1 && natLit? (arg 0) == some o) s!"shdr {i}: reader is not Parse.shdr {o}"
    ok ((Parse.shdr o).run w == (P.L.sections[i]?.map (·.header))) s!"shdr {i}: native run differs"
  | .name i =>
    let some names := P.L.shs[h.sectionNameIndex]? | throw "no .shstrtab"
    let some s := P.L.sections[i]? | throw s!"name {i}: no section"
    ok (reader.isAppOfArity ``Parse.strAt 2 && natLit? (arg 1) == some s.header.name)
      s!"name {i}: reader is not Parse.strAt"
    ok ((Parse.strAt names s.header.name).run w == some s.name) s!"name {i}: native run differs"
  | .body i =>
    let some s := P.L.sections[i]? | throw s!"body {i}: no section"
    ok (reader.isAppOfArity ``Parse.body 2) s!"body {i}: reader is not Parse.body"
    ok ((Parse.body P.L.shs s.header).run w == P.bodies[i]?) s!"body {i}: native run differs"
  | .loader =>
    ok (reader.isAppOfArity ``readLoader 1) "loader: reader is not readLoader"
    ok ((readLoader P.L.phdrs).run w == some P.ld) "loader: native run differs"
  | .layout =>
    ok (reader.isConstOf ``readLayout) "layout: reader is not readLayout"
    ok (readLayout.run w == some P.L) "layout: native run differs"
  | .symbol k j =>
    let some s := P.L.sections[k]? | throw s!"symbol {k}/{j}: no section"
    let some strs := P.L.shs[s.header.link]? | throw s!"symbol {k}/{j}: no string table"
    let some (.symbols _ es) := P.bodies[k]? | throw s!"symbol {k}/{j}: not a symbol table"
    let o := s.header.offset + 24 * j
    ok (reader.isAppOfArity ``Parse.symbol 2 && natLit? (arg 1) == some o) s!"symbol {k}/{j}: reader is not Parse.symbol at {o}"
    ok ((Parse.symbol strs o).run w == es[j]?) s!"symbol {k}/{j}: native run differs"

/-! ## Theorems of a module -/

structure Thm where
  decl : Name
  claim : Claim
  role : Option Role
  axioms : Array Name
  line : Option Nat
  module : Name
  /-- The statement, pretty-printed (contract theorems only). -/
  stmt : Option String := none
  /-- The length of the code literal a contract theorem's `CodeAt` names. -/
  codeLen : Option Nat := none

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- **Axioms with one cache for all theorems** (`Lean.collectAxioms` starts a fresh cache per call,
which revisits the shared dependencies of every theorem). The same traversal as
`Lean.CollectAxioms.collect`, except that a result is cached only when it is complete: one that met
a constant still being traversed further up (a cycle: an inductive type and its constructors, an
unsafe recursive definition) is cached by that constant's own frame, not before. `theorems`
checks the result against `Lean.collectAxioms` on a sample. Returns the axioms and the constants
still in progress that the traversal met. -/
partial def axiomsOf (env : Environment) (c : Name) :
    StateM (Std.HashMap Name NameSet × NameSet) (NameSet × NameSet) := do
  if let some r := (← get).1[c]? then return (r, {})
  if (← get).2.contains c then return ({}, ({} : NameSet).insert c)
  modify fun (m, p) => (m, p.insert c)
  let deps (ds : Array Name) : StateM (Std.HashMap Name NameSet × NameSet) (NameSet × NameSet) :=
    ds.foldlM (fun (acc, hit) d => do
      let (a, h) ← axiomsOf env d
      return (acc.union a, hit.union h)) ({}, {})
  let ofExpr (e : Expr) := deps e.getUsedConstants
  let both (x y : StateM (Std.HashMap Name NameSet × NameSet) (NameSet × NameSet)) := do
    let (a, h) ← x
    let (a', h') ← y
    return (a.union a', h.union h')
  let (r, hit) ← match env.find? c with
    | some (.axiomInfo v) => do let (a, h) ← ofExpr v.type; pure (a.insert c, h)
    | some (.defnInfo v) => both (ofExpr v.type) (ofExpr v.value)
    | some (.thmInfo v) => both (ofExpr v.type) (ofExpr v.value)
    | some (.opaqueInfo v) => both (ofExpr v.type) (ofExpr v.value)
    | some (.quotInfo _) => pure ({}, {})
    | some (.ctorInfo v) => ofExpr v.type
    | some (.recInfo v) => ofExpr v.type
    | some (.inductInfo v) => both (ofExpr v.type) (deps v.ctors.toArray)
    | none => pure ({}, {})
  let hit := hit.erase c
  modify fun (m, p) => (if hit.isEmpty then m.insert c r else m, p.erase c)
  pure (r, hit)

def runCore {α : Type} (env : Environment) (x : CoreM α) : IO α := do
  let (a, _) ← x.toIO { fileName := "<elf-pages>", fileMap := default } { env }
  pure a

def theorems (env : Environment) (P : Pinned) : IO (Array Thm) := do
  let mods := [P.ns ++ `Thms, P.ns ++ `Functions, P.ns ++ `Contracts].filterMap env.getModuleIdx?
  if mods.length < 2 then throw (IO.userError s!"{P.ns}.Thms/Functions not imported")
  let rs : Std.HashMap Name Role := Std.HashMap.ofList (← IO.ofExcept (roles env P.ns))
  let F := P.ns ++ `F
  let mut out : Array Thm := #[]
  let mut cache : Std.HashMap Name NameSet := {}
  for (n, ci) in env.constants.toList do
    unless (env.getModuleIdxFor? n).any mods.contains do continue
    let .thmInfo ti := ci | continue
    if n.isInternal then continue
    let claim ← match Claim.ofType? F ti.type with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"{n}: {e}")
    let role := match claim with
      | .part _ _ v => rs[v]?
      | .layout _ => some .layout
      | _ => none
    if let .part _ _ v := claim then
      if role.isNone then throw (IO.userError s!"{n}: the value {v} is not a part of {P.ns}.L/bodies/ld")
    let ((axs, _), cache') := (axiomsOf env n).run (cache, {})
    cache := cache'.1
    let axioms := axs.toArray.qsort Name.lt
    -- the shared cache against Lean's own `collectAxioms`, on the first theorems of each module
    if out.size < 3 || out.size % 1000 == 0 then
      let lean := (← runCore env (Lean.collectAxioms n)).qsort Name.lt
      unless lean == axioms do throw (IO.userError s!"{n}: axioms {axioms} but collectAxioms gives {lean}")
    let line ← runCore env do
      let r ← Lean.findDeclarationRanges? n
      pure (r.map (·.range.pos.line))
    let module := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!
      | none => .anonymous
    let stmt ← match claim with
      | .contract .. => some <$> runCore env (do return toString (← (Lean.Meta.ppExpr ti.type).run'))
      | _ => pure none
    let codeLen := match claim with
      | .contract _ code _ => ((env.find? code).bind (·.value? (allowOpaque := true))).bind
          fun v => (listLit? v).map (·.length)
      | _ => none
    if let .contract _ code loads := claim then
      unless loads.contains code do
        throw (IO.userError s!"{n}: the statement does not state that the contract loads {code} (no code identity)")
      if codeLen.isNone then throw (IO.userError s!"{n}: {code} is not a literal list of bytes")
    out := out.push { decl := n, claim, role, axioms, line, module, stmt, codeLen }
  pure (out.qsort fun a b => (a.line.getD 0) < (b.line.getD 0))

/-! ## Coverage -/

/-- Byte classes, by precedence. -/
def classNames : Array String := #["unknown", "raw", "zeros", "decoded"]

def coverage (P : Pinned) (thms : Array Thm) : Array Nat := Id.run do
  let mut c := Array.replicate P.size 0
  let mark (c : Array Nat) (o n k : Nat) : Array Nat := Id.run do
    let mut c := c
    for i in [o:min (o + n) P.size] do
      if c[i]! < k then c := c.set! i k
    c
  for s in P.L.sections do
    if s.header.kind != SHT_NOBITS then c := mark c s.header.offset s.header.size 1
  for ph in P.L.phdrs do
    if ph.kind == PT_LOAD then c := mark c ph.offset ph.fileSize 1
  for t in thms do
    match t.claim with
    | .zeros o n => c := mark c o n 2
    | .part ws _ _ => for s in ws do c := mark c s.off s.len 3
    | _ => pure ()
  c

def runs (c : Array Nat) : Array Json := Id.run do
  let mut out : Array Json := #[]
  let mut i := 0
  while i < c.size do
    let k := c[i]!
    let mut j := i
    while j < c.size && c[j]! == k do j := j + 1
    out := out.push (Json.arr #[jn i, jn (j - i), js classNames[k]!])
    i := j
  out

/-! ## Disassembly (external, unverified) -/

/-- The committed listing of `scripts/elf-reader/gen.sh`: GNU objdump's output, after two comment
lines (the objdump version and the command). -/
def listingPath (P : Pinned) : String := s!"examples/elf/disasm/{P.slug}.objdump"

def stripEnd (s : String) (p : Char → Bool) : String :=
  String.ofList (s.toList.reverse.dropWhile p).reverse

def hexVal (s : String) : Option Nat :=
  s.foldl (fun acc ch => acc.bind fun a =>
    if '0' ≤ ch ∧ ch ≤ '9' then some (16 * a + (ch.toNat - '0'.toNat))
    else if 'a' ≤ ch ∧ ch ≤ 'f' then some (16 * a + (ch.toNat - 'a'.toNat + 10))
    else none) (some 0)

/-- The listing's rows `(vaddr, offset, bytes, text, section, label)`; every row's bytes are checked
against the file. -/
def disassemble (P : Pinned) (bytes : ByteArray) : IO (Option (Json × Array Json)) := do
  let path := listingPath P
  let (lines, path) ← if ← System.FilePath.pathExists path then
      pure ((← IO.FS.readFile path).splitOn "\n", path)
    else
      -- no committed listing (files over 512 KiB): run objdump now, if there is one
      let some ver ← (do
          let o ← IO.Process.output { cmd := "objdump", args := #["--version"] }
          pure (if o.exitCode == 0 then (o.stdout.splitOn "\n").head? else none)) <|> pure none
        | return none
      let o ← IO.Process.output { cmd := "objdump", args := #["-d", "-w", "-z", P.path] }
      if o.exitCode != 0 then throw (IO.userError s!"objdump failed: {o.stderr}")
      pure (s!"# {ver}" :: s!"# objdump -d -w -z {P.path}" :: o.stdout.splitOn "\n", "(run when the pages were written)")
  let version := String.ofList ((lines.getD 0 "").toList.drop 2)
  let command := String.ofList ((lines.getD 1 "").toList.drop 2)
  unless command == s!"objdump -d -w -z {P.path}" do
    throw (IO.userError s!"{path}: not a listing of {P.path}")
  let mut rows : Array Json := #[]
  let mut secs : Array Json := #[]
  let mut sec := ""
  let mut label := ""
  let mut bad := 0
  for line in lines.drop 2 do
    if line.startsWith "Disassembly of section " then
      sec := stripEnd (String.ofList (line.toList.drop "Disassembly of section ".length)) (· == ':')
      secs := secs.push (js sec)
    else if line.endsWith ">:" then
      label := stripEnd ((line.splitOn "<").getD 1 "") (fun c => c == ':' || c == '>')
    else
      match line.splitOn "\t" with
      | a :: bs :: rest =>
        let a := a.trimAscii.toString
        if a.endsWith ":" then
          let some v := hexVal (String.ofList a.toList.dropLast) | continue
          let hexs := (bs.trimAscii.toString.splitOn " ").filter (· ≠ "")
          let some vals := hexs.mapM hexVal | continue
          let off := P.L.offsetOf v
          let ok := match off with
            | some f => (vals.zipIdx.all fun (b, i) => bytes.get! (f + i) == b.toUInt8) && f + vals.length ≤ bytes.size
            | none => false
          if !ok then bad := bad + 1
          rows := rows.push (Json.arr #[jn v, (match off with | some f => jn f | none => Json.null),
            js (String.join hexs), js ("\t".intercalate rest).trimAscii.toString, js sec, js label])
          label := ""
      | _ => pure ()
  if bad != 0 then throw (IO.userError s!"{P.slug}: {bad} disassembled instructions do not match the file's bytes")
  -- chunks of `chunkRows` rows (dis/SLUG/K.json), indexed by their first and last address
  let chunkRows := 4000
  let chunks := (List.range ((rows.size + chunkRows - 1) / chunkRows)).toArray.map fun k =>
    rows.extract (k * chunkRows) ((k + 1) * chunkRows)
  let firstAddr (c : Array Json) (i : Nat) : Json := ((c[i]?).bind fun r => (r.getArrVal? 0).toOption).getD Json.null
  pure <| some <| (Json.mkObj [
    ("tool", js version), ("command", js command), ("listing", js path), ("unverified", true),
    ("rows", jn rows.size),
    ("chunks", Json.arr (chunks.mapIdx fun k c => Json.arr #[js s!"dis/{P.slug}/{k}.json", firstAddr c 0, firstAddr c (c.size - 1), jn c.size])),
    ("note", js "External disassembler output, not checked in Lean. Each row's bytes were compared with the file's bytes at its address; the decoding into an instruction (mnemonic, operands, length) is objdump's alone. That bytes look like code, or sit in an executable section, does not make them executed."),
    ("sections", Json.arr secs)], chunks.map Json.arr)

/-! ## The page of a file -/

def thmJson (P : Pinned) (t : Thm) : Json :=
  let kind := match t.claim with
    | .part .. => (match t.role with | some (.symbol ..) => "symbol" | _ => "part")
    | .zeros .. => "zeros" | .layout _ => "layout" | .parses _ => "parses" | .contract .. => "contract"
  let ws := match t.claim with
    | .part ws _ _ => ws | .zeros o n => [⟨o, n⟩] | _ => []
  let kernelOnly := t.axioms.all (standardAxioms.contains ·)
  let status :=
    if t.axioms.contains ``sorryAx then "sorry"
    else if kernelOnly then "checked" else "checked-with-extra-axioms"
  let modFile := t.module.toString.replace "." "/" ++ ".lean"
  Json.mkObj [
    ("decl", js t.decl.toString), ("short", js (t.decl.replacePrefix P.ns .anonymous).toString),
    ("kind", js kind), ("part", match t.role with | some r => js r.key | none => Json.null),
    ("label", match t.role with
      | some r => js r.label
      | none => js (match t.claim with
        | .zeros o n => s!"padding: {n} zero bytes at {hex o}" | .parses _ => "the parse of the whole file"
        | .contract v _ _ => s!"code at {hex v} and its contract"
        | _ => kind)),
    ("windows", spansJson ws),
    ("axioms", Json.arr (t.axioms.map (js ·.toString))),
    ("kernelOnly", toJson kernelOnly), ("status", js status),
    ("module", js t.module.toString), ("file", js modFile),
    ("statement", match t.stmt with | some x => js x | none => Json.null),
    ("line", match t.line with | some l => jn l | none => Json.null)]

def segOf (L : Layout) (s : SectionHeader) : List Nat :=
  (L.phdrs.zipIdx.filter fun (ph, _) =>
    if s.kind == SHT_NOBITS then
      s.address != 0 && ph.virtualAddress ≤ s.address && s.address + s.size ≤ ph.virtualAddress + ph.memorySize && ph.kind == PT_LOAD
    else
      s.size != 0 && ph.offset ≤ s.offset && s.offset + s.size ≤ ph.offset + ph.fileSize).map (·.2)

def symJson (t : String) (i : Nat) (s : ObjectSymbol) : Json :=
  Json.mkObj [("table", js t), ("idx", jn i), ("name", js (nameStr s.name)), ("value", jn s.raw.value),
    ("size", jn s.raw.size), ("type", js (symType s.raw.info)), ("bind", js (symBind s.raw.info)),
    ("shndx", jn s.raw.sectionIndex)]

def bodyJson : Body → Json
  | .progbits d | .strtab d | .other d => Json.mkObj [("span", spansJson [d])]
  | .symbols t es => Json.mkObj [("count", jn es.length), ("table", js (if t == .symtab then "symtab" else "dynsym"))]
  | .relas es => Json.mkObj [("count", jn es.length), ("entries", Json.arr (es.toArray.map fun r =>
      Json.arr #[jn r.offset, jn (r.info % 2 ^ 32), jn (r.info / 2 ^ 32), js (toString r.addend)]))]
  | .rels es => Json.mkObj [("count", jn es.length)]
  | .relr ws => Json.mkObj [("count", jn ws.length)]
  | .dynamic es => Json.mkObj [("count", jn es.length)]
  | .gnuHash g => Json.mkObj [("nbuckets", jn g.nbuckets), ("symoffset", jn g.symoffset),
      ("bloomWords", jn g.bloom.length), ("bloomShift", jn g.bloomShift), ("chain", jn g.chain.length)]
  | .hash t => Json.mkObj [("nbuckets", jn t.buckets.length), ("nchains", jn t.chains.length)]
  | .versym es => Json.mkObj [("count", jn es.length), ("entries", toJson es)]
  | .verdef es => Json.mkObj [("count", jn es.length), ("names", Json.arr (es.toArray.map fun d =>
      Json.arr (d.names.toArray.map (js ∘ nameStr))))]
  | .verneed es => Json.mkObj [("count", jn es.length), ("files", Json.arr (es.toArray.map fun n =>
      Json.mkObj [("file", js (nameStr n.file)), ("versions", Json.arr (n.aux.toArray.map (js ∘ nameStr ∘ (·.name))))]))]
  | .notes ns => Json.mkObj [("count", jn ns.length), ("notes", Json.arr (ns.toArray.map fun n =>
      Json.mkObj [("name", js (nameStr n.name)), ("type", jn n.type), ("desc", spansJson [n.desc])]))]
  | .null | .noBits => Json.mkObj []

/-! ## Functions -/

/-- The version name of entry `i` of the dynamic symbol table (`.gnu.version`, then `.gnu.version_d`
or `.gnu.version_r`), with `@@` for the default version and `@` for a hidden one. -/
def versionOf (P : Pinned) (i : Nat) : Option String := do
  let vs ← P.bodies.findSome? fun | .versym es => some es | _ => none
  let raw ← vs[i]?
  let ndx := raw % 0x8000
  if ndx ≤ 1 then none
  let sep := if raw ≥ 0x8000 then "@" else "@@"
  let defs := P.bodies.flatMap fun | .verdef es => es | _ => []
  let needs := P.bodies.flatMap fun | .verneed es => es.flatMap (·.aux) | _ => []
  match defs.find? (·.ndx == ndx) with
  | some d => (d.names.head?).map fun n => sep ++ nameStr n
  | none => (needs.find? (·.other == ndx)).map fun a => "@" ++ nameStr a.name

/-- **The function table**: one row per `STT_FUNC`/`STT_GNU_IFUNC` entry of a symbol table. A row is
what the symbol table says (its theorem: `Pinned.*.Functions.sym_K_I`), with what follows from the
layout: the segment and section holding `[value, value + size)`, the file offset, aliases and
overlaps. A row with `size = 0` has an **unknown extent**; an `IFUNC` row is a resolver, not the
function chosen at load time; an undefined row is an import. -/
def functions (P : Pinned) (thms : Array Thm) : Array Json := Id.run do
  let L := P.L
  let symThm : Std.HashMap (Nat × Nat) Thm := thms.foldl (fun m t =>
    match t.role with | some (.symbol k i) => m.insert (k, i) t | _ => m) {}
  let contracts := thms.filterMap fun t => match t.claim with | .contract v _ _ => some (v, t) | _ => none
  let mut rows : Array (Nat × Nat × ObjectSymbol × String) := #[]
  for (sec, k) in L.sections.zipIdx do
    if let some (.symbols tab es) := P.bodies[k]? then
      for (e, i) in es.zipIdx do
        let ty := e.raw.info % 16
        if ty == 2 || ty == 10 then
          rows := rows.push (k, i, e, if tab == .symtab then "symtab" else "dynsym")
      let _ := sec
  let defined := rows.filter fun (_, _, e, _) => e.raw.sectionIndex != 0
  let mut out : Array Json := #[]
  for (k, i, e, tab) in rows do
    let v := e.raw.value
    let n := e.raw.size
    let undef := e.raw.sectionIndex == 0
    let abs := e.raw.sectionIndex == 0xfff1
    let ifunc := e.raw.info % 16 == 10
    let load := L.phdrs.zipIdx.find? fun (ph, _) =>
      ph.kind == PT_LOAD && ph.virtualAddress ≤ v && v < ph.virtualAddress + ph.memorySize
    let inFile := load.bind fun (ph, _) => if v < ph.virtualAddress + ph.fileSize then some (v - ph.virtualAddress + ph.offset) else none
    let owner := L.sections.zipIdx.find? fun (s, _) =>
      s.header.flags &&& 2 != 0 && s.header.address ≤ v && v < s.header.address + s.header.size
    let extent : String :=
      if undef then "import (undefined here)"
      else if abs then "absolute symbol"
      else if n == 0 then "unknown (st_size = 0)"
      else match load with
        | some (ph, _) => if v + n ≤ ph.virtualAddress + ph.fileSize then "known (st_value, st_size)" else "exceeds the segment's file bytes"
        | none => "not in a PT_LOAD"
    let aliases := (defined.filter fun (k', i', e', _) => (k', i') != (k, i) && e'.raw.value == v && !undef && v != 0).map fun (_, _, e', _) => nameStr e'.name
    let overlaps := if undef || n == 0 then #[] else
      (defined.filter fun (_, _, e', _) => e'.raw.size != 0 && e'.raw.value != v &&
        e'.raw.value < v + n && v < e'.raw.value + e'.raw.size).map fun (_, _, e', _) => nameStr e'.name
    let ver := if tab == "dynsym" then versionOf P i else none
    let thm := symThm[(k, i)]?
    let linked := if undef || n == 0 then #[] else
      -- the same address, and a code literal of exactly the symbol's size (code identity is
      -- checked in `theorems`: the contract loads that literal)
      (contracts.filter fun (cv, t) => cv == v && t.codeLen == some n).map fun (_, t) => js t.decl.toString
    out := out.push <| Json.mkObj [
      ("table", js tab), ("sec", jn k), ("idx", jn i), ("name", js (nameStr e.name)),
      ("version", match ver with | some x => js x | none => Json.null),
      ("type", js (symType e.raw.info)), ("bind", js (symBind e.raw.info)), ("visibility", jn (e.raw.other % 4)),
      ("shndx", jn e.raw.sectionIndex), ("value", jn v), ("size", jn n),
      ("defined", toJson (!undef)), ("ifunc", toJson ifunc), ("extent", js extent),
      ("offset", match inFile with | some o => jn o | none => Json.null),
      ("segment", match load with | some (_, j) => jn j | none => Json.null),
      ("segmentFlags", match load with | some (ph, _) => js (pflags ph.flags) | none => Json.null),
      ("section", match owner with | some (s, _) => js (nameStr s.name) | none => Json.null),
      ("aliases", toJson aliases), ("overlaps", toJson overlaps),
      ("theorem", match thm with | some t => js t.decl.toString | none => Json.null),
      ("contracts", Json.arr linked)]
  out

def page (P : Pinned) (thms : Array Thm) (dis : Option Json) : Json := Id.run do
  let L := P.L
  let h := L.header
  let thmFor (r : Role) : Json :=
    match thms.find? (·.role == some r) with
    | some t => js t.decl.toString
    | none => Json.null
  let cov := coverage P thms
  let count (k : Nat) := cov.foldl (fun n c => if c == k then n + 1 else n) 0
  let segs := L.phdrs.zipIdx.toArray.map fun (ph, i) => Json.mkObj [
    ("idx", jn i), ("type", js (ptName ph.kind)), ("kind", jn ph.kind), ("flags", js (pflags ph.flags)),
    ("offset", jn ph.offset), ("filesz", jn ph.fileSize), ("vaddr", jn ph.virtualAddress),
    ("paddr", jn ph.physicalAddress), ("memsz", jn ph.memorySize), ("align", jn ph.alignment),
    ("sections", toJson ((L.sections.zipIdx.filter fun (s, _) => (segOf L s.header).contains i).map (·.2))),
    ("theorem", thmFor (.phdr i))]
  let secs := L.sections.zipIdx.toArray.map fun (s, i) =>
    let sh := s.header
    let b := P.bodies[i]?.getD .null
    Json.mkObj [
      ("idx", jn i), ("name", js (nameStr s.name)), ("type", js (shtName sh.kind)), ("kind", jn sh.kind),
      ("flags", js (shflags sh.flags)), ("addr", jn sh.address), ("offset", jn sh.offset),
      ("size", jn sh.size), ("fileBytes", jn (if sh.kind == SHT_NOBITS then 0 else sh.size)),
      ("link", jn sh.link), ("info", jn sh.info), ("align", jn sh.alignment), ("entsize", jn sh.entrySize),
      ("segments", toJson (segOf L sh)), ("exec", toJson (sh.flags &&& 4 != 0)),
      ("body", js (bodyKind b)), ("decoded", toJson (bodyDecoded b)), ("detail", bodyJson b),
      ("headerTheorem", thmFor (.shdr i)), ("nameTheorem", thmFor (.name i)), ("bodyTheorem", thmFor (.body i))]
  let syms := L.sections.zipIdx.foldl (fun acc (_, i) =>
    match P.bodies[i]? with
    | some (.symbols t es) =>
      acc ++ es.zipIdx.toArray.map fun (s, k) =>
        symJson s!"{if t == .symtab then "symtab" else "dynsym"} (section {i})" k s
    | _ => acc) #[]
  let unsupported : List String :=
    (if L.sections.isEmpty then ["no section header table: sections, names and bodies are absent; the program headers and loader view are still read"] else []) ++
    (if L.sections.any (·.header.kind == SHT_SYMTAB) then [] else ["no .symtab (stripped): only the dynamic symbols (.dynsym) are listed"]) ++
    ["payloads kept as byte ranges, not decoded: PROGBITS (code, .rodata, .data, .eh_frame, .got, …), INIT/FINI arrays, string-table bytes no checked part reads; they are marked raw in the coverage map",
     "not supported by the reader: ELFCLASS32, big-endian (ELFDATA2MSB), extended section numbering (e_shnum = 0 with a large section 0), compressed sections; the reader accepts any e_machine",
     "not checked by the specification: alignment, overlap, and agreement of the section and loader views (Silmaril.Elf.Lookup.DynConsistent)"]
  Json.mkObj [
    ("schema", js "silmaril.elf-pages.v1"), ("slug", js P.slug), ("title", js P.title),
    ("path", js P.path), ("size", jn P.size), ("sha256", js P.sha256),
    ("provenance", Json.arr (P.provenance.toArray.map fun (k, v) => Json.arr #[js k, js v])),
    ("module", js P.ns.toString), ("bytesModule", js (P.ns ++ `Bytes).toString),
    ("header", Json.mkObj [
      ("class", js "ELF64"), ("data", js "little-endian"), ("osabi", jn h.osABI), ("abiversion", jn h.abiVersion),
      ("type", js (etName h.fileType)), ("machine", js (machineName h.machine)), ("machineCode", jn h.machine),
      ("version", jn h.version), ("entry", jn h.entry), ("phoff", jn h.programOffset), ("shoff", jn h.sectionOffset),
      ("flags", jn h.flags), ("ehsize", jn h.headerSize), ("phentsize", jn h.programEntrySize),
      ("phnum", jn h.programCount), ("shentsize", jn h.sectionEntrySize), ("shnum", jn h.sectionCount),
      ("shstrndx", jn h.sectionNameIndex), ("theorem", thmFor .header)]),
    ("segments", Json.arr segs), ("sections", Json.arr secs),
    ("loader", Json.mkObj [
      ("interp", match P.ld.interp with | some n => js (nameStr n) | none => Json.null),
      ("needed", Json.arr (P.ld.needed.toArray.map (js ∘ nameStr))),
      ("soname", match P.ld.soname with | some n => js (nameStr n) | none => Json.null),
      ("runpath", match P.ld.runpath with | some n => js (nameStr n) | none => Json.null),
      ("dynamic", Json.arr (P.ld.dynamic.toArray.map fun d => Json.arr #[jn d.tag, js (dtName d.tag), jn d.val])),
      ("theorem", thmFor .loader)]),
    ("symbols", Json.arr syms),
    ("functions", Json.arr (functions P thms)),
    ("theorems", Json.arr (thms.map (thmJson P))),
    ("coverage", Json.arr (runs cov)),
    ("coverageSummary", Json.mkObj ((List.range classNames.size).map fun k => (classNames[k]!, jn (count k)))),
    ("unsupported", toJson unsupported),
    ("disassembly", match dis with
      | some _ => Json.mkObj [("file", js s!"dis/{P.slug}.json")]
      | none => Json.mkObj [("file", Json.null), ("note", js s!"no listing at {listingPath P}, and no objdump when the pages were written")])]


/-! ## CLI: verified input/output records and specifications

A **record** names Lean declarations only. At generation time each name must exist in the
checked environment; its kind, status, axioms, statement and source line are read from the
declaration (`declInfo`), never from this list. The list says what a declaration is **for** in
the record (`role`): the theorem that proves the record, the reduction, the specification, an open
obligation, a trusted model. A name that does not exist stops the tool. -/

/-- The modules the CLI pages read (besides the pinned ELF modules). -/
def cliModules : Array Name := #[
  `Silmaril.Elf.CliExe.Start.Thms, `Silmaril.Elf.CliExe.Hello.Thms,
  `Silmaril.Elf.Link.Dyn.Hello.Thms, `Silmaril.Elf.Link.Dyn.LibMod.Hello.Thms,
  `Silmaril.Elf.Link.Dyn.Libc.Hello.Thms, `Silmaril.Elf.Link.Dyn.Program.Cli.Examples,
  `Silmaril.Process.LPS.Problems.GnuSha256sum.Close, `Silmaril.Process.LPS.Problems.Sha256Cli.EndToEnd, `Silmaril.Cli.Institution.Std.Thms, `Silmaril.Cli.Spec.Sha256sum.Thms,
  `Silmaril.Cli.Spec.WasmOpt.Thms, `Silmaril.Cli.Spec.Wac.Thms, `Silmaril.Cli.Spec.Jco.Thms,
  `Silmaril.Cli.Spec.Asyncify.Thms, `Silmaril.Cli.Spec.WasmTools.Thms,
  `Silmaril.Cli.Spec.WasmVerify.Thms, `Silmaril.Wasm.Binaryen.DriverSpec.Thms]

/-- A declaration's role in a record. -/
structure Edge where
  decl : Name
  role : String
  note : String := ""
  /-- **The record's anchors this declaration must be about**: groups of constants (binary,
  model, specification …); the declaration's statement, with registry rows (`silmaril.*`)
  unfolded, must mention a constant of every group. A proving or refinement edge without anchors is
  a *curated reference*: shown, never counted in a verdict. -/
  about : List (List Name) := []

structure IoRecord where
  id : String
  title : String
  binary : String
  elfSlug : Option String
  «sha256» : String
  level : String
  input : List (String × String)
  output : List (String × String)
  model : List (String × String)
  edges : List Edge
  limits : List String

structure SpecRecord where
  id : String
  title : String
  kind : String
  level : String
  implementation : List (String × String)
  edges : List Edge
  notes : List String

/-- An edge with anchors. -/
def Edge.on (e : Edge) (about : List (List Name)) : Edge := { e with about }

/-- Roles whose edges count towards a verdict or a refinement column. -/
def countingRole (r : String) : Bool :=
  r.startsWith "proves" || r.startsWith "refinement" || r.startsWith "checks"

-- Anchor groups (binary, model, specification) of the records.
def aHelloGcc : List Name := [`Silmaril.Elf.CliExe.Hello.helloGcc, `Silmaril.Elf.Link.Dyn.Program.Examples.helloGcc,
  `Silmaril.Elf.Link.Dyn.Hello.gccFile]
def aHelloClang : List Name := [`Silmaril.Elf.Link.Dyn.Hello.clangFile]
def aHelloSpec : List Name := [`Silmaril.Cli.Institution.Std.hello, `Silmaril.Elf.Link.Dyn.Program.Examples.helloSpec,
  `Silmaril.Elf.Link.Dyn.Hello.HelloDone]
def aGlibcModel : List Name := [`Silmaril.Elf.CliExe.glibcStream, `Silmaril.Elf.CliExe.glibcPin,
  `Silmaril.Elf.Link.Dyn.Program.MainProof, `Silmaril.Elf.Link.Dyn.Proc.MustQ]
def aPins : List Name := [`Silmaril.Elf.Link.Dyn.Program.libc]

def helloModel : List (String × String) := [
  ("machine", "Open9 x86-64 semantics for the executable's own instructions (_start, crt, main), from e_entry"),
  ("ABI", "System V AMD64 process entry: rip = e_entry, 16-byte aligned stack, argc/argv/envp (AtStart)"),
  ("loader", "Dyn.Loader / ExeLoaded: a trusted transcription of ld.so (any bases, eager binding)"),
  ("libc", "glibc 2.39 as contracts, one atomic step each (Silmaril.Elf.Link.Dyn.Proc): __libc_start_main, puts, exit, __cxa_finalize — trusted, glibc's code not executed"),
  ("library files", "libc.so.6 and ld.so: any files agreeing with the pinned lookup chunks (hypothesis)"),
  ("syscalls", "not modelled separately (inside the libc contracts)"),
  ("I/O bridge", "Program's world/outcome rows: stdin at main, stdout flushed at exit (trusted)"),
  ("claim scope", "every proved claim here is about the modelled process (the rows above); none is an end-to-end claim about glibc's or ld.so's code: real execution is helloGcc_real, conditional on the open Task.helloGccCrt and HelloLib")]

def ioRecords : List IoRecord := [
  { id := "hello-gcc", title := "hello world (gcc 13.3 -O2), dynamically linked against glibc 2.39"
    binary := "examples/dyn/pinned/hello-gcc", elfSlug := some "hello-gcc"
    «sha256» := "6964f3f23e27cfd2b6c26bd469cb210ff000dd359fc9988138cadc96683065c7"
    level := "L1 (stream) for the cli_exe row; L3 (full invocation) for the Program API claim"
    input := [("argv", "any (the claim is uniform: Level.liftAll)"), ("stdin", "any"),
      ("environment", "any"), ("files", "any (read-only; hello reads none)"),
      ("precondition", "writes to stdout succeed (Tier.reliable)")]
    output := [("stdout", "hello, world\n"), ("stderr", "empty (L3, helloSpec)"), ("exit", "0")]
    model := helloModel
    edges := [
      (⟨`Silmaril.Elf.CliExe.Hello.hello_cli, "proves the row", "silmaril.elf.cli.hello.gcc_o2: ELF facts, and Std.hello under glibcStream (the process model above, not concrete glibc)", []⟩ : Edge).on [[`Silmaril.Elf.CliExe.Hello.helloGcc], [`Silmaril.Elf.CliExe.glibcStream], [`Silmaril.Cli.Institution.Std.hello]],
      (⟨`Silmaril.Elf.CliExe.hello_start, "checks the start-up description", "silmaril.elf.start.hello.gcc_o2: a decidable check of a description of the file (B.ok), not a statement about runs; its execution consequence is the next two rows", []⟩ : Edge).on [[`Silmaril.Elf.CliExe.Hello.helloGcc], aPins, [`Silmaril.Elf.CliExe.GlibcStart]],
      (⟨`Silmaril.Elf.CliExe.hello_via_start, "proves (via the reduction)", "the execution consequence: hello's L3 spec, from the checked description and main's proof alone", []⟩ : Edge).on [[`Silmaril.Elf.CliExe.Hello.helloGcc], [`Silmaril.Elf.CliExe.glibcPin], [`Silmaril.Elf.Link.Dyn.Program.Examples.helloSpec]],
      ⟨`Silmaril.Elf.CliExe.cli_of_main, "reduction", "for any file: a checked start-up description and a proof of main give the file's CLI spec in the process model", []⟩,
      (⟨`Silmaril.Elf.Link.Dyn.Program.Examples.helloGcc_main, "proves main", "symbolic execution of main against puts's contract", []⟩ : Edge).on [[`Silmaril.Elf.Link.Dyn.Program.Examples.helloGcc], [`Silmaril.Elf.Link.Dyn.Program.MainProof], [`Silmaril.Elf.Link.Dyn.Program.Examples.helloSpec]],
      (⟨`Silmaril.Elf.Link.Dyn.Hello.hello_gcc, "proves (process model)", "MustQ over the modelled process (Open9 for the file's code, glibc as trusted contract steps, memory from the trusted loader relation, any libc.so.6/ld.so agreeing with the pinned chunks): every modelled run from _start ends with status 0 and hello, world on fd 1 (a prefix if writes may fail)", []⟩ : Edge).on [[`Silmaril.Elf.Link.Dyn.Hello.gccFile], [`Silmaril.Elf.Link.Dyn.Proc.MustQ, `Silmaril.Elf.Link.Dyn.Hello.gccWorld], [`Silmaril.Elf.Link.Dyn.Hello.HelloDone]],
      ⟨`Silmaril.Elf.Link.Dyn.Hello.NonVacuous.gcc_nonvacuous, "non-vacuity", "the hypotheses are met by a concrete loaded state with a run", []⟩,
      ⟨`Silmaril.Elf.Link.Dyn.Libc.helloGcc_on, "transfer", "verified on every libc specification above putsSpec", []⟩,
      ⟨`Silmaril.Cli.Institution.Std.hello, "specification", "Sen.prints helloBytes at L1", []⟩,
      ⟨`Silmaril.Elf.Link.Dyn.LibMod.helloGcc_real, "conditional (not proved end to end)", "real execution on a real machine X: assumes Task.helloGccCrt and HelloLib, both open", []⟩,
      ⟨`Silmaril.Elf.Link.Dyn.LibMod.Task.helloGccCrt, "open obligation (assumption of helloGcc_real)", "main on the C-runtime machine", []⟩,
      ⟨`Silmaril.Elf.Link.Dyn.LibMod.HelloLib, "open obligation (assumption of helloGcc_real)", "glibc's code realises init, gate, __libc_start_main, __cxa_finalize, puts", []⟩,
      ⟨`Silmaril.Elf.CliExe.GlibcRuntime, "shape (uninstantiated)", "silmaril.shapes.elf.glibc_runtime: a problem shape, not an open problem: no concrete real machine X or library module M exists yet, so there is no instance (and no glibc 2.39 problem) to prove; instantiating it is itself unmet. The concrete open assumptions are the two rows above", []⟩,
      ⟨`Silmaril.Elf.Link.Dyn.Proc.proc, "trusted model", "the process machine: Open9 plus the libc contracts", []⟩]
    limits := ["no end-to-end claim about concrete glibc: its code is not executed, its entry points are trusted contracts; real start-up and puts depend on the open Task.helloGccCrt and HelloLib (and the glibc_runtime shape, no row)",
      "the loader is a transcription of ld.so, trusted", "consumption, reads and the file log are not observed (L3 via toCli)"] },
  { id := "hello-clang", title := "hello world (clang 18.1 -O2), dynamically linked against glibc 2.39 (lazy binding)"
    binary := "examples/dyn/pinned/hello-clang", elfSlug := some "hello-clang"
    «sha256» := "ecad1a19e6e63e4828e9386a9c831dc6beb635c6858dc42d2c248e6397eaa713"
    level := "process level (no CLI-institution row yet)"
    input := [("argv", "any argc"), ("stdin", "not read"), ("environment", "any"), ("precondition", "reliable writes for the exact output")]
    output := [("stdout", "hello, world\n (a prefix if writes may fail)"), ("exit", "0")]
    model := helloModel ++ [("binding", "lazy: the resolver (_dl_runtime_resolve) as a contract")]
    edges := [(⟨`Silmaril.Elf.Link.Dyn.Hello.hello_clang, "proves (process model)", "MustQ over the modelled process (Open9 for the file's code, glibc and the lazy-binding resolver as trusted contract steps, the trusted loader relation): every modelled run from _start ends with status 0 and hello, world on fd 1 (a prefix if writes may fail)", []⟩ : Edge).on [[`Silmaril.Elf.Link.Dyn.Hello.clangFile], [`Silmaril.Elf.Link.Dyn.Proc.MustQ, `Silmaril.Elf.Link.Dyn.Hello.clangWorld], [`Silmaril.Elf.Link.Dyn.Hello.HelloDone]],
      ⟨`Silmaril.Elf.Link.Dyn.Proc.proc, "trusted model", "the process machine", []⟩]
    limits := ["no cli_exe row: the Program API description (Bin) of hello-clang is not stated as a CLI model here"] },
  { id := "sha256sum-min", title := "sha256sum-min: a libc-free static reimplementation of GNU coreutils 9.4 sha256sum (stdin tier)"
    binary := "Silmaril.Process.LPS.Problems.GnuSha256sum.Elf (the file as Lean literals; apps/sha256sum-min)", elfSlug := none
    «sha256» := "22fa6345cc5bed08f07d4d5a0836885118259a73402470e4d7f7a7a81ad42817"
    level := "LPS process (observable syscall traces)"
    input := [("argv", "the program name only (stdin tier)"), ("stdin", "any finite byte stream"),
      ("environment", "any admissible launch (stack placement in Linux's randomisation windows)"),
      ("files", "unchanged, not read"), ("refusals", "every refusal configuration (spurious syscall failures)")]
    output := [("stdout", "the SHA-256 hex digest of stdin followed by \"  -\\n\" (Apps.Sha256sum.sha256sum)"), ("stderr", "empty"), ("exit", "0"),
      ("termination", "every execution exits; the complete ideal trace occurs")]
    model := [("machine", "LPS x86-64 native machine (Silmaril.Process.LPS), with flag oracles"),
      ("ABI", "Linux x86-64 process entry (ExecEntry, admissible launch)"),
      ("loader", "LPS ELFImage loader of a static ET_EXEC"), ("libc", "none (libc-free)"),
      ("syscalls", "NativeX86.extendedSyscallSpec with refusals")]
    edges := [(⟨`Silmaril.Process.LPS.Problems.GnuSha256sum.Close.lpsTotal_close, "proves", "total correctness in LPS, stdin tier", []⟩ : Edge).on [[`Silmaril.Process.LPS.Problems.GnuSha256sum.snapshot, `Silmaril.Process.LPS.Problems.GnuSha256sum.file], [`Silmaril.Process.LPS.Problems.GnuSha256sum.TotalOn, `Silmaril.Process.LPS.Problems.GnuSha256sum.Total]],
      (⟨`Silmaril.Process.LPS.Problems.GnuSha256sum.Close.lpsPartial_close, "proves", "safety", []⟩ : Edge).on [[`Silmaril.Process.LPS.Problems.GnuSha256sum.snapshot, `Silmaril.Process.LPS.Problems.GnuSha256sum.file]],
      (⟨`Silmaril.Process.LPS.Problems.GnuSha256sum.Close.agree_close, "proves", "agreement with sha256-cli", []⟩ : Edge).on [[`Silmaril.Process.LPS.Problems.GnuSha256sum.file], [`Silmaril.Process.LPS.Problems.Sha256Cli.file]],
      ⟨`Silmaril.Cli.Spec.Sha256sum.spec, "specification (CLI institution)", "the standard sha256sum spec; this proof is stated in LPS, not as this sentence", []⟩]
    limits := ["stdin tier only (no options, no file operands)", "this binary is not the distro sha256sum of the ELF tab"] },
  { id := "sha256-cli", title := "sha256-cli: a freestanding SHA-256 filter (prints 64 hex digits and \\n)"
    binary := "apps/sha256-cli", elfSlug := none, «sha256» := "(see apps/sha256-cli/manifest.json)"
    level := "LPS process"
    input := [("stdin", "any finite byte stream"), ("argv", "any")]
    output := [("stdout", "64 hex digits of SHA-256(stdin) and \\n"), ("exit", "0")]
    model := [("machine", "LPS x86-64 native machine"), ("libc", "none"), ("syscalls", "read, write, exit (LPS spec)")]
    edges := [(⟨`Silmaril.Process.LPS.Problems.Sha256Cli.sha256cli_lps_total, "proves", "total correctness in LPS", []⟩ : Edge).on [[`Silmaril.Process.LPS.Problems.Sha256Cli.snapshot, `Silmaril.Process.LPS.Problems.Sha256Cli.file], [`Silmaril.Process.LPS.Problems.Sha256Cli.TotalOn, `Silmaril.Process.LPS.Problems.Sha256Cli.Total]]]
    limits := [] },
  { id := "gnu-sha256sum", title := "GNU coreutils 9.4 sha256sum (Ubuntu, dynamic, glibc + libcrypto)"
    binary := "examples/elf/pinned/gnu-sha256sum", elfSlug := some "gnu-sha256sum"
    «sha256» := "4d2db56c867e5324e0084c9e897f6360d37517de77ac96f2bd31494223d69a60"
    level := "—"
    input := [], output := []
    model := []
    edges := [⟨`Silmaril.Cli.Spec.Sha256sum.spec, "specification", "the standard spec it would be stated against", []⟩]
    limits := ["no verified input/output pair in this repository: the binary is parsed part by part (ELF tab), its functions listed, nothing about its behaviour is proved here"] }]

def clapEdges (ns : Name) (refines : Bool) : List Edge :=
  [⟨ns ++ `tool, "specification", "the args grammar (clap dialect) and its derived help, usage errors and exit codes", []⟩,
   (⟨ns ++ `tool_wf, "proves", "the grammar is well formed", []⟩ : Edge).on [[ns ++ `tool]]] ++
  (if refines then [(⟨ns ++ `main_refines, "refinement (by construction)", "a main built as tool.main on a dispatch refines the derived spec", []⟩ : Edge).on
      [[ns ++ `tool], [`Silmaril.Cli.Clap.Tool.spec]],
    (⟨ns ++ `main_front, "refinement (front end)", "the front end's help, usage errors and exit codes", []⟩ : Edge).on
      [[ns ++ `tool], [`Silmaril.Cli.Clap.Tool.frontSpec]]] else [])

def specRecords : List SpecRecord := [
  { id := "hello", title := "hello: prints hello, world and exits 0", kind := "sentence", level := "L1"
    implementation := [("ELF", "hello-gcc (examples/dyn/pinned/hello-gcc), via silmaril.elf.cli.hello.gcc_o2")]
    edges := [⟨`Silmaril.Cli.Institution.Std.hello, "specification", "", []⟩,
      (⟨`Silmaril.Cli.Institution.Std.hello_agree, "proves", "two models satisfying it agree", []⟩ : Edge).on [[`Silmaril.Cli.Institution.Std.hello]],
      (⟨`Silmaril.Elf.CliExe.Hello.hello_cli, "refinement proof", "hello-gcc satisfies it (glibcStream)", []⟩ : Edge).on [[`Silmaril.Elf.CliExe.Hello.helloGcc], [`Silmaril.Elf.CliExe.glibcStream], [`Silmaril.Cli.Institution.Std.hello]]]
    notes := [] },
  { id := "cat", title := "cat: copies stdin to stdout", kind := "sentence", level := "L1"
    implementation := [("ELF", "cat-stdin-gcc (examples/dyn/pinned/cat-stdin-gcc)")]
    edges := [⟨`Silmaril.Cli.Institution.Std.cat, "specification", "", []⟩,
      (⟨`Silmaril.Elf.Link.Dyn.Program.Examples.catStdinGcc_filter, "refinement proof", "the L1 reduct of its Program model satisfies the filter", []⟩ : Edge).on [[`Silmaril.Elf.Link.Dyn.Program.Examples.catStdinGcc], [`Silmaril.Elf.Link.Dyn.Program.x86Model], [`Silmaril.Cli.Institution.Std.cat]]]
    notes := ["no cli_exe row for cat-stdin-gcc yet"] },
  { id := "sha256sum", title := "sha256sum (GNU coreutils), at every level of the CLI institution", kind := "specification", level := "L1–L3"
    implementation := [("Lean", "Silmaril.Apps.Sha256sum.sha256sum (an executable specification)"),
      ("ELF", "sha256sum-min (LPS proof, not stated as this sentence)")]
    edges := [⟨`Silmaril.Cli.Spec.Sha256sum.spec, "specification", "", []⟩,
      ⟨`Silmaril.Cli.Institution.Std.sha256Stdin, "specification (L1 sentence)", "", []⟩,
      (⟨`Silmaril.Cli.Spec.Sha256sum.spec_le_lift_stdin, "proves", "the stdin domain refines the L1 sentence", []⟩ : Edge).on [[`Silmaril.Cli.Spec.Sha256sum.spec], [`Silmaril.Cli.Institution.Std.sha256Stdin]]]
    notes := [] },
  { id := "wasm-opt", title := "wasm-opt (silmaril's Binaryen-style optimiser)", kind := "args grammar", level := "L3"
    implementation := [("tool", "tools/wasm-opt"), ("Lean", "Silmaril.Wasm.Binaryen.Driver")]
    edges := clapEdges `Silmaril.Cli.Spec.WasmOpt false ++
      [(⟨`Silmaril.Wasm.Binaryen.DriverSpec.selectable_names, "proves", "the grammar's stage names are exactly the driver's selectable stages", []⟩ : Edge).on [[`Silmaril.Cli.Spec.WasmOpt.passNames], [`Silmaril.Wasm.Binaryen.Driver.selectableStages]],
       (⟨`Silmaril.Wasm.Binaryen.DriverSpec.parseArgs_verifiedStages, "proves", "the driver's reading of the verified-stages path", []⟩ : Edge).on [[`Silmaril.Wasm.Binaryen.Driver.parseArgs]]]
    notes := ["the optimisation passes' semantics are proved elsewhere (Silmaril.Wasm.Binaryen); this row is the command line"] },
  { id := "wasm-wac", title := "wasm-wac", kind := "args grammar", level := "L3"
    implementation := [("tool", "tools/wasm-wac/WasmWac.lean"), ("Lean", "Silmaril.Wasm.Wac.Tool")]
    edges := clapEdges `Silmaril.Cli.Spec.Wac true, notes := [] },
  { id := "wasm-jco", title := "wasm-jco", kind := "args grammar", level := "L3"
    implementation := [("tool", "tools/wasm-jco/WasmJco.lean"), ("Lean", "Silmaril.Wasm.JcoTool")]
    edges := clapEdges `Silmaril.Cli.Spec.Jco true, notes := [] },
  { id := "wasm-asyncify", title := "wasm-asyncify", kind := "args grammar", level := "L3"
    implementation := [("tool", "tools/wasm-asyncify/WasmAsyncify.lean"), ("Lean", "Silmaril.Wasm.FX.Asyncify.Tool")]
    edges := clapEdges `Silmaril.Cli.Spec.Asyncify true, notes := [] },
  { id := "wasm-tools", title := "wasm-tools", kind := "args grammar", level := "L3"
    implementation := [("tool", "tools/wasm-tools")]
    edges := clapEdges `Silmaril.Cli.Spec.WasmTools false, notes := [] },
  { id := "wasm-verify", title := "wasm-verify", kind := "args grammar", level := "L3"
    implementation := [("tool", "tools/wasm-verify/WasmVerify.lean")]
    edges := clapEdges `Silmaril.Cli.Spec.WasmVerify false, notes := [] }]

/-- What the environment says about a declaration. -/
def declInfo (env : Environment) (thmOf : Std.HashMap Name Name)
    (cache : Std.HashMap Name NameSet) (d : Name) : IO (Json × Std.HashMap Name NameSet) := do
  let some ci := env.find? d | throw (IO.userError s!"cli pages: {d} is not in the environment")
  let module := match env.getModuleIdxFor? d with
    | some i => env.header.moduleNames[i.toNat]!
    | none => .anonymous
  let line ← runCore env do return ((← Lean.findDeclarationRanges? d).map (·.range.pos.line))
  let stmt ← runCore env do return toString (← (Lean.Meta.ppExpr ci.type).run')
  let ((axs, _), cache') := (axiomsOf env d).run (cache, {})
  let axioms := axs.toArray.qsort Name.lt
  -- a statement, or a family of statements (`∀ params, Prop`, e.g. an open `Task` or a shape)
  let isProp ← runCore env do return (← (Lean.Meta.isProp ci.type).run')
  let isPropFamily : Bool ← runCore env do
    let m : Lean.MetaM Bool := Lean.Meta.forallTelescopeReducing ci.type fun _ b => return b.isProp
    return (← m.run')
  let kind : String := match ci with
    | .thmInfo _ => "theorem"
    | .inductInfo _ => if isPropFamily then "statement (a structure of obligations)" else "inductive type"
    | .defnInfo _ => if isProp then "statement" else if isPropFamily then "statement (parametrised)" else "definition"
    | _ => "declaration"
  let status : String := match ci with
    | .thmInfo _ =>
      if axioms.contains ``sorryAx then "sorry"
      else if axioms.all (standardAxioms.contains ·) then "proved" else "proved with other axioms"
    | _ => match thmOf[d]? with
      | some t => s!"proved by {t}"
      | none =>
        if isProp then "statement, not proved here"
        else if isPropFamily then "parametrised statement, no instance proved here"
        else "definition"
  pure (Json.mkObj [("decl", js d.toString), ("kind", js kind), ("status", js status),
    ("axioms", Json.arr (axioms.map (js ·.toString))), ("module", js module.toString),
    ("file", js (module.toString.replace "." "/" ++ ".lean")),
    ("line", match line with | some l => jn l | none => Json.null),
    ("statement", js (if stmt.length > 4000 then (String.ofList (stmt.toList.take 4000)) ++ " …" else stmt))], cache'.1)

/-! ### Association: is the declaration about the record? -/

/-- The constants a statement mentions, unfolding `Silmaril`/`silmaril` definitions (registry rows,
goals, models) up to depth 5. -/
def stmtClosure (env : Environment) (e : Expr) : NameSet := Id.run do
  let mut out : NameSet := {}
  let mut todo : List (Name × Nat) := e.getUsedConstants.toList.map (·, 0)
  let mut fuel := 5000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | (c, d) :: rest =>
      todo := rest
      if out.contains c then continue
      out := out.insert c
      if d < 5 && ((`silmaril).isPrefixOf c || (`Silmaril).isPrefixOf c) then
        if let some (.defnInfo v) := env.find? c then todo := todo ++ v.value.getUsedConstants.toList.map (·, d + 1)
  return out

/-- Some closed subterm of the statement (under its binders) is definitionally equal to the
constant `a` (default transparency): `Sen.filter id` is `Std.cat`. -/
def occursDefEq (env : Environment) (stmt : Expr) (a : Name) : IO Bool := runCore env do
  let some ci := env.find? a | return false
  if !ci.levelParams.isEmpty then return false
  Lean.Meta.MetaM.run' do
    Lean.Meta.forallTelescopeReducing stmt fun _ body => do
      let ty ← Lean.Meta.inferType (.const a [])
      let mut found := false
      -- every closed application subterm of the body
      let subs : Array Expr := Id.run do
        let mut acc : Array Expr := #[]
        let mut stack : List Expr := [body]
        let mut n := 0
        while n < 2000 do
          n := n + 1
          match stack with
          | [] => break
          | x :: rest =>
            stack := rest
            if !x.hasLooseBVars then acc := acc.push x
            match x with
            | .app f a => stack := f :: a :: stack
            | .mdata _ b => stack := b :: stack
            | _ => pure ()
        return acc
      for sub in subs do
        if found then break
        try
          if ← Lean.Meta.isDefEq (← Lean.Meta.inferType sub) ty then
            if ← Lean.Meta.isDefEq sub (.const a []) then found := true
        catch _ => pure ()
      return found

/-- The statement a declaration makes: a theorem's type, a definition's value. -/
def statementOf (env : Environment) (d : Name) : Option Expr :=
  match env.find? d with
  | some (.thmInfo t) => some t.type
  | some (.defnInfo v) => some v.value
  | some ci => some ci.type
  | none => none

/-- **The association check**: for each anchor group, the statement mentions one of its constants
(after unfolding registry rows and goals), or has a subterm definitionally equal to one. -/
def checkAssociation (env : Environment) (e : Edge) : IO (Except String Unit) := do
  let some stmt := statementOf env e.decl | return .error s!"{e.decl} is not in the environment"
  let cl := stmtClosure env stmt
  for g in e.about do
    if g.any cl.contains then continue
    let mut ok := false
    for a in g do
      if !ok then ok ← occursDefEq env stmt a
    unless ok do
      return .error s!"{e.decl} ({e.role}) is not about the record: it mentions none of {g}"
  return .ok ()

def edgesJson (env : Environment) (thmOf : Std.HashMap Name Name) (cache : Std.HashMap Name NameSet)
    (es : List Edge) : IO (Json × Std.HashMap Name NameSet) := do
  let mut out : Array Json := #[]
  let mut c := cache
  for e in es do
    let (j, c') ← declInfo env thmOf c e.decl
    c := c'
    let assoc ← if countingRole e.role then
        if e.about.isEmpty then pure "curated"
        else match ← checkAssociation env e with
          | .ok () => pure "checked"
          | .error msg => throw (IO.userError s!"cli pages: {msg}")
      else pure "n/a"
    let j := (j.setObjVal! "association" (js assoc)).setObjVal! "about"
      (toJson (e.about.map (·.map (·.toString))))
    -- an uninstantiated shape is neither an open problem nor a missing proof
    let j := if e.role.startsWith "shape" then j.setObjVal! "status" (js "uninstantiated shape") else j
    -- a non-theorem used as a specification or a model is that, not an open obligation
    let j := if (e.role.startsWith "specification" || e.role.startsWith "trusted model") &&
        j.getObjValD "kind" != js "theorem" then
      j.setObjVal! "status" (js (if e.role.startsWith "trusted" then "trusted model" else "specification"))
      else j
    -- a theorem with open hypotheses is proved only as an implication: never shown as proved
    let j := if e.role.startsWith "conditional" && j.getObjValD "status" == js "proved" then
      j.setObjVal! "status" (js "proved implication; hypotheses open") else j
    out := out.push ((j.setObjVal! "role" (js e.role)).setObjVal! "note" (js e.note))
  pure (Json.arr out, c)

def pairs (xs : List (String × String)) : Json := Json.arr (xs.toArray.map fun (k, v) => Json.arr #[js k, js v])

def cliIndex (env : Environment) : IO Json := do
  -- closed statements proved by a theorem whose type is exactly the statement's constant
  let mut thmOf : Std.HashMap Name Name := {}
  let wanted : Std.HashSet Name := Std.HashSet.ofList
    ((ioRecords.flatMap (·.edges)) ++ (specRecords.flatMap (·.edges)) |>.map (·.decl))
  for (n, ci) in env.constants.toList do
    if let .thmInfo ti := ci then
      if let .const c _ := ti.type.consumeMData then
        if wanted.contains c && !n.isInternal then thmOf := thmOf.insert c n
  let mut cache : Std.HashMap Name NameSet := {}
  let mut ios : Array Json := #[]
  for r in ioRecords do
    let (es, c) ← edgesJson env thmOf cache r.edges
    cache := c
    ios := ios.push (Json.mkObj [("id", js r.id), ("title", js r.title), ("binary", js r.binary),
      ("elfSlug", match r.elfSlug with | some s => js s | none => Json.null), ("sha256", js r.sha256),
      ("level", js r.level), ("input", pairs r.input), ("output", pairs r.output), ("model", pairs r.model),
      ("edges", es), ("limits", toJson r.limits)])
  let mut specs : Array Json := #[]
  for r in specRecords do
    let (es, c) ← edgesJson env thmOf cache r.edges
    cache := c
    specs := specs.push (Json.mkObj [("id", js r.id), ("title", js r.title), ("kind", js r.kind),
      ("level", js r.level), ("implementation", pairs r.implementation), ("edges", es), ("notes", toJson r.notes)])
  pure (Json.mkObj [("schema", js "silmaril.cli-pages.v1"), ("io", Json.arr ios), ("specs", Json.arr specs)])

/-! ## Assembly functions (`elf/asm.json`, `elf/asm-decls.json`) -/

/-- The committed output of `tools/elf-asm` (docs/projects/elf-asm.md). -/
def asmPath : String := "examples/elf-asm/samples.json"
def asmSchema : String := "silmaril.elf.asm/1"
def asmModules : Array Name := #[`Silmaril.Elf.Asm.Example.Thms, `Silmaril.Elf.Asm.Example.Reloc.Thms,
  `Silmaril.Elf.Asm.Example.LeafArith.Thms, `Silmaril.Elf.Abi.Asm.LeafArith.Thms,
  `Silmaril.Elf.Abi.Asm.LeafArith.Decoys, `Silmaril.Elf.Pin.Examples]

/-- The declaration names an assembly JSON mentions: its files, its functions and their files,
decodings, evidence and (when present) ABI conformance rows. -/
def asmDeclNames (j : Json) : Array String := Id.run do
  let arr (x : Json) (k : String) : Array Json := ((x.getObjValD k).getArr?.toOption).getD #[]
  let str (x : Json) (k : String) : Option String := (x.getObjValD k).getStr?.toOption
  let mut out : Array String := (arr j "files").filterMap (str · "decl")
  for f in arr j "functions" do
    out := out ++ ([str f "decl", str f "file"].filterMap id).toArray
    for k in ["decodings", "evidence", "abi", "abiRows"] do
      out := out ++ (arr f k).filterMap (str · "decl")
    out := out ++ (arr f "abiRows").filterMap (str · "bridge")
    out := out ++ (arr f "abiRows").filterMap (str · "fileEq")
  pure (out.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[])


/-- **A conformance row of an assembly record** (curated, then checked exactly). The curated
fields name declarations and the values a reader is told; `abiLinkJson` derives every shown value
from the registered problem's own arguments and refuses the link unless:

* the bridge's type is exactly `SameFunction c r`, with `c` the problem's code argument and `r` the
  record (`Silmaril.Elf.Abi.Asm.LeafArith.SameFunction`: entry address, extent and bytes);
* `fileEq`'s type is exactly `@Eq Blob <the record's file constant> <the problem's file argument>`
  (a kernel theorem such as `Silmaril.Elf.Pin.Examples.leafArith_record_file`, #978): the record's
  file and the row's file are the same blob, not only the same path and SHA-256 strings (those stay
  displayed metadata);
* the problem's function name is the record's name, and its mode, frame and id are the curated
  ones;
* the solution's type is exactly the problem.

Status comes from the solution's and the bridge's axioms. -/
structure AbiLink where
  record : Name
  bridge : Name
  /-- A theorem `record file = the problem's file`. -/
  fileEq : Name
  problemConst : Name
  solution : Name
  /-- What the reader is told; each is checked against the problem. -/
  problemId : String
  mode : String
  frame : Nat
  deriving Inhabited

def abiLinks : List AbiLink := [
  { record := `Silmaril.Elf.Asm.Example.LeafArith.clamp, bridge := `Silmaril.Elf.Abi.Asm.LeafArith.clamp_record_code
    fileEq := `Silmaril.Elf.Pin.Examples.leafArith_record_file
    problemConst := `silmaril.elf.abi.leaf_arith.clamp_i32, solution := `Silmaril.Elf.Abi.LeafArith.clamp_row
    problemId := "silmaril.elf.abi.leaf_arith.clamp_i32", mode := "total", frame := 0 },
  { record := `Silmaril.Elf.Asm.Example.LeafArith.sat, bridge := `Silmaril.Elf.Abi.Asm.LeafArith.sat_record_code
    fileEq := `Silmaril.Elf.Pin.Examples.leafArith_record_file
    problemConst := `silmaril.elf.abi.leaf_arith.sat_add_u32, solution := `Silmaril.Elf.Abi.LeafArith.sat_row
    problemId := "silmaril.elf.abi.leaf_arith.sat_add_u32", mode := "total", frame := 0 }]

/-- A record's file, as `asm.json` names it: its declaration, path and SHA-256. -/
structure RecordFile where
  name : String
  path : String
  sha : String

/-- The problem's arguments: an instance (`silmaril instance … := shape (A := …) …`) unfolded to
`Silmaril.Elf.Abi.AbiConforms A M mode hdr f p F b c frame S` (the definition of the shape `silmaril.shapes.elf.abi_conforms`). -/
partial def abiConformsArgs (env : Environment) (e : Expr) : Option (Array Expr) :=
  let e := e.headBeta
  let fn := e.getAppFn
  match fn with
  | .const n _ =>
    if n == `Silmaril.Elf.Abi.AbiConforms then
      let as := e.getAppArgs
      if as.size == 11 then some as else none
    else match env.find? n with
      | some (.defnInfo d) => abiConformsArgs env (d.value.beta e.getAppArgs)
      | _ => none
  | _ => none

def litNat? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | e => match e.getAppFn, e.getAppArgs with
    | .const ``OfNat.ofNat _, #[_, .lit (.natVal n), _] => some n
    | _, _ => none

def abiLinkJson (env : Environment) (l : AbiLink) (rf : RecordFile) (recordName : String) :
    IO (Except String Json) := do
  let some (.defnInfo pd) := env.find? l.problemConst | return .error s!"{l.problemConst}: not a registered problem"
  let some args := abiConformsArgs env pd.value
    | return .error s!"{l.problemConst}: not an instance of silmaril.shapes.elf.abi_conforms"
  let (A, M, mode, f, F, c, frame) := (args[0]!, args[1]!, args[2]!, args[4]!, args[6]!, args[8]!, args[9]!)
  -- the bridge: exactly `SameFunction c record`
  let some (.thmInfo bi) := env.find? l.bridge | return .error s!"{l.bridge}: not a theorem"
  let want := mkApp2 (.const `Silmaril.Elf.Abi.Asm.LeafArith.SameFunction []) c (.const l.record [])
  unless bi.type.consumeMData == want do
    return .error s!"{l.bridge}: its type is not exactly SameFunction <the problem's code> {l.record}"
  -- the file: a theorem `record file = problem file`, exactly (the strings are only displayed)
  let some (.thmInfo fi) := env.find? l.fileEq | return .error s!"{l.fileEq}: not a theorem"
  let fileOk : Bool := match fi.type.consumeMData with
    | .app (.app (.app (.const ``Eq _) α) lhs) rhs =>
      α == .const ``Silmaril.X86.Link.Blob [] && lhs == .const rf.name.toName [] && rhs == F
    | _ => false
  unless fileOk do
    return .error s!"{l.fileEq}: its type is not exactly {rf.name} = <the problem's file>"
  let some P := pinned.find? (fun P => F == .const (P.ns ++ `F) []) | return .error s!"{l.problemConst}: its file is no pinned file"
  -- name, mode, frame, id
  unless f == .lit (.strVal recordName) do return .error s!"{l.problemConst}: its function is not {recordName}"
  let modeS := match mode with | .const n _ => n.componentsRev.head!.toString | _ => "?"
  unless modeS == l.mode do return .error s!"{l.problemConst}: mode {modeS}, not {l.mode}"
  unless litNat? frame == some l.frame do return .error s!"{l.problemConst}: frame is not {l.frame}"
  unless l.problemConst.toString == l.problemId do return .error s!"{l.problemConst}: id is not {l.problemId}"
  -- the solution
  let some (.thmInfo si) := env.find? l.solution | return .error s!"{l.solution}: not a theorem"
  unless si.type.consumeMData == .const l.problemConst [] do
    return .error s!"{l.solution}: does not state exactly {l.problemConst}"
  let abiId ← runCore env do
    let r : Lean.MetaM Expr := Lean.Meta.whnfD (mkApp (.const `Silmaril.Machine.Abi.Conformance.AbiDef.id []) A)
    return (← r.run')
  let abiIdS := match abiId with | .lit (.strVal s) => s | _ => toString A
  let machine := match M.getAppFn with | .const n _ => n.toString | _ => toString M
  let ((axs, _), _) := (axiomsOf env l.solution).run ({}, {})
  let ((baxs, _), _) := (axiomsOf env l.bridge).run ({}, {})
  let ((faxs, _), _) := (axiomsOf env l.fileEq).run ({}, {})
  let std (xs : NameSet) := xs.toArray.all (standardAxioms.contains ·)
  let status := if [axs, baxs, faxs].any (·.contains ``sorryAx) then "sorry"
    else if std axs && std baxs && std faxs then "proved" else "proved with other axioms"
  pure (.ok (Json.mkObj [("problemId", js l.problemId), ("decl", js l.solution.toString),
    ("bridge", js l.bridge.toString), ("abiId", js abiIdS), ("machine", js machine),
    ("mode", js modeS), ("frame", jn l.frame), ("status", js status),
    ("limits", js "the machine is a restricted model; FP, vector and control state is carried by the model, not proved; real x86 only under Faithful"),
    ("fileEq", js l.fileEq.toString),
    ("fileIdentity", js s!"{rf.name} = {P.ns ++ `F} ({l.fileEq}); {P.path}, SHA-256 {P.«sha256»} (displayed)"),
    ("association", js "checked")]))

/-- **Decoy links the checker must refuse** (`Silmaril.Elf.Abi.Asm.LeafArith.Decoys`, and
tampered curated values). -/
def abiLinkDecoys : List (String × AbiLink × Option RecordFile) :=
  let clampL := abiLinks[0]!
  [("clamp record linked to the sat_add_u32 row with clamp's bridge", { clampL with problemConst := `silmaril.elf.abi.leaf_arith.sat_add_u32, solution := `Silmaril.Elf.Abi.LeafArith.sat_row, problemId := "silmaril.elf.abi.leaf_arith.sat_add_u32" }, none),
   ("bridge True ∨ SameFunction satCode clamp", { clampL with bridge := `Silmaril.Elf.Abi.Asm.LeafArith.Decoys.or_true, problemConst := `silmaril.elf.abi.leaf_arith.sat_add_u32, solution := `Silmaril.Elf.Abi.LeafArith.sat_row, problemId := "silmaril.elf.abi.leaf_arith.sat_add_u32" }, none),
   ("bridge satCode = satCode ∧ clamp = clamp", { clampL with bridge := `Silmaril.Elf.Abi.Asm.LeafArith.Decoys.both_refl, problemConst := `silmaril.elf.abi.leaf_arith.sat_add_u32, solution := `Silmaril.Elf.Abi.LeafArith.sat_row, problemId := "silmaril.elf.abi.leaf_arith.sat_add_u32" }, none),
   ("sat's bridge for the clamp record", { clampL with bridge := `Silmaril.Elf.Abi.Asm.LeafArith.sat_record_code }, none),
   ("wrong file", clampL, some { name := "x", path := "examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums", sha := "00" }),
   ("a record of another pin carrying leaf-arith's path and SHA-256 strings", clampL,
      some ⟨"Silmaril.Elf.Staged.Pinned.ZlibChecksums.F", "examples/elf-ladder/01-leaf-arith/pinned/leaf-arith",
        "d9cf1e5ddd99bcb2abeca7ae44f899c03bbd93586458a7367e1ff6d4a6472484"⟩),
   ("the file theorem of another pair (zlibChecksums_exe_eq)", { clampL with fileEq := `Silmaril.Elf.Pin.Examples.zlibChecksums_exe_eq }, none),
   ("a non-equality as the file theorem", { clampL with fileEq := `Silmaril.Elf.Abi.Asm.LeafArith.clamp_record_code }, none),
   ("wrong mode", { clampL with mode := "safe" }, none),
   ("wrong frame", { clampL with frame := 128 }, none),
   ("wrong problem id", { clampL with problemId := "silmaril.elf.abi.leaf_arith.sat_add_u32" }, none),
   ("solution of another problem", { clampL with solution := `Silmaril.Elf.Abi.LeafArith.sat_row }, none)]

/-- The leaf-arith record file, as `asm.json` names it. -/
def leafRecordFile : RecordFile :=
  { name := "Silmaril.Elf.Asm.Example.LeafArith.F", path := "examples/elf-ladder/01-leaf-arith/pinned/leaf-arith",
    sha := "d9cf1e5ddd99bcb2abeca7ae44f899c03bbd93586458a7367e1ff6d4a6472484" }

/-- Every true link is accepted and every decoy refused; the number of failures. -/
def abiLinkSelfTest (env : Environment) : IO Nat := do
  let mut failed := 0
  for l in abiLinks do
    if let .error m ← abiLinkJson env l leafRecordFile (if l.record == `Silmaril.Elf.Asm.Example.LeafArith.clamp then "clamp_i32" else "sat_add_u32") then
      IO.eprintln s!"elf-pages abi links: a true link is refused ({m})"; failed := failed + 1
  let mut refused := 0
  for (what, l, rf) in abiLinkDecoys do
    match ← abiLinkJson env l (rf.getD leafRecordFile) "clamp_i32" with
    | .ok _ => IO.eprintln s!"elf-pages abi links: the checker accepted '{what}'"; failed := failed + 1
    | .error m => refused := refused + 1; IO.println s!"elf-pages abi links: refused '{what}': {m}"
  IO.println s!"elf-pages abi links: {abiLinks.length} true links accepted, {refused} of {abiLinkDecoys.length} decoys refused"
  pure failed

/-- `elf/asm.json` (the committed file, with each record's checked conformance rows added as
`abiRows`) and `elf/asm-decls.json` (where each named
declaration is: module, file, line, read from the environment). -/
def asmPages (env : Environment) : IO (Json × Json) := do
  let j ← match Json.parse (← IO.FS.readFile asmPath) with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"{asmPath}: {e}")
  unless j.getObjValD "schema" == js asmSchema do
    throw (IO.userError s!"{asmPath}: schema is not {asmSchema}")
  -- the conformance rows of each record (`abiRows`; `abi` stays the record's metadata object)
  let mut fns : Array Json := #[]
  for f in ((j.getObjValD "functions").getArr?.toOption.getD #[]) do
    let d := ((f.getObjValD "decl").getStr?.toOption.getD "").toName
    let mut rows : Array Json := #[]
    let fileDecl := (f.getObjValD "file").getStr?.toOption.getD ""
    let fileEntry := ((j.getObjValD "files").getArr?.toOption.getD #[]).find? (fun x => (x.getObjValD "decl").getStr?.toOption == some fileDecl)
    let rfPath : String := (fileEntry.bind (fun x => (x.getObjValD "path").getStr?.toOption)).getD ""
    let rfSha : String := (fileEntry.bind (fun x => (x.getObjValD "sha256").getStr?.toOption)).getD ""
    let rf : RecordFile := ⟨fileDecl, rfPath, rfSha⟩
    let name := (f.getObjValD "name").getStr?.toOption.getD ""
    for l in abiLinks do
      if l.record == d then
        match ← abiLinkJson env l rf name with
        | .ok r => rows := rows.push r
        | .error m => throw (IO.userError s!"elf-pages abi link: {m}")
    fns := fns.push (if rows.isEmpty then f else f.setObjVal! "abiRows" (Json.arr rows))
  let j := j.setObjVal! "functions" (Json.arr fns)
  let mut decls : Array (String × Json) := #[]
  for s in asmDeclNames j do
    let d := s.toName
    let some ci := env.find? d | throw (IO.userError s!"{asmPath}: {s} is not in the environment ({asmModules})")
    let module := match env.getModuleIdxFor? d with
      | some i => env.header.moduleNames[i.toNat]!
      | none => .anonymous
    let line ← runCore env do return ((← Lean.findDeclarationRanges? d).map (·.range.pos.line))
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | _ => "declaration"
    decls := decls.push (s, Json.mkObj [("module", js module.toString),
      ("file", js (module.toString.replace "." "/" ++ ".lean")), ("kind", js kind),
      ("line", match line with | some l => jn l | none => Json.null)])
  pure (j, Json.mkObj [("schema", js "silmaril.elf-pages.asm-decls.v1"), ("source", js asmPath),
    ("decls", Json.mkObj decls.toList)])

/-! ## Driver -/

def loadEnv : IO Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  importModules (pinned.toArray.flatMap fun P => #[{ module := P.ns ++ `Thms }, { module := P.ns ++ `Functions }] ++
    (if P.slug == "zlib-checksums" then #[{ module := P.ns ++ `Contracts }] else #[]) ++
    cliModules.map ({ module := · }) ++ asmModules.map ({ module := · })) {}

def generateWithEnv : IO (Environment × List (String × Json) × List (String × ByteArray)) := do
  let e0 ← IO.monoMsNow
  let env ← loadEnv
  if (← IO.getEnv "ELF_PAGES_PROFILE").isSome then IO.eprintln s!"import: {(← IO.monoMsNow) - e0} ms"
  let mut files : List (String × Json) := []
  let mut blobs : List (String × ByteArray) := []
  let mut index : Array Json := #[]
  for P in pinned do
    let bytes ← IO.FS.readBinFile P.path
    -- coreutils' sha256sum when present (the list-based Lean reference takes about a minute on
    -- libc.so.6); otherwise the Lean digest
    let sha ← (do
        let o ← IO.Process.output { cmd := "sha256sum", args := #[P.path] }
        if o.exitCode == 0 then pure ((o.stdout.splitOn " ").head!) else pure (sha256Hex bytes))
      <|> pure (sha256Hex bytes)
    if sha != P.sha256 then throw (IO.userError s!"{P.path}: SHA-256 {sha}, pinned {P.sha256}")
    if bytes.size != P.size then throw (IO.userError s!"{P.path}: size {bytes.size}, pinned {P.size}")
    let t0 ← IO.monoMsNow
    let thms ← theorems env P
    let t1 ← IO.monoMsNow
    let src := fastRead bytes
    for t in thms do
      match t.claim, t.role with
      | .part ws reader _, some r =>
        if let .error e := recheck P src r ws reader then throw (IO.userError s!"{t.decl}: {e}")
      | .zeros o n, _ =>
        unless (List.range n).all (fun i => bytes.get! (o + i) == 0) do
          throw (IO.userError s!"{t.decl}: bytes not zero")
      | _, _ => pure ()
    let t2 ← IO.monoMsNow
    let dis ← disassemble P bytes
    let t3 ← IO.monoMsNow
    let pg := page P thms (dis.map (·.1))
    if (← IO.getEnv "ELF_PAGES_PROFILE").isSome then
      IO.eprintln s!"{P.slug}: theorems {t1 - t0} ms, recheck {t2 - t1} ms, disassembly {t3 - t2} ms, page {(← IO.monoMsNow) - t3} ms ({pg.compress.length} B)"
    files := files ++ [(s!"f/{P.slug}.json", pg)]
    if let some (d, cs) := dis then
      files := files ++ [(s!"dis/{P.slug}.json", d)] ++ (cs.mapIdx fun k c => (s!"dis/{P.slug}/{k}.json", c)).toList
    blobs := blobs ++ [(s!"blob/{P.slug}.bin", bytes)]
    index := index.push (Json.mkObj [("slug", js P.slug), ("title", js P.title), ("path", js P.path),
      ("size", jn P.size), ("sha256", js P.sha256), ("module", js P.ns.toString),
      ("type", (pg.getObjValD "header").getObjValD "type"), ("machine", (pg.getObjValD "header").getObjValD "machine"),
      ("sections", jn P.L.sections.length), ("segments", jn P.L.phdrs.length), ("theorems", jn thms.size),
      ("functions", jn ((pg.getObjValD "functions").getArr?.toOption.map (·.size) |>.getD 0)),
      ("kernelOnly", toJson (thms.all fun t => t.axioms.all (standardAxioms.contains ·))),
      ("coverageSummary", pg.getObjValD "coverageSummary")])
  let cli ← cliIndex env
  let (asm, asmDecls) ← asmPages env
  pure (env, ("index.json", Json.mkObj [("schema", js "silmaril.elf-pages.v1"), ("files", Json.arr index)]) ::
    ("cli.json", cli) :: ("asm.json", asm) :: ("asm-decls.json", asmDecls) :: files, blobs)

def generate : IO (List (String × Json) × List (String × ByteArray)) := do
  let (_, files, blobs) ← generateWithEnv
  pure (files, blobs)

/-- The edge of record `id` (an I/O or a specification record) for `decl`. -/
def edgeOf (id : String) (decl : Name) : Option Edge :=
  ((ioRecords.find? (·.id == id)).map (·.edges) <|> (specRecords.find? (·.id == id)).map (·.edges)).bind
    fun es => es.find? (·.decl == decl)

/-- **Association tampers**: a proving or refinement edge with its declaration swapped for a
true theorem about something else. Each must fail `checkAssociation`. -/
def associationTampers : List (String × String × Name × Name) := [
  ("hello-gcc row proved by sha256sum's LPS theorem", "hello-gcc", `Silmaril.Elf.CliExe.Hello.hello_cli,
    `Silmaril.Process.LPS.Problems.GnuSha256sum.Close.lpsTotal_close),
  ("hello-gcc row proved by an unrelated arithmetic fact", "hello-gcc", `Silmaril.Elf.CliExe.Hello.hello_cli, `Nat.add_comm),
  ("hello-gcc process theorem swapped for hello-clang's (other binary)", "hello-gcc", `Silmaril.Elf.Link.Dyn.Hello.hello_gcc,
    `Silmaril.Elf.Link.Dyn.Hello.hello_clang),
  ("hello-gcc execution consequence swapped for cat's refinement (other binary and spec)", "hello-gcc",
    `Silmaril.Elf.CliExe.hello_via_start, `Silmaril.Elf.Link.Dyn.Program.Examples.catStdinGcc_filter),
  ("sha256-cli proved by sha256sum-min's theorem (other binary)", "sha256-cli",
    `Silmaril.Process.LPS.Problems.Sha256Cli.sha256cli_lps_total, `Silmaril.Process.LPS.Problems.GnuSha256sum.Close.lpsTotal_close),
  ("cat refined by hello's proof (other spec)", "cat", `Silmaril.Elf.Link.Dyn.Program.Examples.catStdinGcc_filter,
    `Silmaril.Elf.CliExe.Hello.hello_cli),
  ("hello spec refined by cat's proof (other spec and binary)", "hello", `Silmaril.Elf.CliExe.Hello.hello_cli,
    `Silmaril.Elf.Link.Dyn.Program.Examples.catStdinGcc_filter),
  ("wasm-wac refinement swapped for wasm-jco's", "wasm-wac", `Silmaril.Cli.Spec.Wac.main_refines,
    `Silmaril.Cli.Spec.Jco.main_refines)]

def associationSelfTest (env : Environment) : IO Nat := do
  let mut failed := 0
  for (what, id, orig, swap) in associationTampers do
    let some e := edgeOf id orig | IO.eprintln s!"elf-pages --self-test: no edge {orig} in {id}"; failed := failed + 1; continue
    if e.about.isEmpty then
      IO.eprintln s!"elf-pages --self-test: {orig} in {id} has no anchors"; failed := failed + 1; continue
    match ← checkAssociation env e with
    | .error m => IO.eprintln s!"elf-pages --self-test: the original edge fails ({m})"; failed := failed + 1
    | .ok () =>
      if env.find? swap |>.isNone then
        IO.eprintln s!"elf-pages --self-test: {swap} is not in the environment"; failed := failed + 1
      else if (← checkAssociation env { e with decl := swap }) matches .ok () then
        IO.eprintln s!"elf-pages --self-test: the association check accepted '{what}'"; failed := failed + 1
  pure failed

def write (out : String) (files : List (String × Json)) (blobs : List (String × ByteArray)) : IO Unit := do
  let w0 ← IO.monoMsNow
  for (rel, j) in files do
    let p := System.FilePath.mk out / "elf" / rel
    if let some d := p.parent then IO.FS.createDirAll d
    let c0 ← IO.monoMsNow
    let txt := j.compress
    let c1 ← IO.monoMsNow
    IO.FS.writeFile p txt
    if (← IO.getEnv "ELF_PAGES_PROFILE").isSome && c1 - c0 > 500 then IO.eprintln s!"compress {rel}: {c1 - c0} ms"
  if (← IO.getEnv "ELF_PAGES_PROFILE").isSome then IO.eprintln s!"write: {(← IO.monoMsNow) - w0} ms"
  for (rel, b) in blobs do
    let p := System.FilePath.mk out / "elf" / rel
    if let some d := p.parent then IO.FS.createDirAll d
    IO.FS.writeBinFile p b

/-- The files under `out/elf` that differ from the generated ones. -/
def differences (out : String) (files : List (String × Json)) (blobs : List (String × ByteArray)) :
    IO (List String) := do
  let mut bad := []
  for (rel, j) in files do
    let p := System.FilePath.mk out / "elf" / rel
    let ok ← (do pure (match Json.parse (← IO.FS.readFile p) with | .ok g => g == j | .error _ => false)) <|> pure false
    unless ok do bad := bad ++ [p.toString]
  for (rel, b) in blobs do
    let p := System.FilePath.mk out / "elf" / rel
    let ok ← (do pure ((← IO.FS.readBinFile p) == b)) <|> pure false
    unless ok do bad := bad ++ [p.toString]
  pure bad

/-- Edits of the explorer data that `--verify` must reject: each moves a byte range, re-associates a
theorem with another part or function, widens a coverage class, hides axioms or links a contract to
another function, or changes or drops a piece of an assembly function's evidence. -/
def tampers : List (String × String × (Json → Json)) :=
  let modArr (f : Array Json → Array Json) (key : String) (j : Json) : Json :=
    match j.getObjValD key with
    | .arr a => j.setObjVal! key (.arr (f a))
    | _ => j
  let modFirst (pred : Json → Bool) (g : Json → Json) (a : Array Json) : Array Json :=
    match a.findIdx? pred with
    | some i => a.modify i g
    | none => a
  let part (k : String) (t : Json) := t.getObjValD "part" == Json.str k
  [("window moved", "f/gnu-sha256sum.json", modArr (modFirst (part "phdr/3") fun t =>
      t.setObjVal! "windows" (Json.arr #[Json.arr #[jn 288, jn 56]])) "theorems"),
   ("theorem re-associated", "f/gnu-sha256sum.json", modArr (modFirst (part "phdr/3") fun t =>
      t.setObjVal! "part" (js "phdr/4")) "theorems"),
   ("coverage widened", "f/gnu-sha256sum.json", modArr (modFirst
      (fun r => match r with | .arr x => x[2]? == some (js "raw") | _ => false)
      (fun r => match r with | .arr x => .arr (x.set! 2 (js "decoded")) | r => r)) "coverage"),
   ("axioms hidden", "f/glibc-libc.json", modArr (fun a => a.modify 0 fun t => t.setObjVal! "axioms" (Json.arr #[])) "theorems"),
   ("function row given another theorem", "f/zlib-libz.json", modArr (fun a => a.modify 1 fun r =>
      r.setObjVal! "theorem" ((a[2]?.map (·.getObjValD "theorem")).getD Json.null)) "functions"),
   ("open obligation shown as proved", "cli.json", modArr (fun a => a.modify 0 fun r =>
      match r.getObjValD "edges" with
      | .arr es => r.setObjVal! "edges" (.arr (es.map fun e =>
          if (e.getObjValD "role").getStr?.toOption.any (·.startsWith "open") then e.setObjVal! "status" (js "proved") else e))
      | _ => r) "io"),
   ("contract linked to another function", "f/zlib-checksums.json", modArr (modFirst
      (fun r => r.getObjValD "name" == Json.str "crc32_z") fun r =>
        r.setObjVal! "contracts" (Json.arr #[js "Silmaril.Elf.Staged.Pinned.ZlibChecksums.adler32_z_contract"])) "functions"),
   ("assembly evidence kind changed", "asm.json", modArr (fun a => a.modify 0 fun f =>
      f.setObjVal! "evidence" (.arr ((((f.getObjValD "evidence").getArr?.toOption).getD #[]).modify 0 fun e =>
        e.setObjVal! "kind" (js (if e.getObjValD "kind" == js "notArch" then "arch" else "notArch"))))) "functions"),
   ("assembly evidence dropped", "asm.json", modArr (fun a => a.modify 0 fun f =>
      f.setObjVal! "evidence" (.arr (((f.getObjValD "evidence").getArr?.toOption).getD #[]).pop)) "functions")]

def main (args : List String) : IO UInt32 := do
  match args with
  | [out] =>
    let (files, blobs) ← generate
    write out files blobs
    IO.println s!"elf-pages: wrote {files.length + blobs.length} files under {out}/elf"
    pure 0
  | ["--verify", out] =>
    let (files, blobs) ← generate
    let bad ← differences out files blobs
    for p in bad do IO.eprintln s!"elf-pages: {p} differs from the checked theorems"
    if bad.isEmpty then IO.println "elf-pages: verified"; pure 0 else pure 1
  | ["--self-test", out] =>
    -- one generation: write, verify, then each edit must be rejected
    let (env, files, blobs) ← generateWithEnv
    write out files blobs
    unless (← differences out files blobs).isEmpty do
      IO.eprintln "elf-pages --self-test: freshly written pages differ"; return 1
    let mut failed ← associationSelfTest env
    failed := failed + (← abiLinkSelfTest env)
    for (what, rel, edit) in tampers do
      let some (_, j) := files.find? (·.1 == rel) | IO.eprintln s!"no {rel}"; return 1
      let p := System.FilePath.mk out / "elf" / rel
      let j' := edit j
      if j' == j then IO.eprintln s!"elf-pages --self-test: edit '{what}' changed nothing"; failed := failed + 1
      IO.FS.writeFile p j'.compress
      if (← differences out files blobs).isEmpty then
        IO.eprintln s!"elf-pages --self-test: --verify accepted a tampered page ({what})"; failed := failed + 1
      IO.FS.writeFile p j.compress
    unless (← differences out files blobs).isEmpty do failed := failed + 1
    if failed == 0 then
      IO.println s!"elf-pages --self-test: ok ({tampers.length} edits rejected, {associationTampers.length} swapped proofs rejected)"; pure 0
    else pure 1
  | _ => IO.eprintln "usage: elf-pages OUTDIR | elf-pages --verify OUTDIR | elf-pages --self-test OUTDIR"; pure 2

end ElfPages

def main (args : List String) : IO UInt32 := ElfPages.main args
