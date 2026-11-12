module

public import Silmaril.Elf.Link.Dyn.Loader.Defs
public import Silmaril.Elf.Link.Dyn.Pin.Bytes
public import Silmaril.Elf.Link.Dyn.Pin.Defs

/-! # Hello world, dynamically linked against glibc: the pinned executables

`examples/dyn/hello/hello.c` (`printf("hello, world\n"); return 0;`, which both compilers lower
to `puts("hello, world")`), built by `examples/dyn/hello/build.sh`:

* `hello-gcc`: Ubuntu gcc 13.3.0-6ubuntu2~24.04.1 `-O2`, binutils 2.42-4ubuntu2.10, glibc
  2.39-0ubuntu8.9 crt files: PIE, `DT_NEEDED libc.so.6`, `DF_BIND_NOW`, CET `.plt.sec`;
* `hello-clang`: Ubuntu clang 18.1.3 (1ubuntu1) `-O2`, same linker and crt files: PIE,
  **lazy binding** (no `DF_BIND_NOW`), classic `.plt` with `PLT0`.

GENERATED (the literals) by a generator (untrusted). The `File` blobs are trusted
only to be those files (`examples/dyn/pins.txt`); every other value is checked against
them in `Hello.Thms` by `decide +kernel`. Licence: the executables contain glibc's crt
startup code (LGPL-2.1-or-later with the linking exception) and GCC's crtstuff (GPL-3.0 with
the GCC runtime library exception).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86.Link (Blob)

/-- `hello-gcc` (15960 bytes, sha256 `6964f3f23e27cfd2b6c26bd469cb210ff000dd359fc9988138cadc96683065c7`). -/
def gccFile : Blob := blob_of% Silmaril.Elf.Link.Dyn.PinBytes.helloGcc

def gccInfo : Elf.DynInfo := ⟨[⟨6, 4, 0x40, 0x40, 0x2d8, 0x2d8⟩, ⟨3, 4, 0x318, 0x318, 0x1c, 0x1c⟩, ⟨1, 4, 0x0, 0x0, 0x628, 0x628⟩, ⟨1, 5, 0x1000, 0x1000, 0x179, 0x179⟩, ⟨1, 4, 0x2000, 0x2000, 0xec, 0xec⟩, ⟨1, 6, 0x2db8, 0x3db8, 0x258, 0x260⟩, ⟨2, 6, 0x2dc8, 0x3dc8, 0x1f0, 0x1f0⟩, ⟨4, 4, 0x338, 0x338, 0x30, 0x30⟩, ⟨4, 4, 0x368, 0x368, 0x44, 0x44⟩, ⟨1685382483, 4, 0x338, 0x338, 0x30, 0x30⟩, ⟨1685382480, 4, 0x2014, 0x2014, 0x34, 0x34⟩, ⟨1685382481, 6, 0x0, 0x0, 0x0, 0x0⟩, ⟨1685382482, 4, 0x2db8, 0x3db8, 0x248, 0x248⟩],
  [(0x1, 0x27), (0xc, 0x1000), (0xd, 0x116c), (0x19, 0x3db8), (0x1b, 0x8), (0x1a, 0x3dc0), (0x1c, 0x8), (0x6ffffef5, 0x3b0), (0x5, 0x480), (0x6, 0x3d8), (0xa, 0x8d), (0xb, 0x18), (0x15, 0x0), (0x3, 0x3fb8), (0x2, 0x18), (0x14, 0x7), (0x17, 0x610), (0x7, 0x550), (0x8, 0xc0), (0x9, 0x18), (0x1e, 0x8), (0x6ffffffb, 0x8000001), (0x6ffffffe, 0x520), (0x6fffffff, 0x1), (0x6ffffff0, 0x50e), (0x6ffffff9, 0x3)]⟩

def gccRela : List Elf.Rela := [⟨0x3db8, 8, 0, 4448⟩, ⟨0x3dc0, 8, 0, 4384⟩, ⟨0x4008, 8, 0, 16392⟩, ⟨0x3fd8, 6, 1, 0⟩, ⟨0x3fe0, 6, 2, 0⟩, ⟨0x3fe8, 6, 4, 0⟩, ⟨0x3ff0, 6, 5, 0⟩, ⟨0x3ff8, 6, 6, 0⟩]

def gccJmpRel : List Elf.Rela := [⟨0x3fd0, 7, 3, 0⟩]

/-- The references of the symbol relocations, by symbol index. -/
def gccRefs : List (Nat × Elf.Ref) := [
  (1, ⟨nm "__libc_start_main", false, some ⟨nm "GLIBC_2.34", 0x69691b4, false⟩⟩),
  (2, ⟨nm "_ITM_deregisterTMCloneTable", true, none⟩),
  (4, ⟨nm "__gmon_start__", true, none⟩),
  (5, ⟨nm "_ITM_registerTMCloneTable", true, none⟩),
  (6, ⟨nm "__cxa_finalize", true, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (3, ⟨nm "puts", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩)]

/-- `hello-clang` (16008 bytes, sha256 `ecad1a19e6e63e4828e9386a9c831dc6beb635c6858dc42d2c248e6397eaa713`). -/
def clangFile : Blob := blob_of% Silmaril.Elf.Link.Dyn.PinBytes.helloClang

def clangInfo : Elf.DynInfo := ⟨[⟨6, 4, 0x40, 0x40, 0x2d8, 0x2d8⟩, ⟨3, 4, 0x318, 0x318, 0x1c, 0x1c⟩, ⟨1, 4, 0x0, 0x0, 0x618, 0x618⟩, ⟨1, 5, 0x1000, 0x1000, 0x161, 0x161⟩, ⟨1, 4, 0x2000, 0x2000, 0xcc, 0xcc⟩, ⟨1, 6, 0x2dd0, 0x3dd0, 0x248, 0x250⟩, ⟨2, 6, 0x2de0, 0x3de0, 0x1e0, 0x1e0⟩, ⟨4, 4, 0x338, 0x338, 0x20, 0x20⟩, ⟨4, 4, 0x358, 0x358, 0x44, 0x44⟩, ⟨1685382483, 4, 0x338, 0x338, 0x20, 0x20⟩, ⟨1685382480, 4, 0x2014, 0x2014, 0x2c, 0x2c⟩, ⟨1685382481, 6, 0x0, 0x0, 0x0, 0x0⟩, ⟨1685382482, 4, 0x2dd0, 0x3dd0, 0x230, 0x230⟩],
  [(0x1, 0x27), (0xc, 0x1000), (0xd, 0x1154), (0x19, 0x3dd0), (0x1b, 0x8), (0x1a, 0x3dd8), (0x1c, 0x8), (0x6ffffef5, 0x3a0), (0x5, 0x470), (0x6, 0x3c8), (0xa, 0x8d), (0xb, 0x18), (0x15, 0x0), (0x3, 0x3fe8), (0x2, 0x18), (0x14, 0x7), (0x17, 0x600), (0x7, 0x540), (0x8, 0xc0), (0x9, 0x18), (0x6ffffffb, 0x8000000), (0x6ffffffe, 0x510), (0x6fffffff, 0x1), (0x6ffffff0, 0x4fe), (0x6ffffff9, 0x3)]⟩

def clangRela : List Elf.Rela := [⟨0x3dd0, 8, 0, 4400⟩, ⟨0x3dd8, 8, 0, 4336⟩, ⟨0x4010, 8, 0, 16400⟩, ⟨0x3fc0, 6, 1, 0⟩, ⟨0x3fc8, 6, 2, 0⟩, ⟨0x3fd0, 6, 4, 0⟩, ⟨0x3fd8, 6, 5, 0⟩, ⟨0x3fe0, 6, 6, 0⟩]

def clangJmpRel : List Elf.Rela := [⟨0x4000, 7, 3, 0⟩]

/-- The references of the symbol relocations, by symbol index. -/
def clangRefs : List (Nat × Elf.Ref) := [
  (1, ⟨nm "__libc_start_main", false, some ⟨nm "GLIBC_2.34", 0x69691b4, false⟩⟩),
  (2, ⟨nm "_ITM_deregisterTMCloneTable", true, none⟩),
  (4, ⟨nm "__gmon_start__", true, none⟩),
  (5, ⟨nm "_ITM_registerTMCloneTable", true, none⟩),
  (6, ⟨nm "__cxa_finalize", true, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩),
  (3, ⟨nm "puts", false, some ⟨nm "GLIBC_2.2.5", 0x9691a75, false⟩⟩)]

end Silmaril.Elf.Link.Dyn.Hello
