module

public import Silmaril.Elf.Asm.Example.Listing
public import Silmaril.Elf.Asm.X86
public import Silmaril.X86.Ladder.ZlibChecksums.Defs

/-! # Sample assembly functions: four functions of the pinned zlib-checksums executable

The static x86-64 executable `examples/elf-ladder/03-zlib-checksums/pinned/zlib-checksums`
(zlib 1.3.1 `adler32.c` and `crc32.c`, `-DZ_SOLO -O2`, GCC 13.3; pinned in
`Silmaril.Elf.Staged.Pinned.ZlibChecksums`) as four `AsmFunction`s, with the code literals of
`Silmaril.X86.Ladder.ZlibChecksums` (whose contracts are proved there) as their bytes and the
`objdump` listings of `Listing` as their display lines. Every field is a claim; `Thms` proves
the ones that hold, dimension by dimension, and shows which instruction models decode which
function.

| function | vaddr | bytes | file offset | segment | `.symtab` entry |
|---|---|---|---|---|---|
| `adler32_z` | `0x401410` | 1135 | `0x1410` | 1 | 25 |
| `adler32` | `0x401880` | 7 | `0x1880` | 1 | 13 |
| `crc32_z` | `0x401990` | 291 | `0x1990` | 1 | 14 |
| `crc32` | `0x401ac0` | 7 | `0x1ac0` | 1 | 15 |

`otherMachine` is a function claimed for an `e_machine` (`0x1234`) no model decodes.
-/

@[expose] public section

namespace Silmaril.Elf.Asm.Example

open Silmaril.X86.Ladder.ZlibChecksums (crc32zCode crc32WrapCode adler32zCode adler32WrapCode)

/-- `crc32`: `mov %edx,%edx; jmp crc32_z`. -/
def crc32 : AsmFunction where
  name := "crc32"
  arch := .x86_64
  abiRef := some "sysv64"
  extent := { vaddr := 0x401ac0, size := 7, fileOff := some 0x1ac0, segment := some 1, shndx := some 1 }
  symbol := some ⟨.symtab, 15⟩
  bytes := crc32WrapCode
  lines := crc32Lines
  refs := [{ off := 2, target := some 0x401990, symbol := some "crc32_z", origin := .decoded }]

/-- `crc32_z`. -/
def crc32_z : AsmFunction where
  name := "crc32_z"
  arch := .x86_64
  abiRef := some "sysv64"
  extent := { vaddr := 0x401990, size := 291, fileOff := some 0x1990, segment := some 1, shndx := some 1 }
  symbol := some ⟨.symtab, 14⟩
  bytes := crc32zCode
  lines := crc32zLines

/-- `adler32`: `mov %edx,%edx; jmp adler32_z`. -/
def adler32 : AsmFunction where
  name := "adler32"
  arch := .x86_64
  abiRef := some "sysv64"
  extent := { vaddr := 0x401880, size := 7, fileOff := some 0x1880, segment := some 1, shndx := some 1 }
  symbol := some ⟨.symtab, 13⟩
  bytes := adler32WrapCode
  lines := adler32Lines
  refs := [{ off := 2, target := some 0x401410, symbol := some "adler32_z", origin := .decoded }]

/-- `adler32_z`. -/
def adler32_z : AsmFunction where
  name := "adler32_z"
  arch := .x86_64
  abiRef := some "sysv64"
  extent := { vaddr := 0x401410, size := 1135, fileOff := some 0x1410, segment := some 1, shndx := some 1 }
  symbol := some ⟨.symtab, 25⟩
  bytes := adler32zCode
  lines := adler32zLines

/-- The four functions. -/
def all : List AsmFunction := [adler32_z, adler32, crc32_z, crc32]

/-- The decodings, by the model each function's contract is proved on. -/
def crc32Decoding : List (Nat × x86Open.Instr) := (decodeAll x86Open crc32.bytes).getD []
def crc32zDecoding : List (Nat × x86Open.Instr) := (decodeAll x86Open crc32_z.bytes).getD []
def adler32Decoding : List (Nat × x86Open9.Instr) := (decodeAll x86Open9 adler32.bytes).getD []
def adler32zDecoding : List (Nat × x86Open9.Instr) := (decodeAll x86Open9 adler32_z.bytes).getD []

/-- A function claimed for `e_machine = 0x1234`: its bytes are `crc32`'s, its architecture is not. -/
def otherMachine : AsmFunction := { crc32 with arch := { machine := 0x1234 }, refs := [] }

end Silmaril.Elf.Asm.Example
