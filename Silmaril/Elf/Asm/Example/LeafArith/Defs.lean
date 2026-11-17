module

public import Silmaril.Elf.Asm.Example.LeafArith.Listing
public import Silmaril.Elf.Asm.X86
public import Silmaril.Elf.Load.Defs
public import Silmaril.X86.Ladder.Pinned.LeafArith
public import Silmaril.X86.Ladder.LeafArith.Defs

/-! # Sample assembly functions: `clamp_i32` and `sat_add_u32` of the pinned `leaf-arith`

`examples/elf-ladder/01-leaf-arith/pinned/leaf-arith` (static `ET_EXEC`, gcc 13.3 `-O2`, 9632
bytes, SHA-256 `d9cf1e5d…2484`) is the `Blob` literal `Silmaril.X86.Ladder.Pinned.LeafArith.exe`
(generated and checked against the file by `examples/elf-ladder/pin.sh`). Its parse `ast` is one
kernel run of the specification on that literal. The two functions' bytes are the slices of the
existing transcription `Silmaril.X86.Ladder.LeafArith.code` (`[0x401370, 0x401425)`); their
listings are `objdump -d` output (`Listing`).

| function | vaddr | bytes | file offset | segment | `.symtab` entry |
|---|---|---|---|---|---|
| `clamp_i32` | `0x4013a0` | 19 | `0x13a0` | 1 | 19 |
| `sat_add_u32` | `0x401400` | 29 | `0x1400` | 1 | 10 |

This module and its theorems import no ABI module: the ABI rows about the same functions are a
separate statement (`silmaril.shapes.elf.abi_conforms`), which can refer to these values. -/

@[expose] public section

namespace Silmaril.Elf.Asm.Example.LeafArith

/-- The pinned file. -/
abbrev F : Silmaril.X86.Link.Blob := Silmaril.X86.Ladder.Pinned.LeafArith.exe

/-- Its parse (a kernel run of the specification). -/
def ast : File := (parse F).get (by decide +kernel)

/-- `int clamp_i32(int x, int lo, int hi)`. -/
def clamp : AsmFunction where
  name := "clamp_i32"
  arch := .x86_64
  abiRef := some "x86_64-sysv-psabi"
  abiSource := some "System V Application Binary Interface, AMD64 Architecture Processor Supplement"
  extent := { vaddr := 0x4013a0, size := 19, fileOff := some 0x13a0, segment := some 1, shndx := some 1 }
  symbol := some ⟨.symtab, 19⟩
  bytes := (Silmaril.X86.Ladder.LeafArith.code.drop 0x30).take 19
  lines := clampLines
  listingTool := some "GNU objdump (GNU Binutils for Debian) 2.44"

/-- `u32 sat_add_u32(u32 a, u32 b)`. -/
def sat : AsmFunction where
  name := "sat_add_u32"
  arch := .x86_64
  abiRef := some "x86_64-sysv-psabi"
  abiSource := some "System V Application Binary Interface, AMD64 Architecture Processor Supplement"
  extent := { vaddr := 0x401400, size := 29, fileOff := some 0x1400, segment := some 1, shndx := some 1 }
  symbol := some ⟨.symtab, 10⟩
  bytes := (Silmaril.X86.Ladder.LeafArith.code.drop 0x90).take 29
  lines := satLines
  listingTool := some "GNU objdump (GNU Binutils for Debian) 2.44"

/-- The decodings by `x86Open` (the machine of the existing rung-01 contracts). -/
def clampDecoding : List (Nat × x86Open.Instr) := (decodeAll x86Open clamp.bytes).getD []
def satDecoding : List (Nat × x86Open.Instr) := (decodeAll x86Open sat.bytes).getD []

end Silmaril.Elf.Asm.Example.LeafArith
