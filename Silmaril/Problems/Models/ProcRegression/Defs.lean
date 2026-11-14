module

public import Silmaril.Problems.Models.Proc.Defs
public import Silmaril.X86.EntryState

/-!
# Regression launches for the static loader of `musl-str9` (erebor-lean #70)

A small static `ET_EXEC` image and four launches of it, all with the same segments,
stack pointer, argument string and registers:

* `ordinary`: the auxiliary vector Linux builds, `AT_PHDR = 0x400040`, `AT_PHENT = 56`,
  `AT_PHNUM = 2`, `AT_PAGESZ = 4096`;
* `substitutedAddress`: `AT_PHDR = 0x400000040` (the address substituted in the #70
  reproduction), everything else ordinary;
* `substitutedCount`: `AT_PHNUM = 1`, everything else ordinary;
* `extraExec`: the ordinary stack, plus an executable mapping at `0x400000000` that is
  not an image segment (where the #70 reproduction placed its code).

The image (`image`) has two segments. The first is the start of the file: a 64-byte
ELF header (`ehdr`) and two program headers (`phdr`), one per segment. The second is
`mov eax, 60; xor edi, edi; syscall` at the entry point.
-/

@[expose] public section

namespace Silmaril.Problems.Models.ProcRegression

open Silmaril.Process
open Silmaril.Process.CLI
open Silmaril.X86 (Word State)
open Silmaril.X86.EntryState (Placement)

/-- `width` little-endian bytes of `n`. -/
def le (n width : Nat) : List Byte := (List.range width).map fun i => BitVec.ofNat 8 (n / 256 ^ i)

/-- The ELF header: x86-64 `ET_EXEC`, entry `0x401000`, two 56-byte program headers at
file offset 64. -/
def ehdr : List Byte :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0] ++ le 0 8 ++ le 2 2 ++ le 62 2 ++ le 1 4 ++
    le 0x401000 8 ++ le 64 8 ++ le 0 8 ++ le 0 4 ++ le 64 2 ++ le 56 2 ++ le 2 2 ++
    le 64 2 ++ le 0 2 ++ le 0 2

/-- A program header with equal file and memory sizes and 4 KiB alignment. -/
def phdr (type flags offset vaddr size : Nat) : List Byte :=
  le type 4 ++ le flags 4 ++ le offset 8 ++ le vaddr 8 ++ le vaddr 8 ++ le size 8 ++
    le size 8 ++ le 0x1000 8

/-- The first 176 bytes of the file: the ELF header and the table. -/
def fileHead : List Byte :=
  ehdr ++ phdr 1 4 0 0x400000 176 ++ phdr 1 5 0x1000 0x401000 9

/-- `mov eax, 60; xor edi, edi; syscall`. -/
def code : List Byte := [0xb8, 0x3c, 0, 0, 0, 0x31, 0xff, 0x0f, 0x05]

def seg0 : Segment := ⟨0x400000, 176, ⟨true, false, false⟩, fileHead⟩
def seg1 : Segment := ⟨0x401000, 9, ⟨true, false, true⟩, code⟩

def image : Image := ⟨0x401000, [seg0, seg1]⟩

/-- The image's program-header table. -/
def table : HeaderTable := ⟨0x400000, fileHead, 64, 2⟩

def input (stdin : List Byte) : ProcInput := ⟨[[97]], [], .ofList stdin⟩

def sp : Nat := 0x810000
def argAddress : Nat := 0x810200

def ordinary : List (Word × Word) := [(3, 0x400040), (4, 56), (5, 2), (6, 4096)]
def substitutedAddress : List (Word × Word) := [(3, 0x400000040), (4, 56), (5, 2), (6, 4096)]
def substitutedCount : List (Word × Word) := [(3, 0x400040), (4, 56), (5, 1), (6, 4096)]

/-- The vectors at `sp`: `argc = 1`, `argv[0]`, the two NULLs and `auxv`. -/
def vectorBytes (auxv : List (Word × Word)) : List Byte :=
  Silmaril.Machine.LittleEndian.encodeWords
    (X86Linux.vectorWords [BitVec.ofNat 64 argAddress] [] auxv)

def readWrite : Permissions := ⟨true, true, false⟩

/-- An executable mapping that is not an image segment: `jmp $` at `0x400000000`. -/
def extraCode : Placement := ⟨⟨0x400000000, 2, ⟨true, false, true⟩⟩, some [0xeb, 0xfe]⟩

def pSeg0 : Placement := ⟨seg0.region, some seg0.contents⟩
def pSeg1 : Placement := ⟨seg1.region, some seg1.contents⟩
/-- The writable room below `sp` (unbacked). -/
def pRoom : Placement := ⟨⟨sp - X86Linux.stackRoom, X86Linux.stackRoom, readWrite⟩, none⟩
def pVectors (auxv : List (Word × Word)) : Placement :=
  ⟨⟨sp, (vectorBytes auxv).length, readWrite⟩, some (vectorBytes auxv)⟩
/-- `argv[0] = "a"`. -/
def pArg : Placement := ⟨⟨argAddress, 2, readWrite⟩, some [97, 0]⟩

/-- The mappings: the two segments, the stack room, the vectors, `argv[0]`, then `extra`. -/
def placements (auxv : List (Word × Word)) (extra : List Placement) : List Placement :=
  [pSeg0, pSeg1, pRoom, pVectors auxv, pArg] ++ extra

abbrev launchMemory (auxv : List (Word × Word)) (extra : List Placement) : Memory :=
  Silmaril.X86.EntryState.memory (placements auxv extra)

/-- RIP at the entry, RSP at `sp`, every other register zero. -/
def core : State :=
  (Silmaril.X86.EntryState.blankCore (BitVec.ofNat 64 image.entry)).write .rsp (BitVec.ofNat 64 sp)

end Silmaril.Problems.Models.ProcRegression
