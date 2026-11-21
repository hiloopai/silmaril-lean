module

public import Silmaril.Elf.Region.CFG.Defs

/-! # Small direct CFGs from the pinned GCC hello executable

The two windows are within its executable PT_LOAD, using base-relative ELF VAs.
Theorems in `Regions.Thms` bind them to the included file. No load bias, incoming
entry restriction, whole-function partition or reachability is inferred here.
-/

@[expose] public section
namespace Silmaril.Elf.Staged.Pinned.HelloGcc.Regions
open Silmaril.X86.Decompile
open Silmaril.Machine.Region.X86.CFG

def compareCode : List Silmaril.X86.Byte := [0x48, 0x39, 0xf8, 0x74, 0x15]
def tailCode : List Silmaril.X86.Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x77, 0xff, 0xff, 0xff]

def compareRow : Row where
  code := ⟨0x10be, compareCode⟩
  fuel := 2
  listing := [⟨0x10be, .alu .q .cmp (.reg .rax) .rdi, 3⟩, ⟨0x10c1, .jcc8 .e 0x15, 2⟩]
  entry := 0x10be
  edges := [(0x10be, 0x10c1), (0x10c1, 0x10d8), (0x10c1, 0x10c3)]
  exits := [0x10d8, 0x10c3]

def tailRow : Row where
  code := ⟨0x1160, tailCode⟩
  fuel := 2
  listing := [⟨0x1160, .endbr64, 4⟩, ⟨0x1164, .jmp 0xffffff77, 5⟩]
  entry := 0x1160
  edges := [(0x1160, 0x1164), (0x1164, 0x10e0)]
  exits := [0x10e0]

/-- Identical data supplied as a stated row, without a certificate attached to
this declaration. Equality of data is visible separately from proof provenance. -/
def statedCompare : Row := compareRow

/-- Stated incomplete alternative for comparison; it deliberately omits the
conditional fallthrough. It has no byte/CFG certificate. -/
def missingFallthrough : Row :=
  { compareRow with edges := [(0x10be, 0x10c1), (0x10c1, 0x10d8)], exits := [0x10d8] }

end Silmaril.Elf.Staged.Pinned.HelloGcc.Regions
