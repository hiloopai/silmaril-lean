module

public import Silmaril.Elf.Abi.Asm.Defs
public import Silmaril.Elf.Asm.Example.Defs
public import Silmaril.Elf.Staged.Pinned.ZlibChecksums.Thms

/-! # The typed adapter on the pinned `zlib-checksums`: `crc32_z`

`crc32_z` (`Silmaril.Elf.Asm.Example.crc32_z`, 291 bytes at `0x401990`) as conformance code: its
bytes at its address, and the file's image (the four `PT_LOAD` ranges of its parse). -/

@[expose] public section

namespace Silmaril.Elf.Abi.AsmExample

open Silmaril.Elf.Staged.Pinned.ZlibChecksums (L bodies ld)

/-- The image of the pinned `zlib-checksums`: its `PT_LOAD` ranges as its parse gives them. -/
def image : List (Silmaril.X86.Word × Nat) :=
  (L.assemble bodies ld).loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize)

/-- `crc32_z`'s conformance code. -/
def crc32zCode : Silmaril.Machine.Abi.Conformance.Code :=
  Code.ofAsm Silmaril.Elf.Asm.Example.crc32_z image

end Silmaril.Elf.Abi.AsmExample

end
