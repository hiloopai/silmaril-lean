import Silmaril.Elf.Asm.Example.Thms
import Silmaril.Elf.Asm.Example.Reloc.Thms
import Silmaril.Elf.Asm.Example.LeafArith.Thms

/-! # Decoys for `elf-asm --self-test`

True theorems that must **not** become evidence for a sample function, and one that must
become conditional evidence. `elf-asm` classifies these with the same code as the real theorems
and fails unless each gives exactly the expected result. -/

open Silmaril.Elf Silmaril.Elf.Asm Silmaril.Elf.Asm.Example

namespace ElfAsmDecoys

/-- `crc32` moved by one byte: not a sample constant. -/
def crc32Moved : AsmFunction := { crc32 with extent := { crc32.extent with vaddr := 0x401ac1 } }

/-- A true fact about a copy of a sample: no evidence for `crc32`. -/
theorem moved_tiles : LinesTile crc32Moved := by decide

/-- A name that looks like evidence, a statement that says nothing: no evidence. -/
theorem crc32_bytes : True := trivial

/-- Evidence about a sample against another file (the relocatable object): no evidence, since
`crc32` belongs to the zlib-checksums file. -/
theorem crc32_other_file (h : BytesAt Reloc.F crc32) : BytesAt Reloc.F crc32 := h

/-- A premise is reported: conditional `bytes` evidence for `crc32_z` with one hypothesis. -/
theorem crc32_z_bytes_if (h : BytesAt Staged.Pinned.ZlibChecksums.F crc32_z) :
    BytesAt Staged.Pinned.ZlibChecksums.F crc32_z := h

/-- A contract stated without the function's bytes or code: attached to no function. -/
theorem contract_alone : ∀ entry, (Silmaril.X86.Ladder.ZlibChecksums.crc32Contract entry).Total
    Silmaril.X86.Open.isa := Silmaril.X86.Ladder.ZlibChecksums.crc32_total

/-- A decoding of the same bytes under another function: no `decode` evidence for `crc32`. -/
theorem other_decodes : DecodesAs x86Open { crc32 with name := "other" } crc32Decoding :=
  crc32_decodes

/-- Presence of a sample's name in another file: no `present` evidence. -/
theorem present_other_file (h : Silmaril.Elf.Load.PresentFn Reloc.F (nameOf "clamp_i32")) :
    Silmaril.Elf.Load.PresentFn Reloc.F (nameOf "clamp_i32") := h

/-- Presence of another name in the sample's file: no `present` evidence for `clamp_i32`. -/
theorem present_other_name :
    Silmaril.Elf.Load.PresentFn LeafArith.F (nameOf "popcount32") :=
  ⟨LeafArith.ast, LeafArith.parses, by decide +kernel⟩

end ElfAsmDecoys
