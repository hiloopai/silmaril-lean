module

public import Silmaril.Elf.Facts.Defs
public import Silmaril.Machine.Region.X86.CFG.Defs

/-! # ELF-byte provenance for intrinsic CFG rows

The ELF reader fixes the read-only executable PT_LOAD mapping from virtual
address to file offset. This relation binds the actual file bytes to a direct
CFG syntax certificate. It makes no loading or execution claim.
-/

@[expose] public section
namespace Silmaril.Elf.Region.CFG
open Silmaril.Machine.Region.X86.CFG

def Valid (file : Silmaril.X86.Link.Blob) (row : Row) : Prop :=
  CodeAt file row.code.base row.code.bytes ∧ row.Valid

structure Certified (file : Silmaril.X86.Link.Blob) where
  row : Row
  valid : Valid file row

end Silmaril.Elf.Region.CFG
