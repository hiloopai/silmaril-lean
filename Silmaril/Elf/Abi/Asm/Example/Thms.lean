module

public import Silmaril.Elf.Abi.Asm.Example.Defs
import Silmaril.Proofs.Elf.Abi.Asm.Example

/-! # The typed adapter on `crc32_z`: theorem

PROVED (standard axioms): `crc32z_codeOf`: #851's evidence for the sample function `crc32_z`
(`BytesAt`, `SymbolOf`) and the `.symtab` lookup give the conformance row's code binding
`CodeOf F .symtab "crc32_z" crc32zCode`. Its conformance (on `Open`, where its contract is
proved total, not in first-return form) is not claimed here. -/

@[expose] public section

namespace Silmaril.Elf.Abi.AsmExample

open Silmaril.Elf.Abi

theorem crc32z_codeOf :
    CodeOf Silmaril.Elf.Staged.Pinned.ZlibChecksums.F .symtab "crc32_z" crc32zCode :=
  Silmaril.Proofs.Elf.Abi.AsmExample.crc32z_codeOf

end Silmaril.Elf.Abi.AsmExample

end
