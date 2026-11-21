module

public import Silmaril.Elf.Staged.Pinned.ZlibChecksums.Thms
public import Silmaril.X86.Ladder.ZlibChecksums.Thms

/-! # zlib-checksums: the proved functions, on the pinned file

`Silmaril.X86.Ladder.ZlibChecksums` proves System V function contracts (`FnContract.Spec.Total`)
of four functions of zlib 1.3.1 for their code (`crc32zCode`, `adler32zCode` and the two 7-byte
wrappers) loaded at any entry. Its link to the file, `Silmaril.X86.Ladder.Pinned.zlib_crc32z` and
the others, reads a `Blob` literal trusted to be the file. Here each code literal is tied to the
**pinned file itself** (`include_bytes` of `examples/elf-ladder/03-zlib-checksums/pinned/
zlib-checksums`), at the address its symbol names: `Silmaril.Elf.CodeAt F v code` (the parse of
`F`, the read-only executable `PT_LOAD` mapping `v`, and the bytes there), from one kernel read on
kernel bytes. Each theorem pairs that with the existing contract, unchanged, and states the
**code identity** between them: the contract's entry precondition requires exactly the code
constant that `CodeAt` places in the file (`Loaded m.memory e code`, by projection), and for the
two wrappers, the callee's code `0x130`/`0x470` bytes below the entry, which is where the file
places it (`0x401ac0 - 0x130 = 0x401990`, `0x401880 - 0x470 = 0x401410`). The contracts are System V
first-return contracts (`FnContract.Spec.Total` on `Open`/`Open9`, from an ABI entry); they claim
nothing beyond their pre- and postconditions (other registers, global state, other callers).

The contracts are about code at any entry: their hypotheses ask that the code be loaded there
(and, for `crc32_z`, that `crc_table` sit at `0x4021e0`, as linked). Nothing here proves how a
loader places the file. The other functions of the file have no contract in this repository.
-/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.ZlibChecksums

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader
open Silmaril.X86.Ladder.ZlibChecksums

/-- **`crc32_z`** (`0x401990`, 291 bytes): the file holds `crc32zCode` there, and its contract
holds on `Open`. -/
theorem crc32_z_contract : CodeAt F 0x401990 crc32zCode ∧
    (∀ e m, (crc32zContract e).entry m → Silmaril.X86.Ext.Loaded m.memory e crc32zCode) ∧
    ∀ entry, (crc32zContract entry).Total Silmaril.X86.Open.isa :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide) (by decide +kernel),
    fun _ _ h => h.2.1, crc32z_total⟩

/-- **`crc32`** (`0x401ac0`, 7 bytes, a tail call into `crc32_z`): the file holds the wrapper and
`crc32zCode` `0x130` bytes below it, and its contract holds on `Open`. -/
theorem crc32_contract : CodeAt F 0x401ac0 crc32WrapCode ∧ CodeAt F 0x401990 crc32zCode ∧
    (∀ e m, (crc32Contract e).entry m → Silmaril.X86.Ext.Loaded m.memory e crc32WrapCode ∧
      Silmaril.X86.Ext.Loaded m.memory (e - 0x130#64) crc32zCode) ∧ 0x401ac0 - 0x130 = 0x401990 ∧
    ∀ entry, (crc32Contract entry).Total Silmaril.X86.Open.isa :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide) (by decide +kernel),
    crc32_z_contract.1, fun _ _ h => ⟨h.2.1, h.2.2.1⟩, rfl, crc32_total⟩

/-- **`adler32_z`** (`0x401410`, 1135 bytes): the file holds `adler32zCode` there, and its
contract holds on `Open9`. -/
theorem adler32_z_contract : CodeAt F 0x401410 adler32zCode ∧
    (∀ e m, (adler32zContract e).entry m → Silmaril.X86.Ext.Loaded m.memory e adler32zCode) ∧
    ∀ entry, (adler32zContract entry).Total Silmaril.X86.Open9.isa :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide) (by decide +kernel),
    fun _ _ h => h.2.1, adler32z_total⟩

/-- **`adler32`** (`0x401880`, 7 bytes, a tail call into `adler32_z`): the file holds the wrapper
and `adler32zCode` `0x470` bytes below it, and its contract holds on `Open9`. -/
theorem adler32_contract : CodeAt F 0x401880 adler32WrapCode ∧ CodeAt F 0x401410 adler32zCode ∧
    (∀ e m, (adler32Contract e).entry m → Silmaril.X86.Ext.Loaded m.memory e adler32WrapCode ∧
      Silmaril.X86.Ext.Loaded m.memory (e - 0x470#64) adler32zCode) ∧ 0x401880 - 0x470 = 0x401410 ∧
    ∀ entry, (adler32Contract entry).Total Silmaril.X86.Open9.isa :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide) (by decide +kernel),
    adler32_z_contract.1, fun _ _ h => ⟨h.2.1, h.2.2.1⟩, rfl, adler32_total⟩

end Silmaril.Elf.Staged.Pinned.ZlibChecksums
