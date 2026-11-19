module

public import Silmaril.Elf.Asm.Example.Defs
public import Silmaril.Elf.Asm.Thms
public import Silmaril.Elf.Image.Thms
public import Silmaril.Elf.Facts.Thms
public import Silmaril.Elf.Staged.Pinned.ZlibChecksums.Contracts

/-! # The sample functions, dimension by dimension, on the pinned file's bytes

`F` is the pinned file (`include_bytes`), `A` its parse (`ZlibChecksums.parses`, assembled from
kernel-checked parts). For each function, each dimension is its own theorem, closed by
`decide +kernel` on the parse or on the file's kernel bytes:

| function | `ArchOf` | `BytesAt` | `CodeAt` | `SymbolOf` | `LinesTile` | decoded by | not decoded by | refs | contract (existing) |
|---|---|---|---|---|---|---|---|---|---|
| `crc32` | ✓ | ✓ | ✓ | ✓ | ✓ | `x86Open`, `x86Ext` | | `jmp crc32_z` | `Open` |
| `crc32_z` | ✓ | ✓ | ✓ | ✓ | ✓ | `x86Open` | `x86Ext` | | `Open` |
| `adler32` | ✓ | ✓ | ✓ | ✓ | ✓ | `x86Open9` | | `jmp adler32_z` | `Open9` |
| `adler32_z` | ✓ | ✓ | ✓ | ✓ | ✓ | `x86Open9` | `x86Open` | | `Open9` |

The rows show the dimensions are independent: `crc32_z`'s contract is proved on the `Open`
machine, and the base decoder `x86Ext` does not decode it; `adler32_z`'s is proved on `Open9`, and
`x86Open` does not decode it. `otherMachine` (bytes grounded, architecture `0x1234`) has no
decoding by any x86 model and no `ArchOf`.

The address theorems (`textResolves`, `bssZeroFill`, …) separate file offsets, virtual
addresses and zero fill on the same file: its fourth `PT_LOAD` has `p_offset = 0` and
`p_filesz = 0`, so its addresses are zero fill and **not** file offset 0, which the first
`PT_LOAD` maps to `0x400000`.
-/

@[expose] public section

namespace Silmaril.Elf.Asm.Example

open Silmaril.Elf.Image
open Silmaril.Elf.Staged.Pinned.ZlibChecksums (F K parses L bodies ld)
open Silmaril.X86.Ladder.ZlibChecksums

/-- The parse of the pinned file. -/
abbrev A : File := L.assemble bodies ld

/-! ## `crc32` -/

theorem crc32_arch : ArchOf F crc32 := archOf_of_check parses (by decide +kernel)

theorem crc32_bytes : BytesAt F crc32 :=
  bytesAt_of_kbytes K.wf_true K.toByteArray_eq parses rfl (by decide +kernel) (by decide +kernel)

theorem crc32_code : CodeAt F crc32.extent.vaddr crc32.bytes := Staged.Pinned.ZlibChecksums.crc32_contract.1

theorem crc32_symbol : SymbolOf F crc32 := symbolOf_of_check parses (by decide +kernel)

theorem crc32_tiles : LinesTile crc32 := by decide +kernel

theorem crc32_decodes : DecodesAs x86Open crc32 crc32Decoding :=
  decodesAs_of_decodeAll rfl (by decide +kernel)

/-- The base decoder decodes the wrapper too, into the same two instructions' lengths. -/
theorem crc32_decodes_ext : ((decodeAll x86Ext crc32.bytes).map fun d => d.map (·.1)) = some [2, 5] := by
  decide +kernel

/-- `jmp crc32_z`: the decoded branch at offset 2 targets `0x401990`, `crc32_z`'s address. -/
theorem crc32_refs : RefsGrounded F crc32 x86Open crc32Decoding := by
  intro r hr _
  simp only [crc32, List.mem_singleton] at hr; subst hr
  exact refGrounded_of_check rfl crc32_decodes (by decide +kernel)

/-- The existing contract, beside the grounded bytes. -/
theorem crc32_contract : BytesAt F crc32 ∧ ∀ entry, (crc32Contract entry).Total Silmaril.X86.Open.isa :=
  ⟨crc32_bytes, crc32_total⟩

/-- The reference of `crc32` targets segment 1 (the read-only `.text`): segment association
from the target address alone. -/
theorem crc32_ref_target : ∀ r ∈ crc32.refs, RefTargetIn F r 1 ∧ RefTargetReadOnly F r := by
  intro r hr
  simp only [crc32, List.mem_singleton] at hr; subst hr
  exact ⟨⟨A, 0x401990, .file 0x1990, parses, rfl, by decide +kernel⟩,
    ⟨A, 0x401990, parses, rfl, by decide +kernel, by decide +kernel⟩⟩

/-! ## `crc32_z` -/

theorem crc32_z_arch : ArchOf F crc32_z := archOf_of_check parses (by decide +kernel)

theorem crc32_z_bytes : BytesAt F crc32_z :=
  bytesAt_of_kbytes K.wf_true K.toByteArray_eq parses rfl (by decide +kernel) (by decide +kernel)

theorem crc32_z_code : CodeAt F crc32_z.extent.vaddr crc32_z.bytes :=
  Staged.Pinned.ZlibChecksums.crc32_z_contract.1

theorem crc32_z_symbol : SymbolOf F crc32_z := symbolOf_of_check parses (by decide +kernel)

theorem crc32_z_tiles : LinesTile crc32_z := by decide +kernel

theorem crc32_z_decodes : DecodesAs x86Open crc32_z crc32zDecoding :=
  decodesAs_of_decodeAll rfl (by decide +kernel)

/-- **The base decoder does not decode `crc32_z`** (it stops on an `Ext8` form). -/
theorem crc32_z_not_ext (d : List (Nat × x86Ext.Instr)) : ¬ DecodesAs x86Ext crc32_z d :=
  not_decodesAs_of_decodeAll (by decide +kernel) d

/-- Its listing and its decoding agree on instruction boundaries. -/
theorem crc32_z_boundaries : crc32_z.lines.map (·.len) = crc32zDecoding.map (·.1) := by
  decide +kernel

theorem crc32_z_contract : BytesAt F crc32_z ∧ ∀ entry, (crc32zContract entry).Total Silmaril.X86.Open.isa :=
  ⟨crc32_z_bytes, crc32z_total⟩

/-! ## `adler32` -/

theorem adler32_arch : ArchOf F adler32 := archOf_of_check parses (by decide +kernel)

theorem adler32_bytes : BytesAt F adler32 :=
  bytesAt_of_kbytes K.wf_true K.toByteArray_eq parses rfl (by decide +kernel) (by decide +kernel)

theorem adler32_code : CodeAt F adler32.extent.vaddr adler32.bytes :=
  Staged.Pinned.ZlibChecksums.adler32_contract.1

theorem adler32_symbol : SymbolOf F adler32 := symbolOf_of_check parses (by decide +kernel)

theorem adler32_tiles : LinesTile adler32 := by decide +kernel

theorem adler32_decodes : DecodesAs x86Open9 adler32 adler32Decoding :=
  decodesAs_of_decodeAll rfl (by decide +kernel)

theorem adler32_refs : RefsGrounded F adler32 x86Open9 adler32Decoding := by
  intro r hr _
  simp only [adler32, List.mem_singleton] at hr; subst hr
  exact refGrounded_of_check rfl adler32_decodes (by decide +kernel)

theorem adler32_contract :
    BytesAt F adler32 ∧ ∀ entry, (adler32Contract entry).Total Silmaril.X86.Open9.isa :=
  ⟨adler32_bytes, adler32_total⟩

/-! ## `adler32_z` -/

theorem adler32_z_arch : ArchOf F adler32_z := archOf_of_check parses (by decide +kernel)

theorem adler32_z_bytes : BytesAt F adler32_z :=
  bytesAt_of_kbytes K.wf_true K.toByteArray_eq parses rfl (by decide +kernel) (by decide +kernel)

theorem adler32_z_code : CodeAt F adler32_z.extent.vaddr adler32_z.bytes :=
  Staged.Pinned.ZlibChecksums.adler32_z_contract.1

theorem adler32_z_symbol : SymbolOf F adler32_z := symbolOf_of_check parses (by decide +kernel)

theorem adler32_z_tiles : LinesTile adler32_z := by decide +kernel

theorem adler32_z_decodes : DecodesAs x86Open9 adler32_z adler32zDecoding :=
  decodesAs_of_decodeAll rfl (by decide +kernel)

/-- **`x86Open` does not decode `adler32_z`**, whose contract is proved on `Open9`. -/
theorem adler32_z_not_open (d : List (Nat × x86Open.Instr)) : ¬ DecodesAs x86Open adler32_z d :=
  not_decodesAs_of_decodeAll (by decide +kernel) d

theorem adler32_z_contract :
    BytesAt F adler32_z ∧ ∀ entry, (adler32zContract entry).Total Silmaril.X86.Open9.isa :=
  ⟨adler32_z_bytes, adler32z_total⟩

/-! ## An unmodelled machine -/

/-- The bytes are grounded whatever the claimed architecture (`BytesAt` does not read it)... -/
theorem otherMachine_bytes : BytesAt F otherMachine := crc32_bytes

/-- ...but the file is not for that machine... -/
theorem otherMachine_not_arch : ¬ ArchOf F otherMachine := by
  rintro ⟨A', hA, hm, -⟩
  cases parses_unique hA parses
  exact absurd hm (by decide +kernel)

/-- ...and no x86 model decodes a function claimed for another machine. -/
theorem otherMachine_not_decoded (d : List (Nat × x86Open.Instr)) : ¬ DecodesAs x86Open otherMachine d :=
  fun h => absurd h.1 (by decide)

/-! ## Addresses on the same file -/

/-- `crc32`'s first byte resolves uniquely, to file offset `0x1ac0` in segment 1. -/
theorem textResolves : A.resolve 0x401ac0 = .unique 1 (.file 0x1ac0) := by decide +kernel

/-- The fourth `PT_LOAD` (`p_offset = 0`, `p_filesz = 0`, `p_memsz = 20032`) is zero fill: its
first address has no file byte, although its `p_offset` is `0`. -/
theorem bssZeroFill : A.resolve 0x403000 = .unique 3 .zeroFill := by decide +kernel

/-- File offset `0` is mapped by the first `PT_LOAD`, at `0x400000`. -/
theorem offsetZero : A.layout.vaddrOf 0 = some 0x400000 := by decide +kernel

/-- Past the last segment: unmapped. -/
theorem unmapped : A.resolve 0x500000 = .unmapped := by decide +kernel

/-- No dynamic relocation touches `crc32_z` (a static executable has none). -/
theorem crc32_z_untouched : Untouched A 0x401990 291 := by decide +kernel

end Silmaril.Elf.Asm.Example
