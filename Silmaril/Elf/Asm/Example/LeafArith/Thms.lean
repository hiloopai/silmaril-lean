module

public import Silmaril.Elf.Asm.Example.LeafArith.Defs
public import Silmaril.Elf.Asm.Thms
public import Silmaril.Elf.Load.Thms
public import Silmaril.Elf.Image.Thms
public import Silmaril.Elf.Facts.Thms

/-! # `clamp_i32` and `sat_add_u32`, dimension by dimension, on the pinned file

Every theorem is closed by `decide +kernel` on the parse `ast` or on the `Blob` literal; none
imports an ABI module.

| evidence | `clamp_i32` | `sat_add_u32` |
|---|---|---|
| parse | `parses` | (same) |
| `ArchOf`, `BytesAt`, `CodeAt`, `SymbolOf` | `clamp_arch`, `clamp_bytes`, `clamp_code`, `clamp_symbol` | `sat_…` |
| `DecodesAs x86Open`, `LinesTile`, boundaries agree | `clamp_decodes`, `clamp_tiles`, `clamp_boundaries` | `sat_…` |
| `Unrelocated` | `clamp_unrelocated` | `sat_unrelocated` |
| presence | `clamp_present` (`PresentFn`) | `sat_present` |

File-level adapters on the same file: `rt_write_absent` (`AbsentName`: declared in `rt.h`, not
linked), `rodata_fail` (`ReadOnlyAt`: `"FAIL"` at `0x402000`), `image` (`LoadRangesAre`: four
`PT_LOAD`s, the last one `.bss`, zero fill), `bss_zeroFill`. And the memory bridge:
`clamp_loaded`: **in any memory holding the image at base 0, `clamp_i32`'s 19 bytes are fetchable
at `0x4013a0`** (`Load.readWith_of_segBytes`, with `ImageLoaded` and the execute permission as
hypotheses: nothing here runs a loader).
-/

@[expose] public section

namespace Silmaril.Elf.Asm.Example.LeafArith

open Silmaril.Elf.Image Silmaril.Elf.Load

theorem parses : Parses F ast := (Option.some_get _).symm

/-- The read-only executable `PT_LOAD` (`.text`). -/
def text : Silmaril.Formats.ELF.ProgramHeader := ⟨1, 5, 4096, 0x401000, 0x401000, 2038, 2038, 4096⟩

/-- The read-only `PT_LOAD` of `.rodata`. -/
def rodata : Silmaril.Formats.ELF.ProgramHeader := ⟨1, 4, 8192, 0x402000, 0x402000, 204, 204, 4096⟩

/-! ## `clamp_i32` -/

theorem clamp_arch : ArchOf F clamp := archOf_of_check parses (by decide +kernel)
theorem clamp_bytes : BytesAt F clamp :=
  bytesAt_of_check parses (by decide +kernel) fun o ho => by cases ho; unfold FileBytes; decide +kernel
theorem clamp_code : CodeAt F clamp.extent.vaddr clamp.bytes :=
  ⟨ast, parses, text, by decide +kernel, by decide +kernel⟩
theorem clamp_symbol : SymbolOf F clamp := symbolOf_of_check parses (by decide +kernel)
theorem clamp_decodes : DecodesAs x86Open clamp clampDecoding :=
  decodesAs_of_decodeAll rfl (by decide +kernel)
theorem clamp_tiles : LinesTile clamp := by decide +kernel
theorem clamp_boundaries : clamp.lines.map (·.len) = clampDecoding.map (·.1) := by decide +kernel
theorem clamp_unrelocated : Unrelocated F clamp := ⟨ast, parses, by decide +kernel⟩
theorem clamp_present : PresentFn F (nameOf "clamp_i32") := ⟨ast, parses, by decide +kernel⟩

/-! ## `sat_add_u32` -/

theorem sat_arch : ArchOf F sat := archOf_of_check parses (by decide +kernel)
theorem sat_bytes : BytesAt F sat :=
  bytesAt_of_check parses (by decide +kernel) fun o ho => by cases ho; unfold FileBytes; decide +kernel
theorem sat_code : CodeAt F sat.extent.vaddr sat.bytes :=
  ⟨ast, parses, text, by decide +kernel, by decide +kernel⟩
theorem sat_symbol : SymbolOf F sat := symbolOf_of_check parses (by decide +kernel)
theorem sat_decodes : DecodesAs x86Open sat satDecoding :=
  decodesAs_of_decodeAll rfl (by decide +kernel)
theorem sat_tiles : LinesTile sat := by decide +kernel
theorem sat_unrelocated : Unrelocated F sat := ⟨ast, parses, by decide +kernel⟩
theorem sat_present : PresentFn F (nameOf "sat_add_u32") := ⟨ast, parses, by decide +kernel⟩

/-! ## File-level adapters -/

/-- `rt_write` (declared in `rt.h`) is not in the file, in any table or version. -/
theorem rt_write_absent : AbsentName F (nameOf "rt_write") := ⟨ast, parses, by decide +kernel⟩

/-- The read-only string `"FAIL"` at `0x402000` (`.rodata`, the third `PT_LOAD`). -/
theorem rodata_fail : ReadOnlyAt F 0x402000 [0x46, 0x41, 0x49, 0x4c] :=
  ⟨ast, parses, rodata, by decide +kernel, by decide +kernel⟩

theorem image : LoadRangesAre F [(0x400000, 344), (0x401000, 2038), (0x402000, 204), (0x4030cc, 4)] :=
  ⟨ast, parses, by decide +kernel⟩

/-- Every byte of every load range has exactly one origin: no overlapping segments, so
`ReadOnlyAt` and `ImageLoaded` are not first-match conventions here. -/
theorem image_unambiguous : ∀ r ∈ ast.loadRanges, Unambiguous ast r.1 r.2 := by decide +kernel

/-- The fourth `PT_LOAD` (`p_offset = 204`, `p_filesz = 0`) is zero fill. -/
theorem bss_zeroFill : ast.resolve 0x4030cc = .unique 3 .zeroFill := by decide +kernel

/-- **The memory bridge**: wherever the image is loaded at base 0 and the execute permission
holds, `clamp_i32`'s bytes are fetchable at its address. -/
theorem clamp_loaded {mem : Silmaril.Process.Memory} (hL : ImageLoaded F ast 0 mem)
    (hp : mem.Permitted .execute (0 + 0x4013a0) clamp.bytes.length) :
    mem.readWith .execute (0 + 0x4013a0) clamp.bytes.length = some clamp.bytes := by
  obtain ⟨-, A, i, o, hA, hi, ho, hs⟩ := clamp_bytes
  rw [parses_unique hA parses] at hs
  exact readWith_of_segBytes hL hs (by decide +kernel) hp

end Silmaril.Elf.Asm.Example.LeafArith
