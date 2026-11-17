module

public import Silmaril.Elf.Like.Thms
public import Silmaril.Elf.Example.Thms
public import Silmaril.Elf.Staged.Pinned.ZlibChecksums.Thms

/-! # `ElfLike` examples: one file through several carriers

The pinned zlib-checksums executable (`Silmaril.Elf.Staged.Pinned.ZlibChecksums`) is the `Blob`
`F = blobOf ⟨raw⟩` of its `include_bytes` and also the kernel bytes `K` of the same file. Its parse
`parses` (assembled from kernel-checked parts) is a fact about either carrier, by `denotes_kbytes`
and no further kernel run:

* `kbytes_machine`: through the kernel bytes, the file is for `EM_X86_64`;
* `entries`: its only entry point is `e_entry = 0x401000` (a static `ET_EXEC` with no `.dynsym`);
* `tinyPie_entries`: the synthetic PIE has none (`e_entry = 0`, no exports).
-/

@[expose] public section

namespace Silmaril.Elf.Like.Examples

open Silmaril.Elf.Staged.Pinned.ZlibChecksums (F K parses L bodies ld)

/-- The kernel bytes of the pinned file denote its parse. -/
theorem kbytes_denotes : Denotes K (L.assemble bodies ld) :=
  (denotes_kbytes K.toByteArray_eq _).mpr parses

theorem kbytes_machine : MachineIs K EM_X86_64 := ⟨_, kbytes_denotes, rfl⟩

theorem machine : MachineIs F EM_X86_64 := machineIs_of_parses parses

theorem entries : EntriesAre F [⟨.start, 0x401000⟩] := ⟨_, parses, by decide +kernel⟩

theorem start_isEntry : IsEntry F ⟨.start, 0x401000⟩ := entries.isEntry (List.mem_singleton_self _)

theorem tinyPie_entries : EntriesAre Example.tinyPie [] := by
  obtain ⟨A, hA⟩ : ∃ A, parse Example.tinyPie = some A := ⟨_, (Option.some_get (by decide +kernel)).symm⟩
  have h : (parse Example.tinyPie).map File.entries = some [] := by decide +kernel
  rw [hA] at h; exact ⟨A, hA, Option.some_inj.mp h⟩

end Silmaril.Elf.Like.Examples
