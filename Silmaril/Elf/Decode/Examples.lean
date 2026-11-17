module

public import Silmaril.Elf.Decode.Thms
public import Silmaril.Elf.Like.Thms
public import Silmaril.Elf.Example.Thms

/-! # Decoding examples: each answer, kernel-checked

On the 210-byte PIE `Silmaril.Elf.Example.tinyPie` and on small byte strings, by `decode +kernel`:

| example | answer |
|---|---|
| `tinyPie` whole | `ok` (`tinyPie_ok`), and the parse it agrees with (`tinyPie_parses`) |
| its first 64 bytes | `incomplete` (the header is there, the program headers are not) |
| the file cut at 100 bytes | `invalid (truncated …)`: a whole source that ends early |
| 8 bytes `\x7fELF` `ELFCLASS32` | `unsupported elf32` |
| 8 bytes `\x7fELF` `ELFCLASS64` big-endian | `unsupported bigEndian` |
| 8 bytes with a bad magic | `invalid notElf` |
| 8 bytes `ELFCLASS64` little-endian, nothing else | `invalid (truncated …)` (a supported ELF, cut) |
| `relObj` with `e_machine = 0x1234` | `ok`, and `MachineIs` records `0x1234` (`oddMachine_machine`) |
-/

@[expose] public section

namespace Silmaril.Elf.Decode.Examples

open Silmaril.Elf.Example (tinyPie relObj)
open Silmaril.X86.Link (Blob)

theorem tinyPie_ok : (decode (whole tinyPie)).isOk = true := by decide +kernel

/-- The `ok` answer is the parse (`decode_whole_ok_iff`). -/
theorem tinyPie_parses : ∃ A, decode (whole tinyPie) = .ok A ∧ Parses tinyPie A ∧ A.kind = .pie := by
  obtain ⟨A, hA, hk⟩ := Silmaril.Elf.Example.tinyPie_kindIs
  exact ⟨A, (decode_whole_ok_iff _ _).mpr hA, hA, hk⟩

/-- A 64-byte download prefix is incomplete, not invalid. -/
theorem tinyPie_prefix : (decode (prefixOf tinyPie 64)).isIncomplete = true := by decide +kernel

/-- The file cut at 100 bytes is invalid: it is a whole source that ends early. -/
theorem tinyPie_cut : decode (whole ⟨tinyPie.n % 2 ^ (8 * 100), 100⟩) = .invalid (.truncated 96 8) := by
  decide +kernel

theorem elf32 : decode (whole (toBlob [0x7f, 0x45, 0x4c, 0x46, 1, 1, 1, 0])) = .unsupported .elf32 := by
  decide +kernel

theorem bigEndian :
    decode (whole (toBlob [0x7f, 0x45, 0x4c, 0x46, 2, 2, 1, 0])) = .unsupported .bigEndian := by
  decide +kernel

theorem notElf : decode (whole (toBlob [0x7f, 0x45, 0x4c, 0x47, 2, 1, 1, 0])) = .invalid .notElf := by
  decide +kernel

/-- A supported identification cut after eight bytes is a truncated supported file, not an
unsupported one. -/
theorem elf64_cut :
    decode (whole (toBlob [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0])) = .invalid (.truncated 8 1) := by
  decide +kernel

/-- An `ELFCLASS32` file known only through a prefix of its first eight bytes is already
`unsupported`, and stays so on the whole file (`decode_refines`). -/
theorem elf32_prefix :
    decode (prefixOf (toBlob [0x7f, 0x45, 0x4c, 0x46, 1, 1, 1, 0, 0, 0, 0, 0]) 8) = .unsupported .elf32 := by
  decide +kernel

/-- `relObj` with `e_machine = 0x1234`, a machine nothing here models. -/
def oddMachine : Blob :=
  ⟨relObj.n - ((relObj.n >>> 144) % 65536) * 2 ^ 144 + 0x1234 * 2 ^ 144, 64⟩

theorem oddMachine_ok : (parse oddMachine).map (·.header.machine) = some 0x1234 := by
  decide +kernel

/-- **An unknown machine is recorded, not rejected**: `decode` answers `ok`, and `MachineIs`. -/
theorem oddMachine_machine :
    (∃ A, decode (whole oddMachine) = .ok A) ∧ MachineIs oddMachine 0x1234 := by
  obtain ⟨A, hA⟩ : ∃ A, parse oddMachine = some A := ⟨_, (Option.some_get (by decide +kernel)).symm⟩
  have h := oddMachine_ok
  rw [hA] at h
  exact ⟨⟨A, (decode_whole_ok_iff _ _).mpr hA⟩, A, hA, Option.some_inj.mp h⟩

end Silmaril.Elf.Decode.Examples
