module
public import Silmaril.Project.Defs
public import Silmaril.Formats.ELF.Object
public import Silmaril.Process.LPS.ELFImage

/-!
# Formats `elf.elf64le` and `elf.exec-x86`

Two views of ELF64 little-endian bytes, both thin adapters over silmaril-lean readers:

* `elf.elf64le`: a relocatable object (`ET_REL`) to `Silmaril.Formats.ELF.ObjectFile` (header,
  sections, symbols, relocations), by `Silmaril.Formats.ELF.readObject`.
* `elf.exec-x86`: a fixed-address x86-64 executable (`ET_EXEC`, no interpreter) to the
  checked load records `Silmaril.Process.LPS.ELFImage.Records` (header, program headers,
  the load segment holding the program-header table), by `ELFImage.parse x86Policy`.

Gaps: neither has a printer. `elf.elf64le` has no soundness theorem against an independent ELF
grammar, so no law; `elf.exec-x86` has `sound` for `ELFImage.Parsed` (its layout rules,
not a theorem about Linux's loader). Executables are not `elf.elf64le` values (`readObject` accepts
only `ET_REL`), and shared objects (`ET_DYN`, e.g. `libz.so`) are accepted by neither.
-/

@[expose] public section
namespace Silmaril.Project.Formats

/-- Bytes as the bit-vector array of silmaril's ELF readers. -/
def elfBytes (bytes : Silmaril.Formats.Bytes) : Silmaril.Formats.ELF.Bytes :=
  bytes.toList.toArray.map (fun byte => BitVec.ofNat 8 byte.toNat)

/-- An ELF64 little-endian relocatable object to its sections, symbols and relocations. -/
def elf : Format blob Silmaril.Formats.ELF.ObjectFile where
  parse := fun b => Silmaril.Formats.ELF.readObject (elfBytes b)

/-- An x86-64 `ET_EXEC` executable to its checked load records. -/
def elfExecX86 : Format blob Silmaril.Process.LPS.ELFImage.Records where
  parse b := Silmaril.Process.LPS.ELFImage.parse Silmaril.Process.LPS.ELFImage.x86Policy
    (elfBytes b)

/-- The specification relation of `elf.exec-x86`: the header and program headers are what
the readers return, and they satisfy every layout rule of `ELFImage.RecordsValid`. -/
def ElfExecX86Rel (b : Silmaril.Formats.Bytes) (r : Silmaril.Process.LPS.ELFImage.Records) : Prop :=
  Silmaril.Process.LPS.ELFImage.Parsed Silmaril.Process.LPS.ELFImage.x86Policy
    (elfBytes b) r

end Silmaril.Project.Formats

silmaril format elf.elf64le := Silmaril.Project.Formats.elf
  (doc := "ELF64 little-endian relocatable object (ET_REL) to sections, symbols, relocations (Silmaril.Formats.ELF.readObject)")
silmaril format "elf.exec-x86" := Silmaril.Project.Formats.elfExecX86
  (doc := "x86-64 ET_EXEC executable to checked load records (Silmaril.Process.LPS.ELFImage.parse x86Policy)")
silmaril format_default elf := elf.elf64le
