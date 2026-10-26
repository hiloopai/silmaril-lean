module

public import Silmaril.Formats.ELF.Cst.Types
public import Silmaril.Formats.ELF.Ast

/-! Shared-CST proof and bounded-reader correspondence layer. Data-only clients
import `Cst.Types`; neither construction nor erasure certifies name annotations. -/
@[expose] public section
namespace Silmaril.Formats.ELF.Cst

@[simp] theorem Section.erase_data (part : Section) :
    part.erase.data = part.body.bytes := rfl


theorem File.lossless_of_toList {file : File} {original : Bytes}
    (equal : file.bytes.map Array.toList = some original.toList) : file.Lossless original := by
  cases result : file.bytes with
  | none => simp [result] at equal
  | some bytes =>
    have listEqual : bytes.toList = original.toList := by simpa [result] using equal
    have byteEqual : bytes = original := Array.toList_inj.mp listEqual
    simp [File.Lossless, result, byteEqual]

@[simp] theorem File.erase_header (file : File) : file.erase.header = file.header := rfl

/-- A physical section payload and semantic section data share one definition. -/
theorem File.resolvePart_sectionPayload {file : File} {index : Nat} {part : Section}
    (found : file.sections[index]? = some part) :
    file.resolvePart (.sectionPayload index) =
      some (.raw (.sectionPayload index) part.erase.data) := by
  simp [File.resolvePart, found, Section.erase]

theorem File.bytes_of_layout {file : File} {layout : Ast.File}
    (resolved : file.layout = some layout) : file.bytes = some layout.bytes := by
  simp [File.bytes, resolved]


def File.Interprets (file : File) : Prop :=
  ∃ layout, file.layout = some layout ∧ layout.Interprets file.erase

/-- An existing parser certificate can be reused after byte identity is proved.
The generator's structural erasure alone never supplies this certificate. -/
theorem File.interprets_of_lossless {file : File} {layout : Ast.File} {original : Bytes}
    (resolved : file.layout = some layout) (lossless : layout.Lossless original)
    (parsed : readObject original = some file.erase) : file.Interprets :=
  ⟨layout, resolved, Ast.File.interprets_of_lossless lossless parsed⟩

/-- Use the shared byte projection directly when a separate layout name is
unnecessary. This still requires a parser certificate for the erased object. -/
theorem File.interprets_of_bytes {file : File} {original : Bytes}
    (lossless : file.Lossless original) (parsed : readObject original = some file.erase) :
    file.Interprets := by
  unfold File.Lossless File.bytes at lossless
  cases resolved : file.layout with
  | none => simp [resolved] at lossless
  | some layout =>
    have byteEqual : layout.bytes = original := by simpa [resolved] using lossless
    exact File.interprets_of_lossless resolved byteEqual parsed

theorem File.bytes_parsed {file : File} (interprets : file.Interprets) :
    ∃ bytes, file.bytes = some bytes ∧ readObject bytes = some file.erase := by
  rcases interprets with ⟨layout, resolved, parsed⟩
  exact ⟨layout.bytes, File.bytes_of_layout resolved, parsed⟩


end Silmaril.Formats.ELF.Cst
