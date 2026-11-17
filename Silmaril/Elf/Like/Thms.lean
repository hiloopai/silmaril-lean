module

public import Silmaril.Elf.Like.Defs
public import Silmaril.Elf.Facts.Defs

/-! # `ElfLike`: the instances agree with the existing `Blob` forms

Every instance denotes what the specification parse of the same bytes says, and these are the
`blobOf` forms the existing rows are stated on (the pinned files' `F := blobOf ⟨raw⟩`,
`Shapes.file X := blobOf X.bytes`). So a fact proved through any carrier is a fact about the same
file, with no conversion run inside a kernel check:

| carrier | bridge |
|---|---|
| `ByteArray` | `denotes_byteArray : Denotes a A ↔ Parses (blobOf ⟨a⟩) A` (definitional) |
| `KBytes` | `denotes_kbytes : x.toByteArray = raw → (Denotes x A ↔ Parses (blobOf ⟨raw⟩) A)`; the hypothesis is what `kbytes_def … of_include raw` proves |
| `Formats.Bytes`, `Value V` | `denotes_formatsBytes`, `denotes_value` (definitional) |
| CST | `cst_ast`: a CST checked against an image denotes what the image does |
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.X86.Link (Blob)
open Silmaril.Project (Value)

theorem toBlob_byteArray (a : ByteArray) : toBlob (ByteSource.bytes a) = blobOf ⟨a⟩ := rfl

theorem denotes_byteArray (a : ByteArray) (A : File) : Denotes a A ↔ Parses (blobOf ⟨a⟩) A :=
  Iff.rfl

/-- **Kernel bytes denote what the raw file parses to**, given the equation `kbytes_def … of_include`
proves without decoding a byte. -/
theorem denotes_kbytes {x : KBytes} {raw : ByteArray} (h : x.toByteArray = raw) (A : File) :
    Denotes x A ↔ Parses (blobOf ⟨raw⟩) A := by
  subst h; exact Iff.rfl

theorem denotes_formatsBytes (b : Silmaril.Formats.Bytes) (A : File) :
    Denotes b A ↔ Parses (blobOf b) A := Iff.rfl

theorem denotes_value {V : Type} (X : Value V) (A : File) :
    Denotes X A ↔ Parses (blobOf X.bytes) A := Iff.rfl

theorem denotes_file (A B : File) : Denotes A B ↔ A = B := Option.some_inj

/-- One carrier value denotes at most one AST. -/
theorem Denotes.unique {α : Type} [ElfLike α] {x : α} {A B : File} (hA : Denotes x A)
    (hB : Denotes x B) : A = B :=
  Option.some_inj.mp (hA.symm.trans hB)

/-- **A CST checked against an image denotes what the image does** (`File.isCST_sound_nil`). -/
theorem cst_ast {c : Silmaril.Formats.ELF.Cst.File} {img : Silmaril.BinaryImage}
    (h : c.IsCST img = true) : ElfLike.ast? c = ElfLike.ast? img := by
  show ofCst c = parse (Blob.ofBytes img.bits)
  rw [ofCst, Silmaril.Formats.ELF.Cst.File.isCST_sound_nil h]
  rfl

/-- `MachineIs` on a `Blob`, from any parse of it. -/
theorem machineIs_of_parses {F : Blob} {A : File} (h : Parses F A) :
    MachineIs F A.header.machine := ⟨A, h, rfl⟩

/-- The machine is a function of the file. -/
theorem MachineIs.unique {α : Type} [ElfLike α] {x : α} {m n : Nat} (hm : MachineIs x m)
    (hn : MachineIs x n) : m = n := by
  obtain ⟨A, hA, rfl⟩ := hm
  obtain ⟨B, hB, rfl⟩ := hn
  rw [Denotes.unique hA hB]

/-- `EntriesAre` gives `IsEntry` for each listed entry. -/
theorem EntriesAre.isEntry {α : Type} [ElfLike α] {x : α} {es : List EntryPoint}
    (h : EntriesAre x es) {e : EntryPoint} (he : e ∈ es) : IsEntry x e := by
  obtain ⟨A, hA, rfl⟩ := h
  exact ⟨A, hA, he⟩

/-- `KindIs` is `Denotes` and `File.kind` on a `Blob`. -/
theorem kindIs_iff (F : Blob) (k : Kind) : KindIs F k ↔ ∃ A, Denotes F A ∧ A.kind = k := Iff.rfl

end Silmaril.Elf
