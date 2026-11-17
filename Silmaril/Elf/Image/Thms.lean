module

public import Silmaril.Elf.Image.Defs
import Silmaril.Proofs.Elf.Image

/-! # Address relations: what each first-match convention means

* `mem_origins`: `File.origins` lists exactly the program headers that map `v`, with their origin;
  `origins_index_unique`: one segment gives one origin (a byte of a segment is file-backed or zero
  fill, never both).
* `mapsFile_origins`: a file-backed range is file-backed byte by byte, at consecutive offsets.
* `offsetOf_origin`, `vaddrOf_origin`: the staged layout's first-match lookups
  (`Staged.Layout.offsetOf`, `vaddrOf`) give **one of** the origins; `offsetOf_of_unique`: when
  the address resolves uniquely, `offsetOf` gives **the** origin. With overlapping segments a
  first match is a convention, not a fact about the image.
* `codeAt_segBytes`, `codeAt_of_segBytes`: `CodeAt` (the API's code fact, which takes the first
  read-only executable `PT_LOAD` mapping the range) is `SegBytes` in that segment.

Proofs: `Silmaril.Proofs.Elf.Image` (standard axioms only).
-/

@[expose] public section

namespace Silmaril.Elf.Image

open Silmaril.X86.Link (Blob)

theorem mem_origins {A : File} {v i : Nat} {o : Origin} :
    (i, o) ∈ A.origins v ↔ ∃ ph, A.phdrs[i]? = some ph ∧ segOrigin ph v = some o :=
  Proofs.Elf.Image.mem_origins

theorem origins_index_unique {A : File} {v i : Nat} {o₁ o₂ : Origin}
    (h₁ : (i, o₁) ∈ A.origins v) (h₂ : (i, o₂) ∈ A.origins v) : o₁ = o₂ :=
  Proofs.Elf.Image.origins_index_unique h₁ h₂

/-- A zero-filled byte of a segment is not a file byte of that segment. -/
theorem zeroFill_not_file {A : File} {v i o : Nat} (h : (i, Origin.zeroFill) ∈ A.origins v) :
    (i, Origin.file o) ∉ A.origins v :=
  fun h' => Origin.noConfusion (origins_index_unique h h')

theorem mapsFile_origins {A : File} {i v len o : Nat} (h : MapsFile A i v len o) {k : Nat}
    (hk : k < len) : (i, Origin.file (o + k)) ∈ A.origins (v + k) :=
  Proofs.Elf.Image.mapsFile_origins h hk

theorem offsetOf_origin {A : File} {v o : Nat} (h : A.layout.offsetOf v = some o) :
    ∃ i, (i, Origin.file o) ∈ A.origins v :=
  Proofs.Elf.Image.offsetOf_origin h

theorem offsetOf_of_unique {A : File} {v i o : Nat} (h : A.origins v = [(i, Origin.file o)]) :
    A.layout.offsetOf v = some o :=
  Proofs.Elf.Image.offsetOf_of_unique h

theorem resolve_unique {A : File} {v i o : Nat} (h : A.resolve v = .unique i (.file o)) :
    A.layout.offsetOf v = some o :=
  Proofs.Elf.Image.resolve_unique h

theorem vaddrOf_origin {A : File} {o v : Nat} (h : A.layout.vaddrOf o = some v) :
    ∃ i, (i, Origin.file o) ∈ A.origins v :=
  Proofs.Elf.Image.vaddrOf_origin h

/-- **`CodeAt` is `SegBytes` in a read-only executable segment.** -/
theorem codeAt_segBytes {F : Blob} {v : Nat} {code : List (BitVec 8)} (h : CodeAt F v code) :
    ∃ A, Parses F A ∧ ∃ i ph, A.phdrs[i]? = some ph ∧ codeSeg v code.length ph = true ∧
      SegBytes F A i v (ph.offset + (v - ph.virtualAddress)) code :=
  Proofs.Elf.Image.codeAt_segBytes h

theorem codeAt_of_segBytes {F : Blob} {A : File} (hA : Parses F A) {i v o : Nat}
    {code : List (BitVec 8)} (h : SegBytes F A i v o code)
    (hf : A.phdrs.find? (codeSeg v code.length) = A.phdrs[i]?) : CodeAt F v code :=
  Proofs.Elf.Image.codeAt_of_segBytes hA h hf

end Silmaril.Elf.Image
