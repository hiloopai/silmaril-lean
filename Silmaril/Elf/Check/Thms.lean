module

public import Silmaril.Proofs.Elf.Check.Sound
public import Silmaril.Proofs.Elf.Check.Frame
public import Silmaril.Elf.Link.Dyn.Pages.Thms

/-! # The fast parse checker is sound

* `Check.file_sound`: `Sub r F → Check.file r A = true → Parses F A`;
* `Check.sub_pages`: the page reader of a file's pages answers as the file, so
  `Check.parses_of_pages` turns a kernel run of the checker on 4 KiB pages into `Parses F A`
  without the whole-file number ever being evaluated.

Also `Silmaril.Elf.parse_frame` (`Task.parse_frame`: under `AvoidsCode`, the parse never depends on
code bytes) and `avoidsCode_of_sub` (`AvoidsCode` checked on pages).

Proofs: `Silmaril.Proofs.Elf.Check.{Sound,Frame}` (standard axioms only).
-/

@[expose] public section

namespace Silmaril.Elf.Check

open Silmaril.Elf.Link.DynElf (Chunk ChunksOf pageRead)
open Silmaril.X86.Link (Blob)

theorem sub_pages {F : Blob} {c : Nat} {pg : List Chunk} (hc : ChunksOf F pg) :
    Sub (pageRead c pg) F := fun _ _ _ h => Silmaril.Elf.Link.DynElf.pageRead_of hc h

/-- **A parse row from a run of the checker on the pages of a file.** -/
theorem parses_of_pages {F : Blob} {pg : List Chunk} (hc : ChunksOf F pg) {A : File}
    (h : file (pageRead 4096 pg) A = true) : Parses F A :=
  file_sound (sub_pages hc) h

end Silmaril.Elf.Check
