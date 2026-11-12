module

public import Silmaril.Elf.Bridge.Defs
public import Silmaril.Elf.Link.ElfBind.Thms
public import Silmaril.Elf.Check.Thms
public import Silmaril.Proofs.Elf.Bridge.Silmaril

/-! # Bridges: consequences

PROVED, conditionally on the named bridge goals (taken as hypotheses, never assumed):

* `directCall_of_roLoaded`: **direct-call ⊑ `RoLoaded`**. In memory where the read-only segments
  of `F` are loaded at `base` (`ElfBind.RoLoaded`), the code an API fact `CodeAt` names is
  fetchable at `base + v`: the premise of a direct-call function specification. From `ElfBind.code_loaded` with `Task.codeAt_iff` and
  `Task.placement_iff`.
* `directCall_of_exeLoaded`: the same from the loader relation `Dyn.ExeLoaded`, with
  `Task.roLoaded_of_exeLoaded`.

PROVED outright:

* `check_sound` (`Task.check_sound`): the checker `Silmaril.Elf.Check.file`, whose
  soundness is `Check.file_sound`. `Task.check_sound` (`Nonempty Checker`) only asks for *a*
  sound checker; the content is that this one succeeds on real files within budget: parse rows
  over large files run it on pages (`Check.parses_of_pages`).
* `Check.header_silmaril` (`Task.header_silmaril`): the parse's header is silmaril's
  `readHeader` of the same bytes (`Silmaril.Proofs.Elf.Bridge.Silmaril`);
* `Check.tables_silmaril` (`Task.tables_silmaril`): whenever silmaril's program and section
  header readers succeed, they return the parse's tables.
-/

@[expose] public section

namespace Silmaril.Elf.Bridge

open Silmaril.X86.Link (Blob)
open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)

theorem directCall_of_roLoaded (hc : Task.codeAt_iff) (hp : Task.placement_iff)
    {F : Blob} {A : File} (hA : Parses F A) (hx : A.header.machine = 62)
    (he : A.header.programEntrySize = 56)
    {base : Word} {mem : Memory} {v : Nat} {code : List Byte}
    (hcode : CodeAt F v code) (hplace : Placement F base.toNat) (hl : Silmaril.Elf.Link.ElfBind.RoLoaded F base mem) :
    mem.fetchBytes (base + BitVec.ofNat 64 v).toNat code.length = some code ∧
      (base + BitVec.ofNat 64 v).toNat = base.toNat + v :=
  let h := Silmaril.Elf.Link.ElfBind.code_loaded ((hc F A v code hA hx).2 hcode) ((hp F A base hA hx he).2 hplace) hl
  ⟨h.1, h.2.1⟩

theorem directCall_of_exeLoaded (hc : Task.codeAt_iff) (hp : Task.placement_iff)
    (hel : Task.roLoaded_of_exeLoaded)
    {F : Blob} {A : File} (hA : Parses F A) (hx : A.header.machine = 62)
    (he : A.header.programEntrySize = 56) (hdyn : A.isDynamic)
    (hcons : A.DynConsistent) (hnt : NoTextRel A)
    {fs : List Blob} {base : Word} {bs : List Word} {ifn : Word → Option Word} {lazy : Bool}
    (hgot : lazy = true → NoLazyGotRo A)
    {res : Word} {mem : Memory} {v : Nat} {code : List Byte}
    (hcode : CodeAt F v code) (hplace : Placement F base.toNat)
    (hl : Silmaril.Elf.Link.Dyn.ExeLoaded (F :: fs) (base :: bs) ifn lazy res mem) :
    mem.fetchBytes (base + BitVec.ofNat 64 v).toNat code.length = some code ∧
      (base + BitVec.ofNat 64 v).toNat = base.toNat + v :=
  directCall_of_roLoaded hc hp hA hx he hcode hplace
    (hel F A fs base bs ifn lazy res mem hA hx hdyn hcons hnt hgot ((hp F A base hA hx he).2 hplace) hl)

/-- **The parse builder's checker**: `Check.file` on the whole file (rows run it on pages
instead: `Check.parses_of_pages`). -/
def checker : Checker where
  name := "Silmaril.Elf.Check.file"
  check F A := Check.file (Silmaril.Elf.Link.DynElf.blobRead F) A
  sound _ _ h := Check.file_sound (Check.sub_blobRead _) h

theorem check_sound : Task.check_sound := ⟨checker⟩

end Silmaril.Elf.Bridge
