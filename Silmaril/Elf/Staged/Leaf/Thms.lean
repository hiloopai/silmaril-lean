module

public import Silmaril.Elf.Staged.Leaf.Defs
public import Silmaril.Elf.Staged.Thms
public import Silmaril.Elf.Staged.Symbols.Thms

/-! # The ELF leaves and their two runs

`Leaf.of_native` and `Leaf.of_kernel` turn either run of a leaf into its proposition about the
same file; the leaves of the table in `Leaf.Defs` follow, each sound by a stage lemma. -/

@[expose] public section

namespace Silmaril.Elf.Staged

open Silmaril.Formats.ELF (SectionHeader Rela)
open Silmaril.Elf.Link.DynElf (Chunk ChunksOf)
open Silmaril.X86.Link (Blob)

/-- **A native run** (on the `ByteArray` of `b`) establishes the leaf's proposition about
`blobOf b`. -/
theorem Leaf.of_native {σ : Type} (l : Leaf σ) {b : Silmaril.Formats.Bytes} {c : σ}
    (h : l.native b c = true) : l.P (blobOf b) c :=
  l.sound (sub_fast b) h

/-- **A kernel run** (on the pages of `F`) establishes the same proposition. -/
theorem Leaf.of_kernel {σ : Type} (l : Leaf σ) {F : Blob} {pg : List Chunk} (hc : ChunksOf F pg)
    {c : σ} (h : l.kernel pg c = true) : l.P F c :=
  l.sound (Check.sub_pages hc) h

/-- **A kernel-bytes run** establishes the same proposition about the file of those bytes. -/
theorem Leaf.of_kbytes {σ : Type} (l : Leaf σ) {x : Silmaril.KBytes} (hx : x.wf = true)
    {raw : ByteArray} (h : x.toByteArray = raw) {c : σ} (hk : l.kbytes x c = true) :
    l.P (blobOf ⟨raw⟩) c :=
  l.sound (sub_kbytes x hx h) hk

/-- `elf.layout`. -/
def Leaf.layout : Leaf Layout where
  name := "elf.layout"
  P := LayoutIs
  run r L := readLayout.run r == some L
  sound hs h := layoutIs_of_sub hs (beq_iff_eq.mp h)

/-- `elf.body`. -/
def Leaf.body : Leaf (Layout × SectionHeader × Body) where
  name := "elf.body"
  P F c := BodyIs F c.1 c.2.1 c.2.2
  run r c := (Parse.body c.1.shs c.2.1).run r == some c.2.2
  sound hs h := bodyIs_of_sub hs (beq_iff_eq.mp h)

/-- `elf.loader`. -/
def Leaf.loader : Leaf (Layout × Loader) where
  name := "elf.loader"
  P F c := LoaderIs F c.1 c.2
  run r c := (readLoader c.1.phdrs).run r == some c.2
  sound hs h := loaderIs_of_sub hs (beq_iff_eq.mp h)

/-- `elf.rela`: a window of a `RELA` table (offset, first index, entries). -/
def Leaf.rela : Leaf (Nat × Nat × List Rela) where
  name := "elf.rela"
  P F c := EntriesAt F Parse.rela c.1 24 c.2.1 c.2.2
  run r c := entriesOk r Parse.rela c.1 24 c.2.1 c.2.2
  sound hs h := entriesAt_of_ok hs h

/-- `elf.tiles`: consecutive tiles lie in the file. -/
def Leaf.tiles : Leaf (Nat × List Nat) where
  name := "elf.tiles"
  P F c := TilesAt F (fun _ _ => true) c.1 c.2
  run r c := tilesOk r (fun _ _ => true) c.1 c.2
  sound hs h := tilesAt_of_ok hs h

/-- `elf.tiles.x86`: each tile is one instruction of the local x86 model. -/
def Leaf.tilesX86 : Leaf (Nat × List Nat) where
  name := "elf.tiles.x86"
  P F c := TilesAt F x86Ok c.1 c.2
  run r c := tilesOk r x86Ok c.1 c.2
  sound hs h := tilesAt_of_ok hs h

/-- `elf.symbols.byName`. -/
def Leaf.byName : Leaf Symbols.ByName where
  name := "elf.symbols.byName"
  P F x := x.sorted = true ∧ x.Sound F
  run := Symbols.byNameOk
  sound hs h := Symbols.byNameOk_sound hs h

/-- `elf.symbols.byAddr`. -/
def Leaf.byAddr : Leaf Symbols.ByAddr where
  name := "elf.symbols.byAddr"
  P F x := x.sorted = true ∧ x.Sound F
  run := Symbols.byAddrOk
  sound hs h := Symbols.byAddrOk_sound hs h

end Silmaril.Elf.Staged
