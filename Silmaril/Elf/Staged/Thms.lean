module

public import Silmaril.Elf.Staged.Defs
public import Silmaril.Elf.Check.Thms
public import Silmaril.Prelude.Bytes.Defs
import Silmaril.Proofs.Elf.Staged.Stages
import Silmaril.Proofs.Elf.Staged.Fast

/-! # Staged parsing: the stages are the parse

PROVED (standard axioms; proofs in `Silmaril.Proofs.Elf.Staged.{Stages,Fast}`).

* `parses_iff`: `Parses F A` holds exactly when the layout, every section body and the loader
  view of `A` are the stage facts of `F`. `parses_assemble` builds a parse from a layout, one
  body per section and a loader view, each established separately.
* `layoutIs_of_sub`, `bodyIs_of_sub`, `loaderIs_of_sub`: a stage fact from a run of its reader
  on any source that answers as the file; `…_of_pages` on the 4 KiB pages of an included file
  (paranoid, `decide +kernel`); `sub_fast`: `fastRead` on the bytes of a value is such a source
  (fast, compiled).
* `entriesAt_append`, `entriesAt_of_ok`, `bodyIs_relas_iff`: a `RELA` table checked window by
  window; `tilesAt_of_ok`: byte tiles (instruction boundaries) checked one read each.
-/

@[expose] public section

namespace Silmaril.Elf.Staged

open Silmaril.Formats.ELF (SectionHeader Rela)
open Silmaril.Elf.Link.DynElf (Rd blobRead Chunk ChunksOf pageRead)
open Silmaril.Elf.Check (Src Sub)
open Silmaril.X86.Link (Blob)

variable {F : Blob} {r : Src}

/-! ## The stages are the parse -/

/-- **A parse is its stages.** -/
theorem parses_iff (F : Blob) (A : File) :
    Parses F A ↔ LayoutIs F A.layout ∧ (∀ s ∈ A.sections, BodyIs F A.layout s.header s.body) ∧
      LoaderIs F A.layout A.loader :=
  Proofs.Elf.Staged.parses_iff F A

/-- **A parse from separately established stages.** -/
theorem parses_assemble {L : Layout} {bodies : List Body} {ld : Loader}
    (hL : LayoutIs F L) (hb : List.Forall₂ (fun s b => BodyIs F L s.header b) L.sections bodies)
    (hld : LoaderIs F L ld) : Parses F (L.assemble bodies ld) :=
  Proofs.Elf.Staged.parses_assemble hL hb hld

/-! ## Stage facts from byte sources -/

theorem layoutIs_of_sub (hs : Sub r F) {L : Layout} (h : readLayout.run r = some L) :
    LayoutIs F L :=
  Rd.run_mono hs _ _ h

theorem bodyIs_of_sub (hs : Sub r F) {L : Layout} {sh : SectionHeader} {b : Body}
    (h : (Parse.body L.shs sh).run r = some b) : BodyIs F L sh b :=
  Rd.run_mono hs _ _ h

theorem loaderIs_of_sub (hs : Sub r F) {L : Layout} {ld : Loader}
    (h : (readLoader L.phdrs).run r = some ld) : LoaderIs F L ld :=
  Rd.run_mono hs _ _ h

/-- Paranoid mode: the layout from a kernel run on the pages of the file. -/
theorem layoutIs_of_pages {pg : List Chunk} (hc : ChunksOf F pg) {L : Layout}
    (h : readLayout.run (pageRead 4096 pg) = some L) : LayoutIs F L :=
  layoutIs_of_sub (Check.sub_pages hc) h

theorem bodyIs_of_pages {pg : List Chunk} (hc : ChunksOf F pg) {L : Layout} {sh : SectionHeader}
    {b : Body} (h : (Parse.body L.shs sh).run (pageRead 4096 pg) = some b) : BodyIs F L sh b :=
  bodyIs_of_sub (Check.sub_pages hc) h

theorem loaderIs_of_pages {pg : List Chunk} (hc : ChunksOf F pg) {L : Layout} {ld : Loader}
    (h : (readLoader L.phdrs).run (pageRead 4096 pg) = some ld) : LoaderIs F L ld :=
  loaderIs_of_sub (Check.sub_pages hc) h

/-- Fast mode: `fastRead` on the bytes of `b` answers as the file `blobOf b`. -/
theorem sub_fast (b : Silmaril.Formats.Bytes) : Sub (fastRead b.data) (blobOf b) :=
  Proofs.Elf.Staged.sub_fast b

/-- Kernel bytes (`Silmaril.KBytes`) answer as the file of their bytes. -/
theorem sub_kbytes (x : Silmaril.KBytes) (hx : x.wf = true) {raw : ByteArray}
    (h : x.toByteArray = raw) : Sub x.readLE (blobOf ⟨raw⟩) :=
  Proofs.Elf.Staged.sub_kbytes x hx h

/-! ## Windows -/

theorem entriesAt_append {α : Type} {p : Nat → Rd α} {o w i : Nat} {es₁ es₂ : List α} :
    EntriesAt F p o w i (es₁ ++ es₂) ↔
      EntriesAt F p o w i es₁ ∧ EntriesAt F p o w (i + es₁.length) es₂ :=
  Proofs.Elf.Staged.entriesAt_append

theorem entriesAt_of_ok {α : Type} [BEq α] [LawfulBEq α] (hs : Sub r F) {p : Nat → Rd α}
    {o w i : Nat} {es : List α} (h : entriesOk r p o w i es = true) : EntriesAt F p o w i es :=
  Proofs.Elf.Staged.entriesAt_of_ok hs i es h

/-- **A `RELA` body is a covering by windows.** -/
theorem bodyIs_relas_iff {L : Layout} {sh : SectionHeader} {es : List Rela}
    (hk : sh.kind = SHT_RELA) :
    BodyIs F L sh (.relas es) ↔
      sh.entrySize = 24 ∧ es.length = sh.size / 24 ∧ EntriesAt F Parse.rela sh.offset 24 0 es :=
  Proofs.Elf.Staged.bodyIs_relas_iff hk

theorem tilesAt_of_ok (hs : Sub r F) {ok : Nat → Nat → Bool} {o : Nat} {lens : List Nat}
    (h : tilesOk r ok o lens = true) : TilesAt F ok o lens :=
  Proofs.Elf.Staged.tilesAt_of_ok hs o lens h

end Silmaril.Elf.Staged
