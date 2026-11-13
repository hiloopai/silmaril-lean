module

public import Silmaril.Elf.Parse.Defs
public import Silmaril.Elf.Check.Defs

/-! # Staged parsing of ELF64 files (`Silmaril.Elf.Staged`)

`Silmaril.Elf.read` parses a whole file at once: every section body, every symbol name, every
relocation. For a multi-megabyte executable that is the wrong unit of work: a proof about one
function needs the layout and a few pages of `.text`, not the 21,594 `RELA` entries of
`.rela.dyn`. This module splits **the same specification** into stages, each a fact about the
file `F` (a `Blob`) that can be established on its own, by any byte source agreeing with `F`,
and later recombined (`Staged.parses_iff`, in `Thms`):

| stage | fact | what it reads |
|---|---|---|
| 1. layout | `LayoutIs F L` | ELF header, program headers, section headers, section names |
| 2. section bodies | `BodyIs F L sh b` | one section's table, as `Parse.body` |
| 2'. loader view | `LoaderIs F L ld` | `PT_DYNAMIC`, `PT_INTERP`, the `DT_STRTAB` names |
| 3. windows | `EntriesAt F p o w i es`, `TilesAt F ok o lens` | entries `i, i+1, …` of a table; byte tiles of a span |

Every stage fact is the **specification's own sub-reader** run on the whole file
(`(Parse.header).run (blobRead F) = some h`, …), so nothing in a stage needs a separate
specification, and `parses_iff` says the stages are exactly the parse.

## The layout is a set of named byte views

`Layout` keeps section headers and names but **no payloads**: a section, a segment or any
window of either is a `Span` (offset, length) into the file, read through whatever source
checks it (`pageRead` on 4 KiB literals in the kernel, `fastRead` on a `ByteArray` natively).
`Layout.section? ".text"` names a section; `Layout.segmentOf` finds the `PT_LOAD` that maps it,
`Layout.vaddrOf` turns a file offset in it into the virtual address a disassembler prints, and
`Layout.offsetOf` goes back.
`Layout.boundsOk` checks that every span lies inside the file.

## Byte sources and modes

A stage fact is closed by running its reader on a source `r` with `Check.Sub r F` (every read
`r` answers, `F` answers the same; `Rd.run_mono` transfers the result):

* **paranoid** (kernel): `r = pageRead 4096 pg` on the pages of an `include_bytes` file;
  `decide +kernel` evaluates the reader; every read touches one 4 KiB literal.
* **fast** (compiled): `r = fastRead a` on a `ByteArray` (`sub_fast`, `Thms`). Running a stage
  this way in a compiled tool is trusted computation (the Lean compiler and runtime). Turning
  such a run into a theorem uses compiled evaluation: on the current toolchain each such
  computation adds its own auxiliary axiom (`thm._native.…​.ax_…`, one per
  computation, not a shared `Lean.ofReduceBool`), which the policy must allow by name. The
  lemmas are stated so that the Boolean run on `fastRead` is the only gap.

## Piecewise certificates

A stage-3 window is a certificate checkable on its own: `entriesOk r p o w i es` checks the
records `i … i + |es| - 1` of a table; `EntriesAt.append` glues adjacent windows, and
`bodyIs_relas_iff` turns a covering of `.rela.dyn` into its `BodyIs` fact. `tilesOk r ok o lens`
checks that consecutive tiles of lengths `lens` from `o` (instruction boundaries claimed by a
disassembler) each satisfy a per-tile predicate `ok` on their bytes (an ISA decoder's
acceptance), one read per tile.
-/

@[expose] public section

namespace Silmaril.Elf.Staged

open Silmaril.Formats.ELF (Header ProgramHeader SectionHeader NameBytes Rela)
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Check (Src)
open Silmaril.X86.Link (Blob)

/-! ## Stage 1: the layout -/

/-- A section of the layout: its header and name; its body is not read. -/
structure Sec where
  header : SectionHeader
  name : NameBytes
  deriving DecidableEq, Repr

/-- **The layout of an ELF64 file**: the header, the program headers and the named sections. -/
structure Layout where
  header : Header
  phdrs : List ProgramHeader
  sections : List Sec
  deriving DecidableEq, Repr

/-- The section headers of a layout. -/
def Layout.shs (L : Layout) : List SectionHeader := L.sections.map (·.header)

/-- The named sections (as `Parse.sections`, without the bodies). -/
def readSecs (h : Header) (shs : List SectionHeader) : Rd (List Sec) :=
  if shs.isEmpty then pure [] else do
    let names ← Rd.ofOption shs[h.sectionNameIndex]?
    shs.mapM fun sh => do
      let n ← Parse.strAt names sh.name
      pure ⟨sh, n⟩

/-- **The stage-1 reader**: header, program headers, section headers and names. -/
def readLayout : Rd Layout := do
  let h ← Parse.header
  let phs ← Parse.phdrs h
  let shs ← Parse.shdrs h
  let secs ← readSecs h shs
  pure ⟨h, phs, secs⟩

/-- **`L` is the layout of `F`.** -/
def LayoutIs (F : Blob) (L : Layout) : Prop := readLayout.run (blobRead F) = some L

/-! ## Stage 2: section bodies and the loader view -/

/-- **The body of section `sh` of `F` is `b`** (`Parse.body` against the layout's headers). -/
def BodyIs (F : Blob) (L : Layout) (sh : SectionHeader) (b : Body) : Prop :=
  (Parse.body L.shs sh).run (blobRead F) = some b

/-- The loader's view of a file (the fields of `File` read from the program headers). -/
structure Loader where
  dynamic : List Dyn
  interp : Option NameBytes
  needed : List NameBytes
  soname : Option NameBytes
  runpath : Option NameBytes
  deriving DecidableEq, Repr

/-- The loader's view, read as in `Silmaril.Elf.read`. -/
def readLoader (phs : List ProgramHeader) : Rd Loader := do
  let dyn ← Parse.dynamic phs
  let ip ← Parse.interp phs
  let str := Parse.dynStr phs dyn
  let needed ← ((dyn.filter (·.tag == DT_NEEDED)).map (·.val)).mapM str
  let soname ← Parse.optStr str ((dyn.find? (·.tag == DT_SONAME)).map (·.val))
  let runpath ← Parse.optStr str
    (((dyn.find? (·.tag == DT_RUNPATH)).orElse fun _ => dyn.find? (·.tag == DT_RPATH)).map (·.val))
  pure ⟨dyn, ip, needed, soname, runpath⟩

/-- **The loader's view of `F` is `ld`.** -/
def LoaderIs (F : Blob) (L : Layout) (ld : Loader) : Prop :=
  (readLoader L.phdrs).run (blobRead F) = some ld

/-- The layout of a parse. -/
def _root_.Silmaril.Elf.File.layout (A : File) : Layout :=
  ⟨A.header, A.phdrs, A.sections.map fun s => ⟨s.header, s.name⟩⟩

/-- The loader's view of a parse. -/
def _root_.Silmaril.Elf.File.loader (A : File) : Loader :=
  ⟨A.dynamic, A.interp, A.needed, A.soname, A.runpath⟩

/-- A layout, bodies (one per section, in order) and a loader view, as a parse. -/
def Layout.assemble (L : Layout) (bodies : List Body) (ld : Loader) : File :=
  ⟨L.header, L.phdrs, L.sections.zipWith (fun s b => ⟨s.header, s.name, b⟩) bodies,
    ld.dynamic, ld.interp, ld.needed, ld.soname, ld.runpath⟩

/-! ## Named byte views -/

/-- The bytes a section occupies in the file (none for `SHT_NOBITS`). -/
def Sec.span (s : Sec) : Span :=
  ⟨s.header.offset, if s.header.kind = SHT_NOBITS then 0 else s.header.size⟩

/-- The bytes a segment maps from the file. -/
def phSpan (ph : ProgramHeader) : Span := ⟨ph.offset, ph.fileSize⟩

/-- The first section named `n`. -/
def Layout.section? (L : Layout) (n : String) : Option Sec :=
  L.sections.find? (·.name == nameOf n)

/-- The `PT_LOAD` segment whose file bytes contain the span `s`. -/
def Layout.segmentOf (L : Layout) (s : Span) : Option ProgramHeader :=
  L.phdrs.find? fun ph => ph.kind == PT_LOAD && decide ((phSpan ph).Contains s.off s.len)

/-- The virtual address of file offset `o`, through the `PT_LOAD` that maps it. -/
def Layout.vaddrOf (L : Layout) (o : Nat) : Option Nat :=
  (L.segmentOf ⟨o, 1⟩).map fun ph => o - ph.offset + ph.virtualAddress

/-- The file offset of virtual address `v`, through the `PT_LOAD` that maps it from the file. -/
def Layout.offsetOf (L : Layout) (v : Nat) : Option Nat :=
  (L.phdrs.find? fun ph => ph.kind == PT_LOAD && decide (ph.virtualAddress ≤ v) &&
    decide (v < ph.virtualAddress + ph.fileSize)).map fun ph => v - ph.virtualAddress + ph.offset

/-- A window of a span: `len` bytes at `o`, if inside it. -/
def Span.window (s : Span) (o len : Nat) : Option Span :=
  if s.Contains o len then some ⟨o, len⟩ else none

/-- **Every span of the layout lies in a file of `len` bytes**: the header tables, every
section's bytes and every segment's file bytes. -/
def Layout.boundsOk (L : Layout) (len : Nat) : Bool :=
  let h := L.header
  decide (h.programOffset + 56 * h.programCount ≤ len) &&
    decide (h.sectionOffset + 64 * h.sectionCount ≤ len) &&
    L.sections.all (fun s => decide (s.span.off + s.span.len ≤ len)) &&
    L.phdrs.all fun ph => decide (ph.offset + ph.fileSize ≤ len)

/-! ## Stage 3: windows of tables -/

/-- **Records `i, i + 1, …` of the table of `w`-byte records at `o`, read by `p`, are `es`.** -/
def EntriesAt {α : Type} (F : Blob) (p : Nat → Rd α) (o w i : Nat) (es : List α) : Prop :=
  ∀ j (hj : j < es.length), (p (o + w * (i + j))).run (blobRead F) = some es[j]

/-- The window check behind `EntriesAt`, on any source (one run of `p` per record). -/
def entriesOk {α : Type} [BEq α] (r : Src) (p : Nat → Rd α) (o w : Nat) : Nat → List α → Bool
  | _, [] => true
  | i, e :: es => (p (o + w * i)).run r == some e && entriesOk r p o w (i + 1) es

/-! ## Stage 3: byte tiles (instruction boundaries) -/

/-- **Tiles of lengths `lens` from `o` each satisfy `ok`**: tile `k` starts where tile `k - 1`
ends, and `ok len v` holds of its length and of its bytes `v` (little-endian). -/
def TilesAt (F : Blob) (ok : Nat → Nat → Bool) : Nat → List Nat → Prop
  | _, [] => True
  | o, l :: ls => (∃ v, blobRead F o l = some v ∧ ok l v = true) ∧ TilesAt F ok (o + l) ls

/-- The tile check, one read per tile. -/
def tilesOk (r : Src) (ok : Nat → Nat → Bool) : Nat → List Nat → Bool
  | _, [] => true
  | o, l :: ls => (match r o l with | some v => ok l v | none => false) && tilesOk r ok (o + l) ls

/-- The tiles cover the span `s` exactly. -/
def tilesCover (s : Span) (lens : List Nat) : Bool := lens.all (0 < ·) && lens.sum == s.len

/-! ## The fast source -/

/-- **`w` bytes at `o` of a `ByteArray`**, little-endian (as `Silmaril.Formats.ELF.readLE`;
compiled to direct indexing). -/
def fastRead (a : ByteArray) (o : Nat) : Nat → Option Nat
  | 0 => some 0
  | w + 1 =>
    if h : o < a.size then
      (fastRead a (o + 1) w).map fun rest => a[o].toNat + 256 * rest
    else none

end Silmaril.Elf.Staged
