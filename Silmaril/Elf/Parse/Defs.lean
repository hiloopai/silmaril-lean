module

public import Silmaril.Elf.Ast.Defs
public import Silmaril.Elf.Link.Dyn.Elf.Defs
public import Silmaril.Project.Formats.Elf.Defs

/-! # The parse problem: a file's bytes to its metadata (`Silmaril.Elf.Parses`)

**One parse per file.** `read : Rd File` is the specification of the parse: a reading program
(`Silmaril.Elf.Link.DynElf.Rd`, a free monad over `read offset width`), so that

* it runs on any byte source, the whole file (`blobRead`), its 4 KiB pages (`pageRead`) or a
  sparse view (`sparseRead`), and a result on a sparse view transfers to the file
  (`DynElf.run_sparse`, `Rd.run_mono`): every fact below is checkable without the kernel ever
  forcing a 2 MB number;
* the reads it makes are explicit, which is what the frame theorem (`Task.parse_frame`:
  the parse never reads code bytes) is about.

`Parses F A` says the parse of `F` is `A`. It determines `A` (`parses_unique`, `Thms`), so a
*fact* about `F` is a property of its one AST (`Silmaril.Elf.Facts`).

**Checking a parse.** `read` is a specification, not a fast checker: run by the kernel it reads
names byte by byte (`DynElf.Elf.cstr`, about 47 s for libc's 3,156 dynamic symbols). The
parse builder proves `Parses F A` for a concrete `A` (emitted by a Rust tool) with a **named
checker** (direct decoders over metadata pieces, names compared as wide reads) and a
soundness theorem `check … = true → Parses F A` (`Check.file_sound`). A
claim that only *assumes* an emitted AST says so: it is conditional on the open problem
`silmaril.shapes.elf.parses` for that file and AST, never an axiom.

**What is checked.** The ELF identification (`ELFCLASS64`, `ELFDATA2LSB`, `EV_CURRENT`), the
table entry sizes, that names are NUL-terminated inside their string tables (by the fuel of
`cstr`), and that every table read is a read of the file. Not checked here: `e_machine`
(any machine parses), alignment, overlap and the agreement of the section and loader views
(`DynConsistent`, `Silmaril.Elf.Lookup`). Extended numbering (`e_shnum = 0` with a large
`sh_size` of section 0) is not supported: such a file parses with no sections.
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.Formats.ELF (Header ProgramHeader SectionHeader Symbol Rela NameBytes ObjectSymbol)
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Link.DynElf.Elf (u8 u16 u32 u64 cstr dynFrom)
open Silmaril.X86.Link (Blob)

namespace Parse

/-- A name read as bytes. -/
def toName (n : List Nat) : NameBytes := n.map (BitVec.ofNat 8)

/-- The NUL-terminated name at `o`, within `fuel` bytes. -/
def name (o fuel : Nat) : Rd NameBytes := do
  let n ← cstr o fuel
  pure (toName n)

/-- The ELF header (as `Silmaril.Formats.ELF.readHeader`). -/
def header : Rd Header := do
  Rd.guard ((← u32 0) = 0x464c457f)
  Rd.guard ((← u8 4) = 2)
  Rd.guard ((← u8 5) = 1)
  Rd.guard ((← u8 6) = 1)
  let osABI ← u8 7
  let abiVersion ← u8 8
  let fileType ← u16 16
  let machine ← u16 18
  let version ← u32 20
  let entry ← u64 24
  let programOffset ← u64 32
  let sectionOffset ← u64 40
  let flags ← u32 48
  let headerSize ← u16 52
  let programEntrySize ← u16 54
  let programCount ← u16 56
  let sectionEntrySize ← u16 58
  let sectionCount ← u16 60
  let sectionNameIndex ← u16 62
  pure ⟨osABI, abiVersion, fileType, machine, version, entry, programOffset, sectionOffset,
    flags, headerSize, programEntrySize, programCount, sectionEntrySize, sectionCount,
    sectionNameIndex⟩

/-- A program header at `o`. -/
def phdr (o : Nat) : Rd ProgramHeader := do
  let kind ← u32 o
  let flags ← u32 (o + 4)
  let offset ← u64 (o + 8)
  let virtualAddress ← u64 (o + 16)
  let physicalAddress ← u64 (o + 24)
  let fileSize ← u64 (o + 32)
  let memorySize ← u64 (o + 40)
  let alignment ← u64 (o + 48)
  pure ⟨kind, flags, offset, virtualAddress, physicalAddress, fileSize, memorySize, alignment⟩

/-- The program headers (`e_phentsize = 56`). -/
def phdrs (h : Header) : Rd (List ProgramHeader) :=
  if h.programCount = 0 then pure [] else do
    Rd.guard (h.programEntrySize = 56)
    (List.range h.programCount).mapM fun i => phdr (h.programOffset + 56 * i)

/-- A section header at `o`. -/
def shdr (o : Nat) : Rd SectionHeader := do
  let name ← u32 o
  let kind ← u32 (o + 4)
  let flags ← u64 (o + 8)
  let address ← u64 (o + 16)
  let offset ← u64 (o + 24)
  let size ← u64 (o + 32)
  let link ← u32 (o + 40)
  let info ← u32 (o + 44)
  let alignment ← u64 (o + 48)
  let entrySize ← u64 (o + 56)
  pure ⟨name, kind, flags, address, offset, size, link, info, alignment, entrySize⟩

/-- The section headers (`e_shentsize = 64`). -/
def shdrs (h : Header) : Rd (List SectionHeader) :=
  if h.sectionCount = 0 then pure [] else do
    Rd.guard (h.sectionEntrySize = 64)
    (List.range h.sectionCount).mapM fun i => shdr (h.sectionOffset + 64 * i)

/-- The name at offset `i` of the string table `strs` (a section header). -/
def strAt (strs : SectionHeader) (i : Nat) : Rd NameBytes := do
  Rd.guard (i < strs.size)
  name (strs.offset + i) (strs.size - i)

/-- The `k` fixed-size records of `w` bytes from `o`. -/
def records {α : Type} (o w k : Nat) (r : Nat → Rd α) : Rd (List α) :=
  (List.range k).mapM fun i => r (o + w * i)

/-- A symbol at `o`, named from the string table `strs`. -/
def symbol (strs : SectionHeader) (o : Nat) : Rd ObjectSymbol := do
  let nm ← u32 o
  let info ← u8 (o + 4)
  let other ← u8 (o + 5)
  let sectionIndex ← u16 (o + 6)
  let value ← u64 (o + 8)
  let size ← u64 (o + 16)
  let n ← strAt strs nm
  pure ⟨⟨nm, info, other, sectionIndex, value, size⟩, n⟩

/-- A RELA entry at `o`. -/
def rela (o : Nat) : Rd Rela := do
  let offset ← u64 o
  let info ← u64 (o + 8)
  let a ← u64 (o + 16)
  pure ⟨offset, info, Silmaril.Formats.ELF.signed64 a⟩

/-- A REL entry at `o`. -/
def rel (o : Nat) : Rd Rel := do
  let offset ← u64 o
  let info ← u64 (o + 8)
  pure ⟨offset, info⟩

/-- The GNU hash table of a section. -/
def gnuHash (sh : SectionHeader) : Rd GnuHash := do
  let o := sh.offset
  let nb ← u32 o
  let symoffset ← u32 (o + 4)
  let bsz ← u32 (o + 8)
  let shift ← u32 (o + 12)
  let head := 16 + 8 * bsz + 4 * nb
  Rd.guard (head ≤ sh.size)
  let bloom ← records (o + 16) 8 bsz u64
  let buckets ← records (o + 16 + 8 * bsz) 4 nb u32
  let chain ← records (o + head) 4 ((sh.size - head) / 4) u32
  pure ⟨nb, symoffset, shift, bloom, buckets, chain⟩

/-- The SysV hash table of a section. -/
def sysvHash (sh : SectionHeader) : Rd SysvHash := do
  let nb ← u32 sh.offset
  let nc ← u32 (sh.offset + 4)
  let buckets ← records (sh.offset + 8) 4 nb u32
  let chains ← records (sh.offset + 8 + 4 * nb) 4 nc u32
  pure ⟨buckets, chains⟩

/-- `k` `Elf64_Verdaux` names from `o`. -/
def verdaux (strs : SectionHeader) : Nat → Nat → Rd (List NameBytes)
  | 0, _ => pure []
  | k + 1, o => do
    let nm ← u32 o
    let next ← u32 (o + 4)
    let n ← strAt strs nm
    let rest ← if next = 0 then pure [] else verdaux strs k (o + next)
    pure (n :: rest)

/-- `k` version definitions from `o` (`k = sh_info`). -/
def verdefs (strs : SectionHeader) : Nat → Nat → Rd (List Verdef)
  | 0, _ => pure []
  | k + 1, o => do
    let version ← u16 o
    let flags ← u16 (o + 2)
    let ndx ← u16 (o + 4)
    let cnt ← u16 (o + 6)
    let hash ← u32 (o + 8)
    let aux ← u32 (o + 12)
    let next ← u32 (o + 16)
    let names ← verdaux strs cnt (o + aux)
    let rest ← if next = 0 then pure [] else verdefs strs k (o + next)
    pure (⟨version, flags, ndx, hash, names⟩ :: rest)

/-- `k` `Elf64_Vernaux` entries from `o`. -/
def vernaux (strs : SectionHeader) : Nat → Nat → Rd (List Vernaux)
  | 0, _ => pure []
  | k + 1, o => do
    let hash ← u32 o
    let flags ← u16 (o + 4)
    let other ← u16 (o + 6)
    let nm ← u32 (o + 8)
    let next ← u32 (o + 12)
    let n ← strAt strs nm
    let rest ← if next = 0 then pure [] else vernaux strs k (o + next)
    pure (⟨hash, flags, other, n⟩ :: rest)

/-- `k` version requirements from `o` (`k = sh_info`). -/
def verneeds (strs : SectionHeader) : Nat → Nat → Rd (List Verneed)
  | 0, _ => pure []
  | k + 1, o => do
    let version ← u16 o
    let cnt ← u16 (o + 2)
    let file ← u32 (o + 4)
    let aux ← u32 (o + 8)
    let next ← u32 (o + 12)
    let f ← strAt strs file
    let auxs ← vernaux strs cnt (o + aux)
    let rest ← if next = 0 then pure [] else verneeds strs k (o + next)
    pure (⟨version, f, auxs⟩ :: rest)

/-- Round `n` up to a multiple of `a` (`a ≥ 1`). -/
def alignUp (n a : Nat) : Nat := (n + a - 1) / a * a

/-- The notes of a section from `o` to `stop`, entries aligned to `a`; `fuel` bounds the walk.
The descriptor starts at `alignUp (12 + namesz) a` from the note and the next note at
`alignUp (desc + descsz) a` (binutils' `ELF_NOTE_DESC_OFFSET`/`ELF_NOTE_NEXT_OFFSET`; with
`a = 8`, as in `.note.gnu.property`, this differs from aligning `namesz` alone). -/
def notes (a stop : Nat) : Nat → Nat → Rd (List Note)
  | 0, _ => pure []
  | fuel + 1, o =>
    if stop < o + 12 then pure [] else do
      let namesz ← u32 o
      let descsz ← u32 (o + 4)
      let type ← u32 (o + 8)
      let nm ← if namesz = 0 then pure 0 else Rd.le (o + 12) (namesz - 1)
      let n := (List.range (namesz - 1)).map fun i => BitVec.ofNat 8 (nm >>> (8 * i))
      let d := o + alignUp (12 + namesz) a
      let next := o + alignUp (alignUp (12 + namesz) a + descsz) a
      Rd.guard (next ≤ stop)
      let rest ← notes a stop fuel next
      pure (⟨n, type, ⟨d, descsz⟩⟩ :: rest)

/-- **The body of a section** (`Ast.Body`, by `sh_type`). -/
def body (shs : List SectionHeader) (sh : SectionHeader) : Rd Body :=
  let span : Span := ⟨sh.offset, sh.size⟩
  let linked : Rd SectionHeader := Rd.ofOption shs[sh.link]?
  if sh.kind = SHT_NULL then pure .null
  else if sh.kind = SHT_NOBITS then pure .noBits
  else if sh.kind = SHT_PROGBITS then pure (.progbits span)
  else if sh.kind = SHT_STRTAB then pure (.strtab span)
  else if sh.kind = SHT_SYMTAB ∨ sh.kind = SHT_DYNSYM then do
    Rd.guard (sh.entrySize = 24)
    let strs ← linked
    let es ← records sh.offset 24 (sh.size / 24) (symbol strs)
    pure (.symbols (if sh.kind = SHT_SYMTAB then .symtab else .dynsym) es)
  else if sh.kind = SHT_RELA then do
    Rd.guard (sh.entrySize = 24)
    pure (.relas (← records sh.offset 24 (sh.size / 24) rela))
  else if sh.kind = SHT_REL then do
    Rd.guard (sh.entrySize = 16)
    pure (.rels (← records sh.offset 16 (sh.size / 16) rel))
  else if sh.kind = SHT_RELR then do
    return .relr (← records sh.offset 8 (sh.size / 8) u64)
  else if sh.kind = SHT_DYNAMIC then do
    let es ← dynFrom sh.offset (sh.size / 16)
    pure (.dynamic (es.map fun (t, v) => (⟨t, v⟩ : Dyn)))
  else if sh.kind = SHT_GNU_HASH then do return .gnuHash (← gnuHash sh)
  else if sh.kind = SHT_HASH then do return .hash (← sysvHash sh)
  else if sh.kind = SHT_GNU_versym then do
    return .versym (← records sh.offset 2 (sh.size / 2) u16)
  else if sh.kind = SHT_GNU_verdef then do
    let strs ← linked
    return .verdef (← verdefs strs sh.info sh.offset)
  else if sh.kind = SHT_GNU_verneed then do
    let strs ← linked
    return .verneed (← verneeds strs sh.info sh.offset)
  else if sh.kind = SHT_NOTE then do
    return .notes (← notes (max 4 sh.alignment) (sh.offset + sh.size) (sh.size / 12 + 1) sh.offset)
  else pure (.other span)

/-- The sections: headers, names from `.shstrtab` (`e_shstrndx`), bodies. -/
def sections (h : Header) (shs : List SectionHeader) : Rd (List Section) :=
  if shs.isEmpty then pure [] else do
    let names ← Rd.ofOption shs[h.sectionNameIndex]?
    shs.mapM fun sh => do
      let n ← strAt names sh.name
      let b ← body shs sh
      pure ⟨sh, n, b⟩

/-- The file offset of virtual address `v` (as `File.vToOff`). -/
def vToOff (phs : List ProgramHeader) (v : Nat) : Option Nat :=
  ((phs.filter (·.kind == PT_LOAD)).find? fun ph =>
    ph.virtualAddress ≤ v && v < ph.virtualAddress + ph.fileSize).map
    fun ph => v - ph.virtualAddress + ph.offset

/-- The loader's view: `PT_DYNAMIC` entries, and the `DT_STRTAB` string at `i`. -/
def dynamic (phs : List ProgramHeader) : Rd (List Dyn) :=
  match phs.find? (·.kind == PT_DYNAMIC) with
  | none => pure []
  | some d => do
    let es ← dynFrom d.offset (d.fileSize / 16)
    pure (es.map fun (t, v) => (⟨t, v⟩ : Dyn))

/-- A string of `DT_STRTAB` (at most 4096 bytes). -/
def dynStr (phs : List ProgramHeader) (dyn : List Dyn) (i : Nat) : Rd NameBytes := do
  let st ← Rd.ofOption ((dyn.find? (·.tag == Silmaril.Elf.Link.DynElf.Elf.DT_STRTAB)).bind
    fun e => vToOff phs e.val)
  name (st + i) 4096

/-- The `PT_INTERP` string. -/
def interp (phs : List ProgramHeader) : Rd (Option NameBytes) :=
  match phs.find? (·.kind == PT_INTERP) with
  | none => pure none
  | some ph => do return some (← name ph.offset ph.fileSize)

/-- An optional string of `DT_STRTAB`. -/
def optStr (str : Nat → Rd NameBytes) : Option Nat → Rd (Option NameBytes)
  | none => pure none
  | some i => do return some (← str i)

/-- **The reads a reading program makes** when run on `r`, in order, up to the first read `r`
cannot answer (the footprint of a run; `Task.parse_frame`). -/
def trace {α : Type} (r : Nat → Nat → Option Nat) : Rd α → List (Nat × Nat)
  | .pure _ => []
  | .fail => []
  | .read o w k => (o, w) :: match r o w with
    | some v => trace r (k v)
    | none => []

end Parse

/-- **The parse of an ELF64 little-endian file** (the specification; module doc). -/
def read : Rd File := do
  let h ← Parse.header
  let phs ← Parse.phdrs h
  let shs ← Parse.shdrs h
  let secs ← Parse.sections h shs
  let dyn ← Parse.dynamic phs
  let ip ← Parse.interp phs
  let str := Parse.dynStr phs dyn
  let needed ← ((dyn.filter (·.tag == DT_NEEDED)).map (·.val)).mapM str
  let soname ← Parse.optStr str ((dyn.find? (·.tag == DT_SONAME)).map (·.val))
  let runpath ← Parse.optStr str
    (((dyn.find? (·.tag == DT_RUNPATH)).orElse fun _ => dyn.find? (·.tag == DT_RPATH)).map (·.val))
  pure ⟨h, phs, secs, dyn, ip, needed, soname, runpath⟩

/-- The parse of `F`, if it is an ELF64 little-endian file the reader accepts. -/
def parse (F : Blob) : Option File := read.run (blobRead F)

/-- **`A` is the parse of `F`** (the parse problem). -/
def Parses (F : Blob) (A : File) : Prop := parse F = some A

/-- The file of a project value's bytes. -/
def blobOf (b : Silmaril.Formats.Bytes) : Blob := Blob.ofBytes (Silmaril.Project.Formats.elfBytes b)

/-- **The project format `elf.ast`**: bytes to the metadata AST. Unlike `elf.elf64le`
(`ET_REL` only) and `elf.exec-x86` (`ET_EXEC` only), it accepts every object kind. -/
def format : Silmaril.Project.Format Silmaril.Project.blob File :=
  ⟨fun b => parse (blobOf b), none⟩

end Silmaril.Elf
