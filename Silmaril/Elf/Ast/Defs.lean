module

public import Silmaril.Formats.ELF.Object.Types
public import Silmaril.Formats.ELF.Cst.Types

/-! # The typed metadata of an ELF64 file (the AST of `Silmaril.Elf`)

One value per file, `Silmaril.Elf.File`, holding **all the metadata** a loader, a linker or a
binutils-style tool reads, typed, and **references** (`Span`: offset and length) to the
payloads (code, data, string tables, note descriptors), which stay in the file and are read
through pages, pieces or sparse reads (`Silmaril.Elf.Link.DynElf.Rd`).

It extends silmaril-lean's ELF records rather than replacing them: `Header`, `ProgramHeader`,
`SectionHeader`, `Symbol`, `Rela` and `ObjectSymbol` are silmaril's (`Silmaril.Formats.ELF`),
and a section body (`Body`) refines silmaril's shared CST body (`Cst.SectionBody`, which types
only symbols and RELAs) with the dynamic-linking tables:

| body | section type | content |
|---|---|---|
| `symbols t` | `SHT_SYMTAB` (2), `SHT_DYNSYM` (11) | `ObjectSymbol`s (raw entry and resolved name) |
| `relas` / `rels` / `relr` | 4 / 9 / 19 | RELA, REL entries; RELR words |
| `dynamic` | 6 | `(d_tag, d_val)` entries up to `DT_NULL` |
| `gnuHash` / `hash` | `0x6ffffff6` / 5 | the GNU and SysV hash tables |
| `versym` / `verdef` / `verneed` | `0x6fffffff` / `…fd` / `…fe` | symbol versioning |
| `notes` | 7 | notes (name, type, descriptor span) |
| `strtab` / `progbits` / `other` | 3 / 1 / anything else | a span |
| `noBits` / `null` | 8 / 0 | nothing in the file |

Besides the section view (what `readelf -S`, `nm`, `objdump` read), a `File` keeps the
**loader's view**: the `PT_DYNAMIC` entries, `PT_INTERP`, and the strings ld.so resolves from
`DT_STRTAB` (`DT_NEEDED`, `DT_SONAME`, `DT_RUNPATH`/`DT_RPATH`). `DynConsistent` (in
`Silmaril.Elf.Lookup`) says the two views agree; the lookup specification reads the typed
section tables under it.

`File.kind` classifies an object (`Kind`: relocatable, executable, shared object, PIE,
static PIE). Data only: the reader is `Silmaril.Elf.Parse`, the semantics `Silmaril.Elf.Lookup`.
It sits beside the readers of `Silmaril.Formats.ELF` and reuses their record types.
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.Formats.ELF (Header ProgramHeader SectionHeader Symbol Rela NameBytes ObjectSymbol)

/-! ## Constants -/

/-- `e_type`. -/
def ET_REL := 1
def ET_EXEC := 2
def ET_DYN := 3

/-- `p_type`. -/
def PT_LOAD := 1
def PT_DYNAMIC := 2
def PT_INTERP := 3
def PT_NOTE := 4
def PT_TLS := 7
def PT_GNU_RELRO := 0x6474e552

/-- `sh_type`. -/
def SHT_NULL := 0
def SHT_PROGBITS := 1
def SHT_SYMTAB := 2
def SHT_STRTAB := 3
def SHT_RELA := 4
def SHT_HASH := 5
def SHT_DYNAMIC := 6
def SHT_NOTE := 7
def SHT_NOBITS := 8
def SHT_REL := 9
def SHT_DYNSYM := 11
def SHT_RELR := 19
def SHT_GNU_HASH := 0x6ffffff6
def SHT_GNU_verdef := 0x6ffffffd
def SHT_GNU_verneed := 0x6ffffffe
def SHT_GNU_versym := 0x6fffffff

/-- `sh_flags`: `SHF_ALLOC`, `SHF_EXECINSTR`. -/
def SHF_ALLOC := 2
def SHF_EXECINSTR := 4

/-- `DT_FLAGS_1`: `DF_1_PIE`. -/
def DF_1_PIE := 0x08000000

/-- `d_tag`s read here (the loader's own list is `DynElf.Elf.DT_*`). -/
def DT_NULL := 0
def DT_NEEDED := 1
def DT_SONAME := 14
def DT_RPATH := 15
def DT_RUNPATH := 29
def DT_FLAGS_1 := 0x6ffffffb

/-! ## Records -/

/-- The bytes of a string literal, as a name (`nameOf "adler32_z"`). -/
def nameOf (s : String) : NameBytes := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- **A payload reference**: `len` bytes of the file at offset `off`. -/
structure Span where
  off : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- The read of `w` bytes at `o` lies inside the span. -/
def Span.Contains (s : Span) (o w : Nat) : Prop := s.off ≤ o ∧ o + w ≤ s.off + s.len

instance (s : Span) (o w : Nat) : Decidable (s.Contains o w) := inferInstanceAs (Decidable (_ ∧ _))

/-- Which symbol table. -/
inductive Table where
  /-- `.symtab` (`SHT_SYMTAB`): the static symbol table. -/
  | symtab
  /-- `.dynsym` (`SHT_DYNSYM`): the dynamic symbol table. -/
  | dynsym
  deriving DecidableEq, Repr

/-- The section type of a table. -/
def Table.shType : Table → Nat
  | .symtab => SHT_SYMTAB
  | .dynsym => SHT_DYNSYM

/-- A REL entry (implicit addend: the addend is the word at the place). -/
structure Rel where
  offset : Nat
  info : Nat
  deriving DecidableEq, Repr

def Rel.symbolIndex (r : Rel) : Nat := r.info / 2 ^ 32
def Rel.relocationType (r : Rel) : Nat := r.info % 2 ^ 32

/-- A dynamic entry `(d_tag, d_val)`. -/
structure Dyn where
  tag : Nat
  val : Nat
  deriving DecidableEq, Repr

/-- **The GNU hash table** (`DT_GNU_HASH`): `nbuckets`, `symoffset`, the Bloom filter's shift
and words, the buckets, and the chain hash values (`chain[i - symoffset]` for symbol `i`). -/
structure GnuHash where
  nbuckets : Nat
  symoffset : Nat
  bloomShift : Nat
  bloom : List Nat
  buckets : List Nat
  chain : List Nat
  deriving DecidableEq, Repr

/-- The SysV hash table (`DT_HASH`). -/
structure SysvHash where
  buckets : List Nat
  chains : List Nat
  deriving DecidableEq, Repr

/-- A version definition (`Elf64_Verdef` with its `Elf64_Verdaux` names, first the version's
own name, then its parents). -/
structure Verdef where
  version : Nat
  flags : Nat
  ndx : Nat
  hash : Nat
  names : List NameBytes
  deriving DecidableEq, Repr

/-- A version needed from a file (`Elf64_Vernaux`). -/
structure Vernaux where
  hash : Nat
  flags : Nat
  other : Nat
  name : NameBytes
  deriving DecidableEq, Repr

/-- The versions needed from one file (`Elf64_Verneed`). -/
structure Verneed where
  version : Nat
  file : NameBytes
  aux : List Vernaux
  deriving DecidableEq, Repr

/-- A note: its name (without the NUL), type and descriptor (by reference). -/
structure Note where
  name : NameBytes
  type : Nat
  desc : Span
  deriving DecidableEq, Repr

/-- **A section body**, typed by the section type (module doc). -/
inductive Body where
  | null
  | noBits
  | progbits (data : Span)
  | strtab (data : Span)
  | symbols (table : Table) (entries : List ObjectSymbol)
  | relas (entries : List Rela)
  | rels (entries : List Rel)
  | relr (words : List Nat)
  | dynamic (entries : List Dyn)
  | gnuHash (table : GnuHash)
  | hash (table : SysvHash)
  | versym (entries : List Nat)
  | verdef (entries : List Verdef)
  | verneed (entries : List Verneed)
  | notes (entries : List Note)
  | other (data : Span)
  deriving DecidableEq, Repr

/-- A section: its header, its name (from `.shstrtab`) and its typed body. -/
structure Section where
  header : SectionHeader
  name : NameBytes
  body : Body
  deriving DecidableEq, Repr

/-- **The metadata of an ELF64 little-endian file** (module doc). -/
structure File where
  header : Header
  phdrs : List ProgramHeader
  sections : List Section
  /-- The `PT_DYNAMIC` entries up to `DT_NULL` (the loader's view). -/
  dynamic : List Dyn
  /-- The `PT_INTERP` string. -/
  interp : Option NameBytes
  /-- The `DT_NEEDED` names, in order, from `DT_STRTAB`. -/
  needed : List NameBytes
  /-- `DT_SONAME`. -/
  soname : Option NameBytes
  /-- `DT_RUNPATH`, else `DT_RPATH`. -/
  runpath : Option NameBytes
  deriving DecidableEq, Repr

/-! ## Object kinds -/

/-- **What kind of object a file is.** -/
inductive Kind where
  /-- `ET_REL`: a relocatable object (`.o`; a member of a static archive). -/
  | relocatable
  /-- `ET_EXEC`: a fixed-address executable (static or dynamic). -/
  | exec
  /-- `ET_DYN` without `DF_1_PIE`: a shared object (`libc.so.6`, `libz.so.1`). -/
  | shared
  /-- `ET_DYN` with `DF_1_PIE` and `PT_INTERP`: a position-independent executable. -/
  | pie
  /-- `ET_DYN` with `DF_1_PIE` and no `PT_INTERP`: a static PIE (self-relocating). -/
  | staticPie
  /-- Any other `e_type` (`ET_CORE`, OS- or processor-specific). -/
  | other (etype : Nat)
  deriving DecidableEq, Repr

namespace File

/-- The value of the first loader-view dynamic entry with tag `t`. -/
def dynTag (A : File) (t : Nat) : Option Nat := (A.dynamic.find? (·.tag == t)).map (·.val)

/-- `DF_1_PIE` is set in `DT_FLAGS_1`. -/
def pieFlag (A : File) : Bool := ((A.dynTag DT_FLAGS_1).getD 0) / DF_1_PIE % 2 == 1

/-- **The kind of `A`** (`Kind`). An `ET_DYN` executable linked before `DF_1_PIE` existed
(binutils < 2.31) classifies as `shared`. -/
def kind (A : File) : Kind :=
  if A.header.fileType = ET_REL then .relocatable
  else if A.header.fileType = ET_EXEC then .exec
  else if A.header.fileType = ET_DYN then
    if A.pieFlag then (if A.interp.isSome then .pie else .staticPie) else .shared
  else .other A.header.fileType

/-- The `PT_LOAD` program headers. -/
def loads (A : File) : List ProgramHeader := A.phdrs.filter (·.kind == PT_LOAD)

/-- The file offset of virtual address `v`, through the first `PT_LOAD` mapping it from the file
(as `DynElf.Elf.vToOff`). -/
def vToOff (A : File) (v : Nat) : Option Nat :=
  (A.loads.find? fun ph => ph.virtualAddress ≤ v && v < ph.virtualAddress + ph.fileSize).map
    fun ph => v - ph.virtualAddress + ph.offset

/-- The first section whose body satisfies `p`, with its index. -/
def findSection (A : File) (p : Section → Bool) : Option (Nat × Section) :=
  (A.sections.zipIdx.find? fun (s, _) => p s).map fun (s, i) => (i, s)

/-- The section with header type `t` (the first one). -/
def sectionOfType (A : File) (t : Nat) : Option (Nat × Section) :=
  A.findSection (·.header.kind == t)

/-- The body of the first section of type `t`. -/
def bodyOf (A : File) (t : Nat) : Option Body := (A.sectionOfType t).map (·.2.body)

/-- **The entries of a symbol table** (`[]` if the file has none). -/
def symbols (A : File) (t : Table) : List ObjectSymbol :=
  match A.bodyOf t.shType with
  | some (Body.symbols _ es) => es
  | _ => []

/-- `.dynsym`. -/
def dynsyms (A : File) : List ObjectSymbol := A.symbols .dynsym

/-- The GNU hash table. -/
def gnuHashTab (A : File) : Option GnuHash :=
  match A.bodyOf SHT_GNU_HASH with
  | some (Body.gnuHash g) => some g
  | _ => none

/-- The version index of each `.dynsym` entry (`.gnu.version`). -/
def versyms (A : File) : Option (List Nat) :=
  match A.bodyOf SHT_GNU_versym with
  | some (Body.versym vs) => some vs
  | _ => none

/-- The version definitions (`.gnu.version_d`). -/
def verdefs (A : File) : List Verdef :=
  match A.bodyOf SHT_GNU_verdef with
  | some (Body.verdef ds) => ds
  | _ => []

/-- The version requirements (`.gnu.version_r`). -/
def verneeds (A : File) : List Verneed :=
  match A.bodyOf SHT_GNU_verneed with
  | some (Body.verneed ns) => ns
  | _ => []

/-- All notes, in section order. -/
def notes (A : File) : List Note :=
  A.sections.flatMap fun s => match s.body with
    | .notes ns => ns
    | _ => []

/-- **The code spans**: the payloads of the executable (`SHF_EXECINSTR`) `PROGBITS` sections,
which the metadata reader never reads (`Task.parse_frame`, `Silmaril.Elf.Facts`). -/
def codeSpans (A : File) : List Span :=
  A.sections.filterMap fun s => match s.body with
    | .progbits d => if s.header.flags / SHF_EXECINSTR % 2 = 1 then some d else none
    | _ => none

end File

end Silmaril.Elf

namespace Silmaril.Elf.Lit

/-- A name of `len` bytes given as one little-endian number (the form an emitter emits:
cheap to elaborate and to evaluate in the kernel). -/
def name (len v : Nat) : Silmaril.Formats.ELF.NameBytes :=
  (List.range len).map fun i => BitVec.ofNat 8 (v >>> (8 * i))

end Silmaril.Elf.Lit
