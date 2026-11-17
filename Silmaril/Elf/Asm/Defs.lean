module

public import Silmaril.Elf.Image.Defs
public import Silmaril.Elf.Like.Defs

/-! # Assembly functions: one object for what a compiler explorer shows, with what is proved about it kept apart (`Silmaril.Elf.Asm`)

An `AsmFunction` is one function of an ELF file as an assembly view shows it: a name, an
architecture, a code extent, the exact bytes, listing lines, and the symbols and relocations it
refers to. It is **data**: nothing about it is believed because it was written down. What is
believed is a set of separate propositions about it, each stated against the file's bytes:

| dimension | proposition | what it says |
|---|---|---|
| architecture | `ArchOf F f` | the file's `e_machine` and `e_ident[EI_OSABI]` are `f.arch`'s (the parse reads only ELF64 little-endian files) |
| bytes | `BytesAt F f` | `f.bytes` are the file bytes at `f.extent.fileOff`, mapped by program header `f.extent.segment` to `f.extent.vaddr`, all file-backed (no zero fill), and `f.extent.size` counts them |
| section bytes | `SectionBytesAt F f` | the same through section `f.extent.shndx` (`sh_addr`, `sh_offset`): the grounding of a relocatable object, which has no segments |
| executable code | `Silmaril.Elf.CodeAt F f.extent.vaddr f.bytes` | the API's code fact: the first read-only executable `PT_LOAD` holds them (`Image.codeAt_segBytes`) |
| symbol | `SymbolOf F f` | the symbol table entry `f.symbol` is a function named `f.name` with value `f.extent.vaddr` and size `f.extent.size` |
| decoding | `DecodesAs isa f d` | the instruction model `isa`, for `f.arch.machine`, decodes `f.bytes` exactly into `d`, back to back |
| listing boundaries | `LinesTile f` | the listing lines' byte ranges tile `f.bytes` (the line *text* is never read) |
| references | `RefsGrounded F f isa d` | each reference that claims to come from a relocation is that relocation of the file (offset, type, addend, symbol name); each decoded one is the target of the decoded branch |

None of these implies another: the bytes can be grounded with no instruction model for the
machine (`Isa` is a parameter; a file for an unmodelled `e_machine` decodes, is grounded, and has
no `DecodesAs`), a semantic contract about the bytes says nothing about any decoder (contracts
are stated by the machine models, `Silmaril.X86.FnContract`), and the ABI is not here at all:
`abiRef` is a display or reference identifier, metadata that no proposition reads.

## Presentation is not decoding

`Line.text` is a string a disassembler printed (`objdump -d`, a compiler's `-S` output). No
proposition reads it: `LinesTile` reads only the lines' byte ranges, and every evidence
proposition is invariant under replacing the lines (`Thms.bytesAt_withLines`, …). Decoded
instructions are a separate value, `d : List (Nat × isa.Instr)`, checked by `decodes`, so a
display listing cannot become a trusted decoding by construction. References with
`RefOrigin.display` are likewise unverified annotations.

## Addresses

`Extent.vaddr` is a virtual address of the link-time image (a section offset for `ET_REL`),
`Extent.fileOff` a file offset; the two are related only through a program header
(`Image.MapsFile`). A load address is `Image.loadAddr base vaddr` for a base `Placement` admits;
memory at load addresses equals the file bytes only where no relocation writes
(`Image.Untouched`). `fileOff`, `segment` and `shndx` are `Option`: unknown is `none`, not `0`.
-/

@[expose] public section

namespace Silmaril.Elf.Asm

open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.X86.Link (Blob)

abbrev Byte := BitVec 8

/-! ## The object -/

/-- **Architecture identity**, as the ELF header states it. -/
structure Arch where
  /-- `e_machine` (`EM_X86_64 = 62`, …); any value, modelled or not. -/
  machine : Nat
  /-- `e_ident[EI_CLASS]` (`2`: ELFCLASS64). -/
  cls : Nat := 2
  /-- `e_ident[EI_DATA]` (`1`: little-endian). -/
  data : Nat := 1
  /-- `e_ident[EI_OSABI]`. -/
  osABI : Nat := 0
  deriving DecidableEq, Repr

/-- x86-64, ELF64 little-endian, System V OS ABI byte. -/
def Arch.x86_64 : Arch := ⟨EM_X86_64, 2, 1, 0⟩

/-- **The code extent**: where the function is, in each address space. -/
structure Extent where
  /-- Virtual address of the first byte (a section offset for `ET_REL`). -/
  vaddr : Nat
  /-- Number of bytes. -/
  size : Nat
  /-- File offset of the first byte, when known and file-backed. -/
  fileOff : Option Nat := none
  /-- Index of the program header that maps it, when known. -/
  segment : Option Nat := none
  /-- Index of the section that holds it, when known. -/
  shndx : Option Nat := none
  deriving DecidableEq, Repr

/-- An entry of a symbol table. -/
structure SymRef where
  table : Table
  index : Nat
  deriving DecidableEq, Repr

/-- Where a reference comes from. -/
inductive RefOrigin where
  /-- Relocation `index` of the selector `sel` (`File.relocs`). -/
  | reloc (sel : File.RelocSel) (index : Nat)
  /-- The target of a decoded direct branch or call (`Isa.target`). -/
  | decoded
  /-- Named only by the listing: an unverified annotation. -/
  | display
  deriving DecidableEq, Repr

/-- A reference from the function's bytes to an address or a symbol. -/
structure CodeRef where
  /-- Offset in the function's bytes of the referencing instruction (or relocated field). -/
  off : Nat
  /-- The target virtual address, when known. -/
  target : Option Nat := none
  /-- The target symbol's name, when known. -/
  symbol : Option String := none
  /-- The relocation type (`r_type`), `0` when not a relocation. -/
  kind : Nat := 0
  addend : Int := 0
  origin : RefOrigin
  deriving DecidableEq, Repr

/-- **A listing line**: a byte range of the function and the text a disassembler printed for it.
Display only. -/
structure Line where
  off : Nat
  len : Nat
  text : String
  label : Option String := none
  deriving DecidableEq, Repr

/-- **An assembly function** (module doc): data, believed only through the evidence below. -/
structure AsmFunction where
  name : String
  arch : Arch
  /-- A display or reference identifier for the calling convention (`"sysv64"`, …).
  Metadata: no proposition reads it. -/
  abiRef : Option String := none
  extent : Extent
  symbol : Option SymRef := none
  bytes : List Byte
  lines : List Line := []
  refs : List CodeRef := []
  deriving DecidableEq, Repr

/-- The same function with other listing lines. -/
def AsmFunction.withLines (f : AsmFunction) (ls : List Line) : AsmFunction := { f with lines := ls }

/-! ## Evidence -/

/-- **The file is for `f.arch`.** -/
def ArchOf (F : Blob) (f : AsmFunction) : Prop :=
  ∃ A, Parses F A ∧ A.header.machine = f.arch.machine ∧ A.header.osABI = f.arch.osABI ∧
    f.arch.cls = 2 ∧ f.arch.data = 1

/-- **`f.bytes` are file bytes mapped to `f.extent.vaddr`** by program header `f.extent.segment`
from offset `f.extent.fileOff`, and `f.extent.size` counts them. -/
def BytesAt (F : Blob) (f : AsmFunction) : Prop :=
  f.extent.size = f.bytes.length ∧ ∃ A i o, Parses F A ∧ f.extent.segment = some i ∧
    f.extent.fileOff = some o ∧ Image.SegBytes F A i f.extent.vaddr o f.bytes

/-- **`f.bytes` are file bytes of section `f.extent.shndx`** at `f.extent.vaddr` (a section offset
for `ET_REL`), from offset `f.extent.fileOff`, and `f.extent.size` counts them. The byte grounding
of a relocatable object, which has no segments; for a linked file it complements `BytesAt`. -/
def SectionBytesAt (F : Blob) (f : AsmFunction) : Prop :=
  f.extent.size = f.bytes.length ∧ ∃ A k o, Parses F A ∧ f.extent.shndx = some k ∧
    f.extent.fileOff = some o ∧ Image.SecBytes F A k f.extent.vaddr o f.bytes

/-- The symbol table a relocation selector's symbol indices refer to (by the usual linking:
`.dynsym` for the dynamic relocations, `.symtab` for a section's static ones). -/
def selTable : File.RelocSel → Table
  | .dynamic => .dynsym
  | .forSection _ => .symtab

/-- **The symbol table entry `f.symbol` is the function `f.name` at `f.extent`** (`STT_FUNC` or
`STT_GNU_IFUNC`). The name is compared as `nameOf f.name`, one byte per character, so it is exact
for ASCII names. -/
def SymbolOf (F : Blob) (f : AsmFunction) : Prop :=
  ∃ r s, f.symbol = some r ∧ SymbolAt F r.table r.index s ∧ s.name = nameOf f.name ∧
    s.raw.value = f.extent.vaddr ∧ s.raw.size = f.extent.size ∧ (s.kind = 2 ∨ s.kind = 10)

/-- The lines' byte ranges tile `[o, o + n)`, in order, each nonempty. -/
def tiles : Nat → List Line → Nat → Bool
  | o, [], n => o == n
  | o, l :: ls, n => l.off == o && decide (0 < l.len) && tiles (o + l.len) ls n

/-- **The listing lines tile the bytes.** Their text is not read. -/
def LinesTile (f : AsmFunction) : Prop := tiles 0 f.lines f.bytes.length = true

instance (f : AsmFunction) : Decidable (LinesTile f) := inferInstanceAs (Decidable (_ = true))

/-- **An instruction model**: a decoder for one `e_machine`, with the direct-branch targets it
knows. -/
structure Isa where
  /-- A stable name for the model (`x86-64/Silmaril.X86.Ext`, …). -/
  name : String
  /-- The `e_machine` it decodes. -/
  machine : Nat
  Instr : Type
  decEq : DecidableEq Instr
  /-- One instruction from the start of the bytes, with the number of bytes it takes. -/
  decode : List Byte → Option (Instr × Nat)
  /-- The target of a direct branch or call `i` at address `pc`, `len` bytes long. -/
  target : Instr → Nat → Nat → Option Nat := fun _ _ _ => none
  /-- A rendering of a decoded instruction (for display of the decoding; not evidence). -/
  render : Instr → String := fun _ => ""

instance (isa : Isa) : DecidableEq isa.Instr := isa.decEq

/-- **`isa` decodes `bs` exactly into `d`** (instruction lengths and instructions), back to back. -/
def decodes (isa : Isa) : List Byte → List (Nat × isa.Instr) → Bool
  | [], [] => true
  | bs, (n, i) :: d =>
    decide (0 < n) && decide (n ≤ bs.length) &&
      (match isa.decode bs with
        | some (i', n') => decide (n' = n) && @decide (i' = i) (isa.decEq i' i)
        | none => false) &&
      decodes isa (bs.drop n) d
  | _ :: _, [] => false

/-- Decode greedily with at most `fuel` instructions. -/
def decodeAllF (isa : Isa) : Nat → List Byte → Option (List (Nat × isa.Instr))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bs@(_ :: _) =>
    match isa.decode bs with
    | some (i, n) =>
      if 0 < n ∧ n ≤ bs.length then (decodeAllF isa fuel (bs.drop n)).map ((n, i) :: ·) else none
    | none => none

/-- **The decoding of `bs` by `isa`, if every instruction decodes** (`Thms.decodes_iff_decodeAll`:
it is the only `d` with `decodes isa bs d`). -/
def decodeAll (isa : Isa) (bs : List Byte) : Option (List (Nat × isa.Instr)) :=
  decodeAllF isa bs.length bs

/-- **The instruction model `isa`, for `f`'s machine, decodes `f.bytes` into `d`.** -/
def DecodesAs (isa : Isa) (f : AsmFunction) (d : List (Nat × isa.Instr)) : Prop :=
  isa.machine = f.arch.machine ∧ decodes isa f.bytes d = true

/-- The instruction of a decoding that starts at offset `off`, with its length. -/
def insnAt {isa : Isa} : List (Nat × isa.Instr) → Nat → Nat → Option (Nat × isa.Instr)
  | [], _, _ => none
  | (n, i) :: d, o, off => if o = off then some (n, i) else insnAt d (o + n) off

/-- **A reference is grounded.** From a relocation: the file's relocation is at the referencing
field with that type and addend, and its symbol (in `selTable sel`) is `r.symbol` when that is given
(a `REL` entry has no addend field; its addend is in the
relocated bytes, and `r.addend` must then be `0`). From a decoding: the instruction at `r.off` is a direct branch or
call to `r.target`. A display reference is never grounded. -/
def RefGrounded (F : Blob) (f : AsmFunction) (isa : Isa) (d : List (Nat × isa.Instr)) (r : CodeRef) :
    Prop :=
  match r.origin with
  | .reloc sel k => ∃ A rel, Parses F A ∧ (A.relocs sel)[k]? = some rel ∧
      rel.offset = f.extent.vaddr + r.off ∧ rel.kind = r.kind ∧ rel.addend.getD 0 = r.addend ∧
      ∀ n, r.symbol = some n →
        ((A.symbols (selTable sel))[rel.symbol]?).map (·.name) = some (nameOf n)
  | .decoded => DecodesAs isa f d ∧ ∃ n i, insnAt d 0 r.off = some (n, i) ∧
      r.target.isSome ∧ isa.target i (f.extent.vaddr + r.off) n = r.target
  | .display => False

/-- The check of a decoded reference against a decoding `d` (`Thms.refGrounded_of_check`). -/
def decodedRefOk (f : AsmFunction) (isa : Isa) (d : List (Nat × isa.Instr)) (r : CodeRef) : Bool :=
  match insnAt d 0 r.off with
  | some (n, i) => r.target.isSome && isa.target i (f.extent.vaddr + r.off) n == r.target
  | none => false

/-- **Every non-display reference of `f` is grounded** (against the decoding `d` by `isa`). -/
def RefsGrounded (F : Blob) (f : AsmFunction) (isa : Isa) (d : List (Nat × isa.Instr)) : Prop :=
  ∀ r ∈ f.refs, r.origin ≠ .display → RefGrounded F f isa d r

/-! ## Checks on a parse

Boolean checks of the metadata parts of the evidence against a parse `A` (no byte of code is
read); `Thms` turns each into its proposition (`archOf_of_check`, `symbolOf_of_check`,
`bytesAt_of_check`, which also takes one read of the bytes). -/

/-- The header names `f.arch`. -/
def archOk (A : File) (f : AsmFunction) : Bool :=
  A.header.machine == f.arch.machine && A.header.osABI == f.arch.osABI && f.arch.cls == 2 &&
    f.arch.data == 1

/-- `ph` is a `PT_LOAD` mapping the `len` bytes at `v` from the file at offset `o`. -/
def mapsOk (ph : Silmaril.Formats.ELF.ProgramHeader) (v len o : Nat) : Bool :=
  ph.kind == PT_LOAD && decide (ph.virtualAddress ≤ v) &&
    decide (v + len ≤ ph.virtualAddress + ph.fileSize) && o == ph.offset + (v - ph.virtualAddress)

/-- The extent's size counts the bytes, and its segment maps them from its file offset. -/
def extentOk (A : File) (f : AsmFunction) : Bool :=
  f.extent.size == f.bytes.length &&
    match f.extent.segment, f.extent.fileOff with
    | some i, some o =>
      match A.phdrs[i]? with
      | some ph => mapsOk ph f.extent.vaddr f.bytes.length o
      | none => false
    | _, _ => false

/-- Section `f.extent.shndx` holds the bytes at `f.extent.vaddr` from `f.extent.fileOff`. -/
def secOk (A : File) (f : AsmFunction) : Bool :=
  f.extent.size == f.bytes.length &&
    match f.extent.shndx, f.extent.fileOff with
    | some k, some o =>
      match A.sections[k]? with
      | some s => s.header.kind != SHT_NOBITS && decide (s.header.address ≤ f.extent.vaddr) &&
          decide (f.extent.vaddr + f.bytes.length ≤ s.header.address + s.header.size) &&
          o == s.header.offset + (f.extent.vaddr - s.header.address)
      | none => false
    | _, _ => false

/-- The check of a relocation reference `r` (origin `.reloc sel k`) against a parse. -/
def relocRefOk (A : File) (f : AsmFunction) (r : CodeRef) : Bool :=
  match r.origin with
  | .reloc sel k =>
    match (A.relocs sel)[k]? with
    | some rel => rel.offset == f.extent.vaddr + r.off && rel.kind == r.kind &&
        rel.addend.getD 0 == r.addend &&
        (match r.symbol with
          | some n => ((A.symbols (selTable sel))[rel.symbol]?).map (·.name) == some (nameOf n)
          | none => true)
    | none => false
  | _ => false

/-- The symbol table entry `f.symbol` is the function `f.name` at `f.extent`. -/
def symbolOk (A : File) (f : AsmFunction) : Bool :=
  match f.symbol with
  | some r =>
    match (A.symbols r.table)[r.index]? with
    | some s => s.name == nameOf f.name && s.raw.value == f.extent.vaddr &&
        s.raw.size == f.extent.size && (s.kind == 2 || s.kind == 10)
    | none => false
  | none => false

end Silmaril.Elf.Asm
