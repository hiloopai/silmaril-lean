module

public import Silmaril.Formats.ELF.Ast.Types

/-! Shared ELF concrete syntax and direct projections, without byte readers or
correspondence proofs. Resolved names remain producer annotations. -/
@[expose] public section
namespace Silmaril.Formats.ELF.Cst

inductive SectionBody where
  | raw (data : Bytes)
  | symbols (entries : List ObjectSymbol)
  | dynamicSymbols (entries : List ObjectSymbol)
  | relas (entries : List Rela)
  | noBits
  deriving DecidableEq, Repr

def SectionBody.bytes : SectionBody → Bytes
  | .raw data => data
  | .symbols entries | .dynamicSymbols entries =>
      (entries.flatMap fun entry => (Ast.Part.symbol 0 0 entry.raw).bytes.toList).toArray
  | .relas entries =>
      (entries.flatMap fun entry => (Ast.Part.rela 0 0 entry).bytes.toList).toArray
  | .noBits => #[]

def SectionBody.symbolEntries : SectionBody → List ObjectSymbol
  | .symbols entries => entries
  | _ => []

def SectionBody.relaEntries : SectionBody → List Rela
  | .relas entries => entries
  | _ => []

/-- Scalar-width obligations for structured payloads, separately from physical
layout checks. Serializing an unchecked field can truncate it. -/
def SectionBody.RecordsWellFormed : SectionBody → Prop
  | .symbols entries | .dynamicSymbols entries => ∀ entry ∈ entries, (Ast.Part.symbol 0 0 entry.raw).WellFormed
  | .relas entries => ∀ entry ∈ entries, (Ast.Part.rela 0 0 entry).WellFormed
  | _ => True

instance (body : SectionBody) : Decidable body.RecordsWellFormed := by
  cases body <;> unfold SectionBody.RecordsWellFormed <;> infer_instance

structure Section where
  header : SectionHeader
  /-- Resolved annotation; agreement with the string table is a separate claim. -/
  name : NameBytes
  body : SectionBody
  deriving DecidableEq, Repr

def Section.erase (part : Section) : ObjectSection :=
  { header := part.header, name := part.name, data := part.body.bytes }

/-- Resolve relocation metadata from the shared raw RELA and containing header. -/
def Section.relocations (part : Section) : List ObjectRelocation :=
  part.body.relaEntries.map fun entry =>
    { targetSection := part.header.info
      offset := entry.offset
      symbol := entry.symbolIndex
      kind := entry.relocationType
      addend := entry.addend }


inductive Part where
  | header (padding : Bytes)
  | sectionHeader (index : Nat)
  | programHeader (index : Nat)
  | sectionPayload (index : Nat)
  | raw (role : Ast.RawRole) (data : Bytes)
  deriving DecidableEq, Repr

structure Block where
  offset : Nat
  body : Part
  deriving DecidableEq, Repr

/-- Shared syntax for ELF64LE files with ordinary section/program headers.
Unsupported/ill-tagged constructors remain representable so validation is
explicit rather than built into a trusted producer. -/
structure File where
  header : Header
  sections : Array Section
  blocks : List Block
  programHeaders : Array ProgramHeader := #[]
  deriving DecidableEq, Repr

/-- Direct structural erasure. All symbol bodies are concatenated in section
order; the supported profile's separate validity obligation requires one table.
Resolved names are copied, not parsed or certified by this operation. -/
def File.erase (file : File) : ObjectFile :=
  { header := file.header
    sections := file.sections.toList.map Section.erase
    symbols := file.sections.toList.flatMap fun part => part.body.symbolEntries
    relocations := file.sections.toList.flatMap Section.relocations }

/-- Out-of-bounds physical references fail explicitly. Tags and annotations are
not checked here; this is reference resolution, not an ELF parser. -/
def File.resolvePart (file : File) : Part → Option Ast.Part
  | .header padding => some (.header file.header padding)
  | .sectionHeader index => do
      let part ← file.sections[index]?
      pure (.sectionHeader index part.header)
  | .programHeader index => do
      let header ← file.programHeaders[index]?
      pure (.programHeader index header)
  | .sectionPayload index => do
      let part ← file.sections[index]?
      pure (.raw (.sectionPayload index) part.body.bytes)
  | .raw role data => some (.raw role data)

def File.resolveBlock (file : File) (block : Block) : Option Ast.Block := do
  pure { offset := block.offset, body := ← file.resolvePart block.body }

/-- Physical syntax uses the same source records and payloads as `erase`.
No byte parser is invoked. -/
def File.layout (file : File) : Option Ast.File := do
  pure ⟨← file.blocks.mapM file.resolveBlock⟩

def File.bytes (file : File) : Option Bytes :=
  file.layout.map Ast.File.bytes

/-- Byte identity is independent of semantic/ELF validity. -/
def File.Lossless (file : File) (original : Bytes) : Prop :=
  file.bytes = some original


def File.LayoutWellFormed (file : File) : Prop :=
  ∃ layout, file.layout = some layout ∧ layout.WellFormed

/-- Range checks for shared typed records, without an ELF parser call. These do
not certify table tags, name annotations, links or physical placement. -/
def File.RecordsWellFormed (file : File) : Prop :=
  Ast.Fits 1 file.header.osABI ∧ Ast.Fits 1 file.header.abiVersion ∧
    Ast.fieldsFit (Ast.headerFields file.header) ∧
    (∀ part ∈ file.sections.toList,
      Ast.fieldsFit (Ast.sectionHeaderFields part.header) ∧ part.body.RecordsWellFormed) ∧
    ∀ header ∈ file.programHeaders.toList, Ast.fieldsFit (Ast.programHeaderFields header)

instance (file : File) : Decidable file.RecordsWellFormed := by
  unfold File.RecordsWellFormed Ast.Fits
  infer_instance


/-- A symbol table retains its source section and SHT_SYMTAB (2) or SHT_DYNSYM
(11) tag. Symbol indices are local to this table. -/
structure SymbolTable where
  sectionIndex : Nat
  kind : Nat
  entries : List ObjectSymbol
  deriving DecidableEq, Repr

/-- RELA metadata retains sh_link and sh_info. In a linked file r_offset is a
virtual address; targetSection = 0 does not name a section. -/
structure RelocationTable where
  sectionIndex : Nat
  symbolTable : Nat
  targetSection : Nat
  entries : List Rela
  deriving DecidableEq, Repr

/-- Semantic records for relocatable, executable and shared ELF files. Unlike
ObjectFile, this projection preserves program headers and table origins. No
loader, relocation or machine interpretation is imposed. -/
structure SemanticFile where
  header : Header
  programHeaders : List ProgramHeader
  sections : List ObjectSection
  symbolTables : List SymbolTable
  relocationTables : List RelocationTable
  deriving DecidableEq, Repr

/-- Direct projection; names and tags remain unchecked producer annotations. -/
def File.semantic (file : File) : SemanticFile :=
  { header := file.header
    programHeaders := file.programHeaders.toList
    sections := file.sections.toList.map Section.erase
    symbolTables := file.sections.toList.zipIdx |>.filterMap fun (part, index) =>
      match part.body with
      | .symbols entries => some ⟨index, part.header.kind, entries⟩
      | .dynamicSymbols entries => some ⟨index, part.header.kind, entries⟩
      | _ => none
    relocationTables := file.sections.toList.zipIdx |>.filterMap fun (part, index) =>
      match part.body with
      | .relas entries => some ⟨index, part.header.link, part.header.info, entries⟩
      | _ => none }

end Silmaril.Formats.ELF.Cst
