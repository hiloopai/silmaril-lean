module

public import Silmaril.Formats.ELF.Reader
public import Silmaril.Formats.ELF.Object.Types

/-! # A checked ELF64 little-endian relocatable-object profile

This layer preserves machine identifiers and relocation kinds as data. It does
not interpret an ISA or apply relocations. Names are byte strings, so decoding
does not assume UTF-8. Reads, string termination, section extents, symbol-table
links, and explicit-addend relocation tables are checked with total operations.
Extended section numbering, implicit-addend relocations, and multiple symbol
tables are outside this initial profile.
-/

@[expose] public section

namespace Silmaril.Formats.ELF

/-- A NUL-terminated byte string, entirely within its declared string table. -/
def readName (table : Bytes) (offset : Nat) : Option NameBytes := do
  guard (offset < table.size)
  let remaining := table.toList.drop offset
  let name := remaining.takeWhile (fun byte => byte != 0)
  guard (name.length < remaining.length)
  pure name

/-- File bytes for an ordinary section, or the empty prefix for NOBITS. -/
def sectionData (bytes : Bytes) (part : SectionHeader) : Option Bytes := do
  if part.kind = 8 then
    pure #[]
  else do
    guard (part.offset + part.size ≤ bytes.size)
    pure ⟨(bytes.toList.drop part.offset).take part.size⟩

/-- Section alignment is absent, unit, or a power of two. -/
def validSectionAlignment (alignment : Nat) : Bool :=
  alignment ≤ 1 || (alignment &&& (alignment - 1)) == 0

def readObjectSections (bytes : Bytes) (headers : List SectionHeader)
    (strings : Bytes) : Option (List ObjectSection) :=
  headers.mapM fun header => do
    guard (validSectionAlignment header.alignment)
    let name ← readName strings header.name
    let data ← sectionData bytes header
    pure { header, name, data }

def readObjectSymbols (bytes : Bytes) (sections : List ObjectSection)
    (tableIndex : Nat) : Option (List ObjectSymbol) := do
  let table ← sections[tableIndex]?
  guard (table.header.kind = 2 ∧ table.header.entrySize = 24)
  guard (table.header.size % 24 = 0 ∧ 24 ≤ table.header.size)
  let strings ← sections[table.header.link]?
  guard (strings.header.kind = 3)
  (List.range (table.header.size / 24)).mapM fun index => do
    let raw ← readSymbol bytes (table.header.offset + 24 * index)
    let name ← readName strings.data raw.name
    guard (raw.sectionIndex < sections.length ∨ 0xff00 ≤ raw.sectionIndex)
    pure { raw, name }

def readObjectRelocations (bytes : Bytes) (sections : List ObjectSection)
    (symbolTable symbolCount : Nat) : Option (List ObjectRelocation) := do
  let tables : List (List ObjectRelocation) ← sections.mapM fun table => do
    if table.header.kind = 4 then
      guard (table.header.link = symbolTable ∧ table.header.entrySize = 24)
      guard (table.header.size % 24 = 0)
      let target ← sections[table.header.info]?
      (List.range (table.header.size / 24)).mapM fun index => do
        let relocation ← readRela bytes (table.header.offset + 24 * index)
        guard (relocation.symbolIndex < symbolCount)
        guard (relocation.offset < target.header.size)
        pure { targetSection := table.header.info
               offset := relocation.offset
               symbol := relocation.symbolIndex
               kind := relocation.relocationType
               addend := relocation.addend }
    else do
      guard (table.header.kind ≠ 9 ∧ table.header.kind ≠ 18)
      pure []
  pure tables.flatten

/-- Parse a relocatable file without accepting or interpreting any ISA's relocation rules. -/
def readObject (bytes : Bytes) : Option ObjectFile := do
  let header ← readHeader bytes
  guard (header.fileType = 1 ∧ header.version = 1 ∧ header.entry = 0 ∧ header.programCount = 0)
  guard (header.headerSize = 64)
  let headers ← readSectionHeaders bytes header
  guard (0 < headers.length)
  let null ← headers[0]?
  guard (null.kind = 0 ∧ null.size = 0)
  let names ← headers[header.sectionNameIndex]?
  guard (names.kind = 3)
  let strings ← sectionData bytes names
  let sections ← readObjectSections bytes headers strings
  let symbolTables := (List.range sections.length).filter fun index =>
    (sections[index]?.map (fun part => part.header.kind)) == some 2
  let [symbolTable] := symbolTables | none
  let symbols ← readObjectSymbols bytes sections symbolTable
  let relocations ← readObjectRelocations bytes sections symbolTable symbols.length
  pure { header, sections, symbols, relocations }

/-- Unsupported object-format versions are rejected before any section is interpreted. -/
theorem readObject_invalidVersion {bytes : Bytes} {header : Header}
    (header_read : readHeader bytes = some header) (invalid : header.version ≠ 1) :
    readObject bytes = none := by
  simp [readObject, header_read, invalid]

/-- A missing NUL terminator is a parse failure, not an unbounded string walk. -/
example : readName #[65, 66] 0 = none := by decide
example : readName #[65, 0, 66] 0 = some [65] := by decide
example : readName #[0] 1 = none := by decide

end Silmaril.Formats.ELF
