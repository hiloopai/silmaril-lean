module

public import Silmaril.Formats.ELF.Object

/-! Compositional certificates for the checked relocatable-object parser.

Separately certified parser stages can be assembled without repeatedly reducing
the original byte image through every parser continuation.
-/

@[expose] public section

namespace Silmaril.Formats.ELF

/-- Assemble independently checked headers, names, sections, symbols and relocations. -/
theorem readObject_of_parts
    (bytes : Bytes) (header : Header) (headers : List SectionHeader)
    (null names : SectionHeader) (strings : Bytes) (sections : List ObjectSection)
    (symbolTable : Nat) (symbols : List ObjectSymbol) (relocations : List ObjectRelocation)
    (header_read : readHeader bytes = some header)
    (header_profile : header.fileType = 1 ∧ header.version = 1 ∧
      header.entry = 0 ∧ header.programCount = 0)
    (header_size : header.headerSize = 64)
    (headers_read : readSectionHeaders bytes header = some headers)
    (headers_nonempty : 0 < headers.length)
    (null_at : headers[0]? = some null)
    (null_valid : null.kind = 0 ∧ null.size = 0)
    (names_at : headers[header.sectionNameIndex]? = some names)
    (names_kind : names.kind = 3)
    (strings_read : sectionData bytes names = some strings)
    (sections_read : readObjectSections bytes headers strings = some sections)
    (table_unique : (List.range sections.length).filter (fun index =>
      (sections[index]?.map (fun part => part.header.kind)) == some 2) = [symbolTable])
    (symbols_read : readObjectSymbols bytes sections symbolTable = some symbols)
    (relocations_read : readObjectRelocations bytes sections symbolTable symbols.length =
      some relocations) :
    readObject bytes = some ⟨header, sections, symbols, relocations⟩ := by
  have null_get : headers[0]'headers_nonempty = null := by
    simpa only [List.getElem?_eq_getElem headers_nonempty, Option.some.injEq] using null_at
  simp [readObject, header_read, header_profile, header_size, headers_read,
    headers_nonempty, null_get, null_valid, names_at, names_kind, strings_read,
    sections_read, table_unique, symbols_read, relocations_read]

end Silmaril.Formats.ELF
