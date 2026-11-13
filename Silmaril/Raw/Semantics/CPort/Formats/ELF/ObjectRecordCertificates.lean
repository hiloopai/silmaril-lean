module
public import Silmaril.Formats.ELF.Object

/-! Bounded ELF64 record certificates and symbolic object-parser composition.

These lemmas depend only on generic ELF records and byte windows. An ISA-specific
artifact can check each small record separately, then compose the resulting
certificates without reducing its full byte image through parser continuations.
-/

@[expose] public section
namespace Silmaril.Formats.ELF

/-- Compose opaque per-record certificates without evaluating their readers. -/
theorem mapM_record_certificates {α β : Type} (reader : α → Option β)
    {inputs : List α} {outputs : List β}
    (records : List.Forall₂ (fun input output => reader input = some output) inputs outputs) :
    inputs.mapM reader = some outputs := by
  induction records with
  | nil => rfl
  | cons first _ ih => simp only [List.mapM_cons, first, ih, bind, Option.bind, pure]

/-- Assemble a checked section-header table from independently proved record reads. -/
theorem readSectionHeaders_of_records (bytes : Bytes) (header : Header) (headers : List SectionHeader)
    (numbering : header.sectionCount < 0xff00 ∧ header.sectionNameIndex < 0xff00)
    (nonempty : header.sectionCount ≠ 0)
    (layout : header.sectionEntrySize = 64 ∧ 64 ≤ header.sectionOffset)
    (names : header.sectionNameIndex < header.sectionCount)
    (bounded : header.sectionOffset + 64 * header.sectionCount ≤ bytes.size)
    (records : List.Forall₂ (fun i r => readSectionHeader bytes (header.sectionOffset + 64 * i) = some r)
      (List.range header.sectionCount) headers) : readSectionHeaders bytes header = some headers := by
  have table := mapM_record_certificates _ records
  simpa [readSectionHeaders, readTable, numbering, nonempty, layout, names, bounded] using table

/-- A bounded little-endian read depends only on the bytes in its requested window. -/
theorem readLE_congr (first second : Bytes) (start other width : Nat)
    (same : ∀ index, index < width → first.toList[start + index]? = second.toList[other + index]?) :
    readLE first start width = readLE second other width := by
  induction width generalizing start other with
  | zero => rfl
  | succ width ih =>
    simp only [readLE]
    rw [show first.toList[start]? = second.toList[other]? from by simpa using same 0 (by omega)]
    rw [ih (start + 1) (other + 1) (by
      intro index bound
      simpa only [Nat.add_assoc, Nat.add_comm 1] using same (index + 1) (by omega))]

/-- Remove an arbitrary prefix and suffix when the complete read fits in the retained window. -/
theorem readLE_window (before chunk suffix : List (BitVec 8)) (offset width : Nat)
    (bound : offset + width ≤ chunk.length) :
    readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + offset) width = readLE ⟨chunk⟩ offset width := by
  apply readLE_congr
  intro index inside
  change (before ++ (chunk ++ suffix))[before.length + offset + index]? = chunk[offset + index]?
  rw [Nat.add_assoc]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by omega)]

/-- A section-header certificate needs only its 64-byte record, independently of the surrounding file. -/
theorem readSectionHeader_window (before chunk suffix : List (BitVec 8))
    (bound : 64 ≤ chunk.length) :
    readSectionHeader ⟨before ++ (chunk ++ suffix)⟩ before.length = readSectionHeader ⟨chunk⟩ 0 := by
  have part (offset size : Nat) (inside : offset + size ≤ 64) :=
    readLE_window before chunk suffix offset size (Nat.le_trans inside bound)
  simpa only [readSectionHeader, Nat.add_zero, Nat.zero_add] using
    (show readSectionHeader ⟨before ++ (chunk ++ suffix)⟩ (before.length + 0) = readSectionHeader ⟨chunk⟩ 0 by
      simp only [readSectionHeader, Nat.add_zero, Nat.zero_add]
      rw [(show readLE ⟨before ++ (chunk ++ suffix)⟩ before.length 4 = readLE ⟨chunk⟩ 0 4 from by simpa only [Nat.add_zero] using part 0 4 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 4) 4 = readLE ⟨chunk⟩ 4 4 from by simpa only [Nat.add_zero] using part 4 4 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 8) 8 = readLE ⟨chunk⟩ 8 8 from by simpa only [Nat.add_zero] using part 8 8 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 16) 8 = readLE ⟨chunk⟩ 16 8 from by simpa only [Nat.add_zero] using part 16 8 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 24) 8 = readLE ⟨chunk⟩ 24 8 from by simpa only [Nat.add_zero] using part 24 8 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 32) 8 = readLE ⟨chunk⟩ 32 8 from by simpa only [Nat.add_zero] using part 32 8 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 40) 4 = readLE ⟨chunk⟩ 40 4 from by simpa only [Nat.add_zero] using part 40 4 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 44) 4 = readLE ⟨chunk⟩ 44 4 from by simpa only [Nat.add_zero] using part 44 4 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 48) 8 = readLE ⟨chunk⟩ 48 8 from by simpa only [Nat.add_zero] using part 48 8 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 56) 8 = readLE ⟨chunk⟩ 56 8 from by simpa only [Nat.add_zero] using part 56 8 (by decide))])

/-- A symbol certificate needs only its 24-byte record, independently of the surrounding file. -/
theorem readSymbol_window (before chunk suffix : List (BitVec 8))
    (bound : 24 ≤ chunk.length) :
    readSymbol ⟨before ++ (chunk ++ suffix)⟩ before.length = readSymbol ⟨chunk⟩ 0 := by
  have part (offset size : Nat) (inside : offset + size ≤ 24) :=
    readLE_window before chunk suffix offset size (Nat.le_trans inside bound)
  simpa only [readSymbol, Nat.add_zero, Nat.zero_add] using
    (show readSymbol ⟨before ++ (chunk ++ suffix)⟩ (before.length + 0) = readSymbol ⟨chunk⟩ 0 by
      simp only [readSymbol, Nat.add_zero, Nat.zero_add]
      rw [(show readLE ⟨before ++ (chunk ++ suffix)⟩ before.length 4 = readLE ⟨chunk⟩ 0 4 from by simpa only [Nat.add_zero] using part 0 4 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 4) 1 = readLE ⟨chunk⟩ 4 1 from by simpa only [Nat.add_zero] using part 4 1 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 5) 1 = readLE ⟨chunk⟩ 5 1 from by simpa only [Nat.add_zero] using part 5 1 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 6) 2 = readLE ⟨chunk⟩ 6 2 from by simpa only [Nat.add_zero] using part 6 2 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 8) 8 = readLE ⟨chunk⟩ 8 8 from by simpa only [Nat.add_zero] using part 8 8 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 16) 8 = readLE ⟨chunk⟩ 16 8 from by simpa only [Nat.add_zero] using part 16 8 (by decide))])

/-- An explicit-addend relocation certificate needs only its 24-byte record. -/
theorem readRela_window (before chunk suffix : List (BitVec 8))
    (bound : 24 ≤ chunk.length) :
    readRela ⟨before ++ (chunk ++ suffix)⟩ before.length = readRela ⟨chunk⟩ 0 := by
  have part (offset size : Nat) (inside : offset + size ≤ 24) :=
    readLE_window before chunk suffix offset size (Nat.le_trans inside bound)
  simpa only [readRela, Nat.add_zero, Nat.zero_add] using
    (show readRela ⟨before ++ (chunk ++ suffix)⟩ (before.length + 0) = readRela ⟨chunk⟩ 0 by
      simp only [readRela, Nat.add_zero, Nat.zero_add]
      rw [(show readLE ⟨before ++ (chunk ++ suffix)⟩ before.length 8 = readLE ⟨chunk⟩ 0 8 from by simpa only [Nat.add_zero] using part 0 8 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 8) 8 = readLE ⟨chunk⟩ 8 8 from by simpa only [Nat.add_zero] using part 8 8 (by decide)),
        (show readLE ⟨before ++ (chunk ++ suffix)⟩ (before.length + 16) 8 = readLE ⟨chunk⟩ 16 8 from by simpa only [Nat.add_zero] using part 16 8 (by decide))])

/-- A symbol record is assembled from an opaque raw-read equality and checks
which mention only its small literal metadata and string table. -/
theorem objectSymbol_of_raw (bytes strings : Bytes) (sectionCount offset : Nat)
    (symbol : ObjectSymbol) (raw : readSymbol bytes offset = some symbol.raw)
    (name : readName strings symbol.raw.name = some symbol.name)
    (valid : symbol.raw.sectionIndex < sectionCount ∨ 0xff00 ≤ symbol.raw.sectionIndex) :
    (do
      let record ← readSymbol bytes offset
      let name ← readName strings record.name
      guard (record.sectionIndex < sectionCount ∨ 0xff00 ≤ record.sectionIndex)
      pure ({raw := record, name := name} : ObjectSymbol)) = some symbol := by
  simp [raw, name, guard, valid]

/-- Opaque symbol reads suffice to certify the complete table parser. -/
theorem readObjectSymbols_of_records (bytes : Bytes) (sections : List ObjectSection)
    (tableIndex : Nat) (table strings : ObjectSection) (symbols : List ObjectSymbol)
    (tableFound : sections[tableIndex]? = some table)
    (tableMeta : table.header.kind = 2 ∧ table.header.entrySize = 24)
    (tableSize : table.header.size % 24 = 0 ∧ 24 ≤ table.header.size)
    (stringsFound : sections[table.header.link]? = some strings)
    (stringsMeta : strings.header.kind = 3)
    (records : List.Forall₂ (fun index symbol =>
      (do
        let raw ← readSymbol bytes (table.header.offset + 24 * index)
        let name ← readName strings.data raw.name
        guard (raw.sectionIndex < sections.length ∨ 0xff00 ≤ raw.sectionIndex)
        pure ({raw, name} : ObjectSymbol)) = some symbol)
      (List.range (table.header.size / 24)) symbols) :
    readObjectSymbols bytes sections tableIndex = some symbols := by
  simpa [readObjectSymbols, tableFound, tableMeta, tableSize, stringsFound, stringsMeta, guard]
    using mapM_record_certificates _ records

/-- One explicit-addend relocation is checked without reducing its byte reader. -/
theorem objectRelocation_of_raw (bytes : Bytes) (offset targetSection targetSize symbolCount : Nat)
    (raw : Rela) (read : readRela bytes offset = some raw)
    (symbol : raw.symbolIndex < symbolCount) (inside : raw.offset < targetSize) :
    (do
      let relocation ← readRela bytes offset
      guard (relocation.symbolIndex < symbolCount)
      guard (relocation.offset < targetSize)
      pure ({targetSection, offset := relocation.offset, symbol := relocation.symbolIndex, kind := relocation.relocationType, addend := relocation.addend} : ObjectRelocation)) =
    some {targetSection, offset := raw.offset, symbol := raw.symbolIndex, kind := raw.relocationType, addend := raw.addend} := by
  rw [read]
  simp [guard, symbol, inside]

/-- The relocation-table stage is assembled from exact record certificates. -/
theorem relocationTable_of_records (bytes : Bytes) (sections : List ObjectSection)
    (symbolTable symbolCount : Nat) (table target : ObjectSection)
    (relocations : List ObjectRelocation) (kind : table.header.kind = 4)
    (metadata : table.header.link = symbolTable ∧ table.header.entrySize = 24)
    (size : table.header.size % 24 = 0)
    (targetFound : sections[table.header.info]? = some target)
    (records : List.Forall₂ (fun index relocation =>
      (do
        let raw ← readRela bytes (table.header.offset + 24 * index)
        guard (raw.symbolIndex < symbolCount)
        guard (raw.offset < target.header.size)
        pure ({targetSection := table.header.info, offset := raw.offset, symbol := raw.symbolIndex, kind := raw.relocationType, addend := raw.addend} : ObjectRelocation)) = some relocation)
      (List.range (table.header.size / 24)) relocations) :
    (do
      if table.header.kind = 4 then
        guard (table.header.link = symbolTable ∧ table.header.entrySize = 24)
        guard (table.header.size % 24 = 0)
        let target ← sections[table.header.info]?
        (List.range (table.header.size / 24)).mapM fun index => do
          let relocation ← readRela bytes (table.header.offset + 24 * index)
          guard (relocation.symbolIndex < symbolCount)
          guard (relocation.offset < target.header.size)
          pure ({targetSection := table.header.info, offset := relocation.offset, symbol := relocation.symbolIndex, kind := relocation.relocationType, addend := relocation.addend} : ObjectRelocation)
      else do
        guard (table.header.kind ≠ 9 ∧ table.header.kind ≠ 18)
        pure []) = some relocations := by
  simpa [kind, metadata, size, targetFound, guard] using mapM_record_certificates _ records

/-- Non-relocation sections contribute no relocations, with REL/RELR rejected. -/
theorem relocationTable_empty (bytes : Bytes) (sections : List ObjectSection)
    (symbolTable symbolCount : Nat) (table : ObjectSection)
    (ordinary : table.header.kind ≠ 4) (supported : table.header.kind ≠ 9 ∧ table.header.kind ≠ 18) :
    (do
      if table.header.kind = 4 then
        guard (table.header.link = symbolTable ∧ table.header.entrySize = 24)
        guard (table.header.size % 24 = 0)
        let target ← sections[table.header.info]?
        (List.range (table.header.size / 24)).mapM fun index => do
          let relocation ← readRela bytes (table.header.offset + 24 * index)
          guard (relocation.symbolIndex < symbolCount)
          guard (relocation.offset < target.header.size)
          pure ({targetSection := table.header.info, offset := relocation.offset, symbol := relocation.symbolIndex, kind := relocation.relocationType, addend := relocation.addend} : ObjectRelocation)
      else do
        guard (table.header.kind ≠ 9 ∧ table.header.kind ≠ 18)
        pure []) = some ([] : List ObjectRelocation) := by
  simp [ordinary, supported, guard]

/-- Flatten already-certified tables without evaluating any relocation reader. -/
theorem readObjectRelocations_of_records (bytes : Bytes) (sections : List ObjectSection)
    (symbolTable symbolCount : Nat) (tables : List (List ObjectRelocation))
    (records : List.Forall₂ (fun table relocations =>
      (do
        if table.header.kind = 4 then
          guard (table.header.link = symbolTable ∧ table.header.entrySize = 24)
          guard (table.header.size % 24 = 0)
          let target ← sections[table.header.info]?
          (List.range (table.header.size / 24)).mapM fun index => do
            let relocation ← readRela bytes (table.header.offset + 24 * index)
            guard (relocation.symbolIndex < symbolCount)
            guard (relocation.offset < target.header.size)
            pure ({targetSection := table.header.info, offset := relocation.offset, symbol := relocation.symbolIndex, kind := relocation.relocationType, addend := relocation.addend} : ObjectRelocation)
        else do
          guard (table.header.kind ≠ 9 ∧ table.header.kind ≠ 18)
          pure []) = some relocations) sections tables) :
    readObjectRelocations bytes sections symbolTable symbolCount = some tables.flatten := by
  unfold readObjectRelocations
  rw [mapM_record_certificates _ records]
  rfl

end Silmaril.Formats.ELF
