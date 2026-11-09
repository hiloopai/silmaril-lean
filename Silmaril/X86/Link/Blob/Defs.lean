module

public import Silmaril.Formats.ELF.Object
public import Silmaril.Process.LPS.ELFImage

/-! # Byte blobs and kernel-fast ELF readers

Kernel evaluation of the public certified readers (`Silmaril.Formats.ELF.readObject`,
`Silmaril.Process.LPS.ELFImage.parse`) walks `bytes.toList` once per byte read, so
`decide +kernel` on a 1 KB object already takes about 30 s, and a 5 KB one many
minutes. Here a file is one `Nat` (`Blob`), and each reader below is the public
reader with every byte access replaced by a shift and a modulus. These copies are
**not trusted**: `Silmaril.Proofs.X86.Link.Blob` proves each equal to the public
reader on `bytesOf n len` (`readObject_bytesOf`, `parse_bytesOf`), so a fixture checked with
them is a statement about the public readers.
-/

@[expose] public section

namespace Silmaril.X86.Link

/-- A file as one natural number (little-endian) and its length. Kernel `Nat`
arithmetic is GMP-accelerated, so random access costs one shift instead of a
list walk. -/
structure Blob where
  n : Nat
  len : Nat
  deriving DecidableEq, Repr

namespace Blob

open Silmaril.Formats.ELF
open Silmaril.Process.LPS

/-- Byte `i` of a little-endian blob. -/
def byteAt (n i : Nat) : BitVec 8 := BitVec.ofNat 8 (n >>> (8 * i))

/-- The first `len` little-endian bytes of `n`. -/
def bytesOf (n len : Nat) : Bytes := ((List.range len).map (byteAt n)).toArray

/-- The byte array a blob denotes. -/
def bytes (b : Blob) : Bytes := bytesOf b.n b.len

/-- Little-endian value of a byte list. -/
def valueLE : List (BitVec 8) → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * valueLE rest

/-- Every byte array is a blob (`Blob.bytes_ofBytes`; `Blob.ofBytes` is the inverse of `Blob.bytes`). -/
def ofBytes (bytes : Bytes) : Blob := ⟨valueLE bytes.toList, bytes.size⟩

/-- `readLE` on `bytesOf n len`, by arithmetic. -/
def readLEN (n len off w : Nat) : Option Nat :=
  if w = 0 ∨ off + w ≤ len then some ((n >>> (8 * off)) % 2 ^ (8 * w)) else none

/-- `readHeader` on `bytesOf n len`. -/
def readHeaderN (n len : Nat) : Option Header := do
  guard (64 ≤ len)
  guard ((← readLEN n len 0 4) = 0x464c457f)
  guard ((← readLEN n len 4 1) = 2)
  guard ((← readLEN n len 5 1) = 1)
  guard ((← readLEN n len 6 1) = 1)
  let osABI ← readLEN n len 7 1
  let abiVersion ← readLEN n len 8 1
  let fileType ← readLEN n len 16 2
  let machine ← readLEN n len 18 2
  let version ← readLEN n len 20 4
  let entry ← readLEN n len 24 8
  let programOffset ← readLEN n len 32 8
  let sectionOffset ← readLEN n len 40 8
  let flags ← readLEN n len 48 4
  let headerSize ← readLEN n len 52 2
  let programEntrySize ← readLEN n len 54 2
  let programCount ← readLEN n len 56 2
  let sectionEntrySize ← readLEN n len 58 2
  let sectionCount ← readLEN n len 60 2
  let sectionNameIndex ← readLEN n len 62 2
  pure ⟨osABI, abiVersion, fileType, machine, version, entry, programOffset, sectionOffset,
    flags, headerSize, programEntrySize, programCount, sectionEntrySize, sectionCount, sectionNameIndex⟩

def readSectionHeaderN (n len offset : Nat) : Option SectionHeader := do
  let name ← readLEN n len offset 4
  let kind ← readLEN n len (offset + 4) 4
  let flags ← readLEN n len (offset + 8) 8
  let address ← readLEN n len (offset + 16) 8
  let fileOffset ← readLEN n len (offset + 24) 8
  let size ← readLEN n len (offset + 32) 8
  let link ← readLEN n len (offset + 40) 4
  let info ← readLEN n len (offset + 44) 4
  let alignment ← readLEN n len (offset + 48) 8
  let entrySize ← readLEN n len (offset + 56) 8
  pure ⟨name, kind, flags, address, fileOffset, size, link, info, alignment, entrySize⟩

def readSymbolN (n len offset : Nat) : Option Symbol := do
  let name ← readLEN n len offset 4
  let info ← readLEN n len (offset + 4) 1
  let other ← readLEN n len (offset + 5) 1
  let sectionIndex ← readLEN n len (offset + 6) 2
  let value ← readLEN n len (offset + 8) 8
  let size ← readLEN n len (offset + 16) 8
  pure ⟨name, info, other, sectionIndex, value, size⟩

def readRelaN (n len offset : Nat) : Option Rela := do
  let address ← readLEN n len offset 8
  let info ← readLEN n len (offset + 8) 8
  let addend ← readLEN n len (offset + 16) 8
  pure ⟨address, info, signed64 addend⟩

def readTableN {R : Type} (reader : Nat → Option R) (len offset width count : Nat) : Option (List R) := do
  guard (offset + width * count ≤ len)
  (List.range count).mapM (fun index => reader (offset + width * index))

def readSectionHeadersN (n len : Nat) (header : Header) : Option (List SectionHeader) := do
  guard (header.sectionCount < 0xff00 ∧ header.sectionNameIndex < 0xff00)
  if header.sectionCount = 0 then
    guard (header.sectionOffset = 0 ∧ header.sectionNameIndex = 0)
    pure []
  else do
    guard (header.sectionEntrySize = 64 ∧ 64 ≤ header.sectionOffset)
    guard (header.sectionNameIndex < header.sectionCount)
    readTableN (readSectionHeaderN n len) len header.sectionOffset 64 header.sectionCount

def sectionDataN (n len : Nat) (part : SectionHeader) : Option Bytes := do
  if part.kind = 8 then
    pure #[]
  else do
    guard (part.offset + part.size ≤ len)
    pure (bytesOf (n >>> (8 * part.offset)) part.size)

def readObjectSectionsN (n len : Nat) (headers : List SectionHeader)
    (strings : Bytes) : Option (List ObjectSection) :=
  headers.mapM fun header => do
    guard (validSectionAlignment header.alignment)
    let name ← readName strings header.name
    let data ← sectionDataN n len header
    pure { header, name, data }

def readObjectSymbolsN (n len : Nat) (sections : List ObjectSection)
    (tableIndex : Nat) : Option (List ObjectSymbol) := do
  let table ← sections[tableIndex]?
  guard (table.header.kind = 2 ∧ table.header.entrySize = 24)
  guard (table.header.size % 24 = 0 ∧ 24 ≤ table.header.size)
  let strings ← sections[table.header.link]?
  guard (strings.header.kind = 3)
  (List.range (table.header.size / 24)).mapM fun index => do
    let raw ← readSymbolN n len (table.header.offset + 24 * index)
    let name ← readName strings.data raw.name
    guard (raw.sectionIndex < sections.length ∨ 0xff00 ≤ raw.sectionIndex)
    pure { raw, name }

def readObjectRelocationsN (n len : Nat) (sections : List ObjectSection)
    (symbolTable symbolCount : Nat) : Option (List ObjectRelocation) := do
  let tables : List (List ObjectRelocation) ← sections.mapM fun table => do
    if table.header.kind = 4 then
      guard (table.header.link = symbolTable ∧ table.header.entrySize = 24)
      guard (table.header.size % 24 = 0)
      let target ← sections[table.header.info]?
      (List.range (table.header.size / 24)).mapM fun index => do
        let relocation ← readRelaN n len (table.header.offset + 24 * index)
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

/-- `readObject` on `bytesOf n len`. -/
def readObjectN (n len : Nat) : Option ObjectFile := do
  let header ← readHeaderN n len
  guard (header.fileType = 1 ∧ header.version = 1 ∧ header.entry = 0 ∧ header.programCount = 0)
  guard (header.headerSize = 64)
  let headers ← readSectionHeadersN n len header
  guard (0 < headers.length)
  let null ← headers[0]?
  guard (null.kind = 0 ∧ null.size = 0)
  let names ← headers[header.sectionNameIndex]?
  guard (names.kind = 3)
  let strings ← sectionDataN n len names
  let sections ← readObjectSectionsN n len headers strings
  let symbolTables := (List.range sections.length).filter fun index =>
    (sections[index]?.map (fun part => part.header.kind)) == some 2
  let [symbolTable] := symbolTables | none
  let symbols ← readObjectSymbolsN n len sections symbolTable
  let relocations ← readObjectRelocationsN n len sections symbolTable symbols.length
  pure { header, sections, symbols, relocations }

def readProgramHeaderN (n len offset : Nat) : Option ProgramHeader := do
  let kind ← readLEN n len offset 4
  let flags ← readLEN n len (offset + 4) 4
  let fileOffset ← readLEN n len (offset + 8) 8
  let virtualAddress ← readLEN n len (offset + 16) 8
  let physicalAddress ← readLEN n len (offset + 24) 8
  let fileSize ← readLEN n len (offset + 32) 8
  let memorySize ← readLEN n len (offset + 40) 8
  let alignment ← readLEN n len (offset + 48) 8
  pure ⟨kind, flags, fileOffset, virtualAddress, physicalAddress, fileSize, memorySize, alignment⟩

def readProgramHeadersN (n len : Nat) (header : Header) : Option (List ProgramHeader) := do
  guard (header.programCount < 0xffff)
  if header.programCount = 0 then pure [] else do
    guard (header.programEntrySize = 56 ∧ 64 ≤ header.programOffset)
    readTableN (readProgramHeaderN n len) len header.programOffset 56 header.programCount

/-- `ELFImage.ValidLoad` on a file of `len` bytes (it reads only the file size). -/
def ValidLoadN (policy : ELFImage.Policy) (len : Nat) (header : ProgramHeader) : Prop :=
  header.kind = 1 ∧ header.flags < 8 ∧ header.fileSize ≤ header.memorySize ∧
    header.offset + header.fileSize ≤ len ∧ 0 < header.memorySize ∧
    header.virtualAddress + header.memorySize ≤ policy.taskSize ∧
    Nat.land header.alignment (header.alignment - 1) = 0 ∧
    (header.alignment ≤ 1 ∨ header.virtualAddress % header.alignment = header.offset % header.alignment) ∧
    header.virtualAddress % 4096 = header.offset % 4096

instance (policy : ELFImage.Policy) (len : Nat) (header : ProgramHeader) :
    Decidable (ValidLoadN policy len header) := by
  unfold ValidLoadN
  infer_instance

/-- Two loaded segments (as program headers) do not overlap in memory. -/
def LoadDisjoint (first second : ProgramHeader) : Prop :=
  first.virtualAddress + first.memorySize ≤ second.virtualAddress ∨
    second.virtualAddress + second.memorySize ≤ first.virtualAddress

instance (first second : ProgramHeader) : Decidable (LoadDisjoint first second) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- `ELFImage.RecordsValid` on `bytesOf n len`, without materialising the file: it depends on
the file only through its size and the segments' bases and sizes
(`Silmaril.X86.Link.Blob.recordsValidN_iff`). -/
def RecordsValidN (policy : ELFImage.Policy) (len : Nat) (records : ELFImage.Records) : Prop :=
  ELFImage.HeaderSupported policy records.header records.programHeaders ∧
    records.phdrOwner ∈ records.programHeaders ∧
    ELFImage.HoldsPhdrTable records.header records.phdrOwner ∧
    ELFImage.loadHeaders records.programHeaders ≠ [] ∧
    (∀ ph ∈ ELFImage.loadHeaders records.programHeaders, ValidLoadN policy len ph) ∧
    (ELFImage.loadHeaders records.programHeaders).Pairwise LoadDisjoint

instance (policy : ELFImage.Policy) (len : Nat) (records : ELFImage.Records) :
    Decidable (RecordsValidN policy len records) := by
  unfold RecordsValidN
  infer_instance

/-- `ELFImage.parse` on `bytesOf n len`. -/
def parseN (policy : ELFImage.Policy) (n len : Nat) : Option ELFImage.Records := do
  let header ← readHeaderN n len
  let headers ← readProgramHeadersN n len header
  let owner ← headers.find? (fun ph => decide (ELFImage.HoldsPhdrTable header ph))
  let records := ELFImage.Records.mk header headers owner
  if RecordsValidN policy len records then some records else none

end Blob

end Silmaril.X86.Link
