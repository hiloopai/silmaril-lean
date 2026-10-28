module
public import Silmaril.Formats.ELF.Basic

/-!
Total ELF64 little-endian record readers. These decode bounded bytes, not an ISA
or executable policy. File type, machine, permissions, linkage and relocation
support are checked by higher layers. Extended table numbering is explicitly
excluded by the table readers; callers may still inspect the raw header.
-/
@[expose] public section
namespace Silmaril.Formats.ELF

/-- Every byte read must exist; arithmetic is unbounded and cannot wrap. -/
def readLE (bytes : Bytes) (offset : Nat) : Nat → Option Nat
  | 0 => some 0
  | width + 1 => do
    let byte ← bytes.toList[offset]?
    let rest ← readLE bytes (offset + 1) width
    pure (byte.toNat + 256 * rest)

/-- ELF64 signed two's-complement addends. -/
def signed64 (value : Nat) : Int :=
  if value < 2 ^ 63 then Int.ofNat value else Int.ofNat value - 2 ^ 64

/-- Check ELF64/LE/current identification; preserve the remaining header fields. -/
def readHeader (bytes : Bytes) : Option Header := do
  guard (64 ≤ bytes.size)
  guard ((← readLE bytes 0 4) = 0x464c457f)
  guard ((← readLE bytes 4 1) = 2)
  guard ((← readLE bytes 5 1) = 1)
  guard ((← readLE bytes 6 1) = 1)
  let osABI ← readLE bytes 7 1
  let abiVersion ← readLE bytes 8 1
  let fileType ← readLE bytes 16 2
  let machine ← readLE bytes 18 2
  let version ← readLE bytes 20 4
  let entry ← readLE bytes 24 8
  let programOffset ← readLE bytes 32 8
  let sectionOffset ← readLE bytes 40 8
  let flags ← readLE bytes 48 4
  let headerSize ← readLE bytes 52 2
  let programEntrySize ← readLE bytes 54 2
  let programCount ← readLE bytes 56 2
  let sectionEntrySize ← readLE bytes 58 2
  let sectionCount ← readLE bytes 60 2
  let sectionNameIndex ← readLE bytes 62 2
  pure ⟨osABI, abiVersion, fileType, machine, version, entry, programOffset, sectionOffset,
    flags, headerSize, programEntrySize, programCount, sectionEntrySize, sectionCount, sectionNameIndex⟩

def readProgramHeader (bytes : Bytes) (offset : Nat) : Option ProgramHeader := do
  let kind ← readLE bytes offset 4
  let flags ← readLE bytes (offset + 4) 4
  let fileOffset ← readLE bytes (offset + 8) 8
  let virtualAddress ← readLE bytes (offset + 16) 8
  let physicalAddress ← readLE bytes (offset + 24) 8
  let fileSize ← readLE bytes (offset + 32) 8
  let memorySize ← readLE bytes (offset + 40) 8
  let alignment ← readLE bytes (offset + 48) 8
  pure ⟨kind, flags, fileOffset, virtualAddress, physicalAddress, fileSize, memorySize, alignment⟩

def readSectionHeader (bytes : Bytes) (offset : Nat) : Option SectionHeader := do
  let name ← readLE bytes offset 4
  let kind ← readLE bytes (offset + 4) 4
  let flags ← readLE bytes (offset + 8) 8
  let address ← readLE bytes (offset + 16) 8
  let fileOffset ← readLE bytes (offset + 24) 8
  let size ← readLE bytes (offset + 32) 8
  let link ← readLE bytes (offset + 40) 4
  let info ← readLE bytes (offset + 44) 4
  let alignment ← readLE bytes (offset + 48) 8
  let entrySize ← readLE bytes (offset + 56) 8
  pure ⟨name, kind, flags, address, fileOffset, size, link, info, alignment, entrySize⟩

def readSymbol (bytes : Bytes) (offset : Nat) : Option Symbol := do
  let name ← readLE bytes offset 4
  let info ← readLE bytes (offset + 4) 1
  let other ← readLE bytes (offset + 5) 1
  let sectionIndex ← readLE bytes (offset + 6) 2
  let value ← readLE bytes (offset + 8) 8
  let size ← readLE bytes (offset + 16) 8
  pure ⟨name, info, other, sectionIndex, value, size⟩

def readRela (bytes : Bytes) (offset : Nat) : Option Rela := do
  let address ← readLE bytes offset 8
  let info ← readLE bytes (offset + 8) 8
  let addend ← readLE bytes (offset + 16) 8
  pure ⟨address, info, signed64 addend⟩

/-- Bounded fixed-width table; empty tables need no readable record. -/
def readTable {Record : Type} (reader : Bytes → Nat → Option Record)
    (bytes : Bytes) (offset width count : Nat) : Option (List Record) := do
  guard (offset + width * count ≤ bytes.size)
  (List.range count).mapM (fun index => reader bytes (offset + width * index))

def readProgramHeaders (bytes : Bytes) (header : Header) : Option (List ProgramHeader) := do
  guard (header.programCount < 0xffff)
  if header.programCount = 0 then pure [] else do
    guard (header.programEntrySize = 56 ∧ 64 ≤ header.programOffset)
    readTable readProgramHeader bytes header.programOffset 56 header.programCount

def readSectionHeaders (bytes : Bytes) (header : Header) : Option (List SectionHeader) := do
  guard (header.sectionCount < 0xff00 ∧ header.sectionNameIndex < 0xff00)
  if header.sectionCount = 0 then
    guard (header.sectionOffset = 0 ∧ header.sectionNameIndex = 0)
    pure []
  else do
    guard (header.sectionEntrySize = 64 ∧ 64 ≤ header.sectionOffset)
    guard (header.sectionNameIndex < header.sectionCount)
    readTable readSectionHeader bytes header.sectionOffset 64 header.sectionCount

/-- A checked finite byte slice for file-backed sections or segments. -/
def slice (bytes : Bytes) (offset size : Nat) : Option Bytes := do
  guard (offset + size ≤ bytes.size)
  pure ⟨(bytes.toList.drop offset).take size⟩

end Silmaril.Formats.ELF
