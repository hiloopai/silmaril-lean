module
public import Init.Data.BitVec

/-!
Architecture-independent ELF64 record shapes. Numeric machine IDs, file types,
section kinds and relocation codes are retained for the caller's policy.
Field widths/layouts follow the System V gABI ELF64 definitions:
https://refspecs.linuxfoundation.org/elf/gabi4+/ch4.eheader.html
https://refspecs.linuxfoundation.org/elf/gabi4+/ch4.sheader.html
https://refspecs.linuxfoundation.org/elf/gabi4+/ch4.symtab.html
https://refspecs.linuxfoundation.org/elf/gabi4+/ch4.reloc.html
-/
@[expose] public section
namespace Silmaril.Formats.ELF

abbrev Bytes := Array (BitVec 8)

structure Header where
  osABI : Nat
  abiVersion : Nat
  fileType : Nat
  machine : Nat
  version : Nat
  entry : Nat
  programOffset : Nat
  sectionOffset : Nat
  flags : Nat
  headerSize : Nat
  programEntrySize : Nat
  programCount : Nat
  sectionEntrySize : Nat
  sectionCount : Nat
  sectionNameIndex : Nat
  deriving DecidableEq, Repr

structure ProgramHeader where
  kind : Nat
  flags : Nat
  offset : Nat
  virtualAddress : Nat
  physicalAddress : Nat
  fileSize : Nat
  memorySize : Nat
  alignment : Nat
  deriving DecidableEq, Repr

structure SectionHeader where
  name : Nat
  kind : Nat
  flags : Nat
  address : Nat
  offset : Nat
  size : Nat
  link : Nat
  info : Nat
  alignment : Nat
  entrySize : Nat
  deriving DecidableEq, Repr

structure Symbol where
  name : Nat
  info : Nat
  other : Nat
  sectionIndex : Nat
  value : Nat
  size : Nat
  deriving DecidableEq, Repr

def Symbol.binding (symbol : Symbol) : Nat := symbol.info / 16
def Symbol.kind (symbol : Symbol) : Nat := symbol.info % 16
def Symbol.visibility (symbol : Symbol) : Nat := symbol.other % 4

structure Rela where
  offset : Nat
  info : Nat
  addend : Int
  deriving DecidableEq, Repr

def Rela.symbolIndex (relocation : Rela) : Nat := relocation.info / 2 ^ 32
def Rela.relocationType (relocation : Rela) : Nat := relocation.info % 2 ^ 32

/-- Common loaded-segment representation, independent of instruction decoding. -/
structure Segment where
  address : Nat
  flags : Nat
  memorySize : Nat
  data : Bytes
  deriving DecidableEq, Repr

structure Image where
  entry : Nat
  segments : List Segment
  deriving DecidableEq, Repr

end Silmaril.Formats.ELF
