module

public import Silmaril.Formats.ELF.Object.Types

/-! Data-only lossless ELF physical syntax and serializers. No byte readers.
Scalar range and contiguous-layout predicates do not assert ELF validity. -/
@[expose] public section
namespace Silmaril.Formats.ELF.Ast

def encodeLE : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | width + 1, value => BitVec.ofNat 8 value :: encodeLE width (value / 256)


def decodeLE : List (BitVec 8) → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * decodeLE rest


def Fits (width value : Nat) : Prop := value < 256 ^ width

abbrev Fields := List (Nat × Nat)

def fieldsBytes (fields : Fields) : List (BitVec 8) :=
  fields.flatMap fun field => encodeLE field.1 field.2

def fieldsFit (fields : Fields) : Prop := ∀ field ∈ fields, Fits field.1 field.2

instance (fields : Fields) : Decidable (fieldsFit fields) := by
  unfold fieldsFit Fits
  infer_instance

/-- ELF identification's fixed magic, class, data encoding and version prefix. -/
def identificationPrefix : List (BitVec 8) := [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1]

def headerFields (header : Header) : Fields :=
  [(2, header.fileType), (2, header.machine), (4, header.version),
   (8, header.entry), (8, header.programOffset), (8, header.sectionOffset),
   (4, header.flags), (2, header.headerSize), (2, header.programEntrySize),
   (2, header.programCount), (2, header.sectionEntrySize),
   (2, header.sectionCount), (2, header.sectionNameIndex)]

def programHeaderFields (header : ProgramHeader) : Fields :=
  [(4, header.kind), (4, header.flags), (8, header.offset), (8, header.virtualAddress),
   (8, header.physicalAddress), (8, header.fileSize), (8, header.memorySize), (8, header.alignment)]

def sectionHeaderFields (header : SectionHeader) : Fields :=
  [(4, header.name), (4, header.kind), (8, header.flags), (8, header.address),
   (8, header.offset), (8, header.size), (4, header.link), (4, header.info),
   (8, header.alignment), (8, header.entrySize)]

def symbolFields (symbol : Symbol) : Fields :=
  [(4, symbol.name), (1, symbol.info), (1, symbol.other), (2, symbol.sectionIndex),
   (8, symbol.value), (8, symbol.size)]

/-- The signed addend is encoded as a 64-bit two's-complement integer. -/
def relaFields (rela : Rela) : Fields :=
  [(8, rela.offset), (8, rela.info), (8, (BitVec.ofInt 64 rela.addend).toNat)]

inductive RawRole where
  | padding
  | sectionPayload (index : Nat)
  | opaque
  deriving DecidableEq, Repr

/-- Tags annotate physical file records, not disjoint semantic sections. A
section can include many records, and NOBITS has metadata but no file payload. -/
inductive Part where
  | header (fields : Header) (padding : Bytes)
  | programHeader (index : Nat) (fields : ProgramHeader)
  | sectionHeader (index : Nat) (fields : SectionHeader)
  | symbol (table index : Nat) (fields : Symbol)
  | rela (sectionIndex index : Nat) (fields : Rela)
  | raw (role : RawRole) (bytes : Bytes)
  deriving DecidableEq, Repr

/-- The padding field contains the seven EI_PAD bytes, including nonzero bytes. -/
def Part.bytes : Part → Bytes
  | .header fields padding =>
      (identificationPrefix ++ encodeLE 1 fields.osABI ++ encodeLE 1 fields.abiVersion ++
        padding.toList ++ fieldsBytes (headerFields fields)).toArray
  | .programHeader _ fields => (fieldsBytes (programHeaderFields fields)).toArray
  | .sectionHeader _ fields => (fieldsBytes (sectionHeaderFields fields)).toArray
  | .symbol _ _ fields => (fieldsBytes (symbolFields fields)).toArray
  | .rela _ _ fields => (fieldsBytes (relaFields fields)).toArray
  | .raw _ bytes => bytes

/-- Declared syntax span; malformed EI_PAD length remains visible. -/
def Part.size : Part → Nat
  | .header _ padding => 57 + padding.size
  | .programHeader .. => 56
  | .sectionHeader .. => 64
  | .symbol .. => 24
  | .rela .. => 24
  | .raw _ bytes => bytes.size

def Part.WellFormed : Part → Prop
  | .header fields padding =>
      padding.size = 7 ∧ Fits 1 fields.osABI ∧ Fits 1 fields.abiVersion ∧
        fieldsFit (headerFields fields)
  | .programHeader _ fields => fieldsFit (programHeaderFields fields)
  | .sectionHeader _ fields => fieldsFit (sectionHeaderFields fields)
  | .symbol _ _ fields => fieldsFit (symbolFields fields)
  | .rela _ _ fields => fieldsFit (relaFields fields) ∧
      -(2 ^ 63 : Int) ≤ fields.addend ∧ fields.addend < 2 ^ 63
  | .raw .. => True

instance (part : Part) : Decidable part.WellFormed := by
  cases part <;> unfold Part.WellFormed Fits <;> infer_instance


structure Block where
  offset : Nat
  body : Part
  deriving DecidableEq, Repr

def Block.bytes (block : Block) : Bytes := block.body.bytes

def Block.size (block : Block) : Nat := block.body.size


structure File where
  blocks : List Block
  deriving DecidableEq, Repr

def File.bytes (file : File) : Bytes :=
  (file.blocks.flatMap fun block => block.bytes.toList).toArray


def BlocksAt : Nat → List Block → Prop
  | _, [] => True
  | expected, block :: rest => block.offset = expected ∧ block.body.WellFormed ∧
      BlocksAt (expected + block.size) rest

def decidableBlocksAt (offset : Nat) (blocks : List Block) : Decidable (BlocksAt offset blocks) :=
  match blocks with
  | [] => isTrue trivial
  | block :: rest =>
    have : Decidable (BlocksAt (offset + block.size) rest) :=
      decidableBlocksAt (offset + block.size) rest
    inferInstanceAs (Decidable (block.offset = offset ∧ block.body.WellFormed ∧
      BlocksAt (offset + block.size) rest))

instance (offset : Nat) (blocks : List Block) : Decidable (BlocksAt offset blocks) :=
  decidableBlocksAt offset blocks


def File.WellFormed (file : File) : Prop := BlocksAt 0 file.blocks

instance (file : File) : Decidable file.WellFormed := inferInstanceAs (Decidable (BlocksAt 0 file.blocks))

/-- Byte identity can be proved without accepting a semantic interpretation.
Use list equality for large concrete arrays when array equality is expensive. -/
def File.Lossless (file : File) (original : Bytes) : Prop := file.bytes = original


def File.ofBytes (bytes : Bytes) : File := ⟨[⟨0, .raw .opaque bytes⟩]⟩


end Silmaril.Formats.ELF.Ast
