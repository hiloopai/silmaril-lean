module

public import Silmaril.Elf.Parse.Defs
public import Silmaril.Project.Core.Defs
public import Silmaril.Formats.ELF.Cst.IsCst
public import Silmaril.Prelude.Bytes.Format.Defs

/-! # ELF-like things; the machine and the entry points of an ELF file (`Silmaril.Elf.Like`)

One interface for everything that may denote an ELF file: raw bytes, kernel bytes, project values,
binary images, a lossless CST and the metadata AST itself.

| decl | statement |
|---|---|
| `ElfLike α` | `α` may denote an ELF file: its metadata AST, `none` when it does not |
| `ElfLike.ofSource β` | the instance of any byte representation (`Silmaril.ByteSource`): the specification parse of its bytes |
| `Denotes x A` | `x` denotes the AST `A` (for a `Blob`, exactly `Parses`) |
| `cst_ast` | a CST checked against an image denotes what the image does |
| `MachineIs x m` | the `e_machine` of `x` is `m` |
| `File.entries` | the entry points of a file, by kind |
| `EntriesAre x es`, `IsEntry x e` | the entry points of `x` are `es`; `e` is one |

## Byte carriers: one class, no second byte abstraction

Byte representations already have one class, `Silmaril.ByteSource` (`bytes : β → List UInt8`;
instances for `ByteArray`, `KBytes` and `List UInt8`). This module does **not** add another: a
byte representation becomes `ElfLike` through `ElfLike.ofSource`, a `def` and never a blanket
instance, so no type reaches two `ElfLike` instances. The canonical kernel form of a file stays
`Silmaril.X86.Link.Blob` (`blobOf`), which every existing fact (`Parses`, `CodeAt`, …) is stated
on; `toBlob` is the bridge, and `Thms` proves that the instances agree with the `blobOf` forms the
existing rows use (`denotes_byteArray`, `denotes_kbytes`, `denotes_value`).

The AST is `ElfLike` but holds code by reference (`Span`), so facts that read code bytes stay on
`Blob`. Partial and paged views of a file stay explicit oracle arguments to `Rd.run`
(`Silmaril.Elf.Decode` runs them three-valued).

Ported from the authors' development of the ELF API (`BytesLike`/`ElfLike`, entry points and
machine shapes). Migration: the development's `BytesLike.blob x` is `toBlob (ByteSource.bytes x)`
here, and `ElfLike.ofBytes` is `ElfLike.ofSource`; the names of every other declaration are kept.
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.X86.Link (Blob)
open Silmaril.Project (Value)
open Silmaril.Formats.ELF (NameBytes ObjectSymbol)

/-! ## ELF-like -/

/-- **`α` may denote an ELF file**: its metadata AST, `none` when `x` is not an ELF64 file this
API reads (`Silmaril.Elf.Decode` says why). -/
class ElfLike (α : Type) where
  ast? : α → Option File

/-- The canonical kernel form of a byte list, as the existing rows build it (`blobOf`). -/
def toBlob (bs : List UInt8) : Blob := blobOf ⟨⟨⟨bs⟩⟩⟩

/-- Through the bytes of any representation: the specification parse. -/
@[instance_reducible] def ElfLike.ofSource (β : Type) [ByteSource β] : ElfLike β :=
  ⟨fun x => parse (toBlob (ByteSource.bytes x))⟩

/-- A `Blob` is read by the specification directly. -/
instance instElfLikeBlob : ElfLike Blob := ⟨parse⟩

instance instElfLikeByteArray : ElfLike ByteArray := ElfLike.ofSource ByteArray
instance instElfLikeKBytes : ElfLike KBytes := ElfLike.ofSource KBytes
instance instElfLikeBytesList : ElfLike (List UInt8) := ElfLike.ofSource (List UInt8)

/-- The byte strings of the format registry, as `blobOf` (the form of `Shapes.file`). -/
instance instElfLikeFormatsBytes : ElfLike Silmaril.Formats.Bytes := ⟨fun b => parse (blobOf b)⟩

/-- A project value, through its bytes (definitionally `parse (Shapes.file X)`). -/
instance instElfLikeValue {V : Type} : ElfLike (Value V) := ⟨fun X => parse (blobOf X.bytes)⟩

/-- The ELF readers' byte arrays (`Array (BitVec 8)`). -/
instance instElfLikeElfBytes : ElfLike Silmaril.Formats.ELF.Bytes := ⟨fun b => parse (Blob.ofBytes b)⟩

/-- A binary image, through its bits. -/
instance instElfLikeBinaryImage : ElfLike Silmaril.BinaryImage :=
  ⟨fun img => parse (Blob.ofBytes img.bits)⟩

/-- The AST denotes itself. -/
instance instElfLikeFile : ElfLike File := ⟨some⟩

/-- The AST a CST denotes: the parse of its serialization (`none` when it does not serialize). -/
def ofCst (c : Silmaril.Formats.ELF.Cst.File) : Option File :=
  c.bytes.bind fun b => parse (Blob.ofBytes b)

instance instElfLikeCst : ElfLike Silmaril.Formats.ELF.Cst.File := ⟨ofCst⟩

/-- **`x` denotes the AST `A`.** -/
def Denotes {α : Type} [ElfLike α] (x : α) (A : File) : Prop := ElfLike.ast? x = some A

/-- On a `Blob`, `Denotes` is the parse relation. -/
theorem denotes_blob (F : Blob) (A : File) : Denotes F A ↔ Parses F A := Iff.rfl

/-! ## Machine -/

/-- `EM_X86_64`. -/
def EM_X86_64 : Nat := 62

/-- `EM_AARCH64`. -/
def EM_AARCH64 : Nat := 183

/-- `EM_RISCV`. -/
def EM_RISCV : Nat := 243

/-- **The `e_machine` of `x` is `m`.** Any value is accepted and recorded: an `e_machine` this
repository has no instruction model for is not a malformed file. -/
def MachineIs {α : Type} [ElfLike α] (x : α) (m : Nat) : Prop :=
  ∃ A, Denotes x A ∧ A.header.machine = m

/-! ## Entry points -/

/-- How control enters an object from outside it. -/
inductive Via where
  /-- `e_entry`: process start, from the kernel or ld.so. -/
  | start
  /-- Entry `index` of `.dynsym`, a function ld.so's lookups can bind; for an IFUNC the address
  is the resolver's. -/
  | exported (index : Nat) (name : NameBytes) (ifunc : Bool)
  /-- A defined global or weak function of `.symtab` (`ET_REL`); the address is an offset in
  section `shndx`. -/
  | symbol (name : NameBytes) (shndx : Nat)
  deriving DecidableEq, Repr

/-- An entry point: how it is entered and where (relative to the load base for `ET_DYN`). -/
structure EntryPoint where
  via : Via
  vaddr : Nat
  deriving DecidableEq, Repr

/-- `s` is a defined (not `SHN_UNDEF`, not reserved), `STB_GLOBAL` or `STB_WEAK`, `STV_DEFAULT` or
`STV_PROTECTED`, `STT_FUNC` or `STT_GNU_IFUNC` symbol. -/
def callable (s : ObjectSymbol) : Bool :=
  s.raw.sectionIndex != 0 && decide (s.raw.sectionIndex < 0xff00) &&
    (s.binding == 1 || s.binding == 2) &&
    (s.raw.visibility == 0 || s.raw.visibility == 3) &&
    (s.kind == 2 || s.kind == 10)

namespace File

/-- The functions of `.dynsym` that other objects can bind, with their `.dynsym` indices. -/
def exports (A : File) : List EntryPoint :=
  let ds := A.dynsyms
  (List.range ds.length).filterMap fun i =>
    match ds[i]? with
    | some s => if callable s then some ⟨.exported i s.name (s.kind == 10), s.raw.value⟩ else none
    | none => none

/-- **The entry points of `A`, by kind.** `ET_REL`: its defined global functions. Every other
kind: `e_entry` when it is nonzero (`libc.so.6` is runnable), then its exports. The code ld.so
runs at load (`DT_INIT`, `DT_INIT_ARRAY`, IFUNC resolvers) is not yet listed. -/
def entries (A : File) : List EntryPoint :=
  if A.kind = .relocatable then
    ((A.symbols .symtab).filter callable).map fun s =>
      ⟨.symbol s.name s.raw.sectionIndex, s.raw.value⟩
  else
    (if A.header.entry = 0 then [] else [⟨.start, A.header.entry⟩]) ++ A.exports

end File

/-- **The entry points of `x` are `es`**, in `File.entries` order. -/
def EntriesAre {α : Type} [ElfLike α] (x : α) (es : List EntryPoint) : Prop :=
  ∃ A, Denotes x A ∧ A.entries = es

/-- **`e` is an entry point of `x`.** The row for large files. -/
def IsEntry {α : Type} [ElfLike α] (x : α) (e : EntryPoint) : Prop :=
  ∃ A, Denotes x A ∧ e ∈ A.entries

end Silmaril.Elf
