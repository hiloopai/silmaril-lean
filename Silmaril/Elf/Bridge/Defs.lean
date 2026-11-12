module

public import Silmaril.Elf.Facts.Defs
public import Silmaril.Elf.Link.ElfBind.Defs
public import Silmaril.Elf.Link.Dyn.Loader.Defs
public import Silmaril.Formats.ELF.Object
public import Silmaril.Formats.ELF.Cst.Types
public import Silmaril.Process.LPS.ELFImage

/-! # Bridges: the ELF API against the existing models

The API (`Silmaril.Elf`) adds a model; it does not replace the ones in use. This module states how
it relates to each of them, as **named open goals** (`Task`s) and conversions. Nothing here is assumed: a theorem that needs a bridge takes
the `Task` as a hypothesis (`Bridge.Thms`).

| existing model | where | relation | goal |
|---|---|---|---|
| ELF64 header reader | `Silmaril.Formats.ELF.readHeader` | equal results | `Task.header_silmaril` |
| program/section header readers | `readProgramHeaders`, `readSectionHeaders` | refinement | `Task.tables_silmaril` |
| `ET_REL` object reader | `Silmaril.Formats.ELF.readObject` | refinement | `Task.readObject_agrees` |
| shared CST | `Silmaril.Formats.ELF.Cst.File` | refinement (`ET_REL`) | `Task.cst_agrees` |
| LPS `ET_EXEC` loader | `Silmaril.Process.LPS.ELFImage.parse` | refinement | `Task.elfImage_agrees` |
| loader headers | `DynElf.Elf.dynInfo` | equal results (x86-64) | `Task.dynInfo_rd` |
| ld.so lookup | `DynElf.Elf.lookupDef` | equal results | `Task.lookup_rd` |
| `DT_NEEDED` | `DynElf.Elf.needed` | refinement | `Task.needed_rd` |
| dynamic relocations | `DynElf.Elf.relas` | refinement | `Task.relas_rd` |
| binding | `ElfBind.Bound` | iff | `Task.bound_iff` |
| contents | `ElfBind.CodeAt` | iff | `Task.codeAt_iff` |
| placement | `ElfBind.Placement` | iff | `Task.placement_iff` |
| loading | `Dyn.ExeLoaded` ⊑ `ElfBind.RoLoaded` | implication | `Task.roLoaded_of_exeLoaded` (proved from `dynInfo_rd`, `relas_rd`: `Exe.roLoaded_task`) |
| fast parse checker | (parse builder) | soundness | `Task.check_sound` |

"Refinement": whenever the existing reader succeeds, the API's parse agrees with it (the API
accepts more files: every machine, every object kind, `ET_DYN`).
-/

@[expose] public section

namespace Silmaril.Elf.Bridge

open Silmaril.Formats.ELF (NameBytes)
open Silmaril.X86.Link (Blob)
open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Elf.Link.DynElf (blobRead)

/-! ## Conversions -/

/-- A name as `Silmaril.Elf.Link.DynElf.Name`. -/
def toDynName (n : NameBytes) : Silmaril.Elf.Link.DynElf.Name := n.map BitVec.toNat

def _root_.Silmaril.Elf.Ver.toDyn (v : Ver) : Silmaril.Elf.Link.DynElf.Elf.Ver := ⟨toDynName v.name, v.hash, v.hidden⟩

def _root_.Silmaril.Elf.Ref.toDyn (r : Ref) : Silmaril.Elf.Link.DynElf.Elf.Ref := ⟨toDynName r.name, r.weak, r.ver.map Ver.toDyn⟩

def _root_.Silmaril.Elf.Def.toDyn (d : Def) : Silmaril.Elf.Link.DynElf.Elf.Def := ⟨d.value, d.ifunc, d.abs⟩

def _root_.Silmaril.Elf.Sel.toBind : Sel → Silmaril.Elf.Link.ElfBind.Sel
  | .dyn r => .dyn r.toDyn
  | .sym n => .sym (toDynName n)
  | .fn r => .fn r.toDyn

def phdrToDyn (ph : Silmaril.Formats.ELF.ProgramHeader) : Silmaril.Elf.Link.DynElf.Elf.Phdr :=
  ⟨ph.kind, ph.flags, ph.offset, ph.virtualAddress, ph.fileSize, ph.memorySize⟩

/-- The loader's header view of an AST. -/
def dynInfoOf (A : File) : Silmaril.Elf.Link.DynElf.Elf.DynInfo :=
  ⟨A.phdrs.map phdrToDyn, A.dynamic.map fun e => (e.tag, e.val)⟩

/-- A relocation without its source section: place, type, symbol, addend. -/
def relocKey (r : File.Reloc) : Nat × Nat × Nat × Option Int := (r.offset, r.kind, r.symbol, r.addend)

/-- No dynamic relocation writes a read-only `PT_LOAD` (no `DT_TEXTREL`). -/
def NoTextRel (A : File) : Prop :=
  ∀ r ∈ A.relocs .dynamic, ∀ ph ∈ A.loads, ph.flags / 2 % 2 = 0 →
    r.offset + 8 ≤ ph.virtualAddress ∨ ph.virtualAddress + ph.memorySize ≤ r.offset

/-! ## silmaril-lean readers -/

def Task.header_silmaril : Prop :=
  ∀ (F : Blob) (A : File), Parses F A → Silmaril.Formats.ELF.readHeader F.bytes = some A.header

def Task.tables_silmaril : Prop :=
  ∀ (F : Blob) (A : File), Parses F A →
    (∀ ps, Silmaril.Formats.ELF.readProgramHeaders F.bytes A.header = some ps → ps = A.phdrs) ∧
    (∀ ss, Silmaril.Formats.ELF.readSectionHeaders F.bytes A.header = some ss →
      ss = A.sections.map (·.header))

def Task.readObject_agrees : Prop :=
  ∀ (F : Blob) (A : File) obj, Parses F A → Silmaril.Formats.ELF.readObject F.bytes = some obj →
    A.kind = .relocatable ∧ obj.header = A.header ∧ obj.sections.map (·.header) = A.sections.map (·.header) ∧
      obj.sections.map (·.name) = A.sections.map (·.name) ∧ obj.symbols = A.symbols .symtab

/-- The shared CST of an `ET_REL` file, once its interpretation is certified, agrees with the AST. -/
def Task.cst_agrees : Prop :=
  ∀ (F : Blob) (A : File) (c : Silmaril.Formats.ELF.Cst.File), Parses F A →
    c.Lossless F.bytes → Silmaril.Formats.ELF.readObject F.bytes = some c.erase →
    c.header = A.header ∧ c.erase.symbols = A.symbols .symtab

def Task.elfImage_agrees : Prop :=
  ∀ (P : Silmaril.Process.LPS.ELFImage.Policy) (F : Blob) (A : File) r, Parses F A →
    Silmaril.Process.LPS.ELFImage.parse P F.bytes = some r →
    A.kind = .exec ∧ r.header = A.header ∧ r.programHeaders = A.phdrs

/-! ## The loader's readers (`DynElf`) -/

def Task.dynInfo_rd : Prop :=
  ∀ (F : Blob) (A : File), Parses F A → A.header.machine = 62 → A.isDynamic →
    Silmaril.Elf.Link.DynElf.Elf.dynInfo.run (blobRead F) = some (dynInfoOf A)

def Task.lookup_rd : Prop :=
  ∀ (F : Blob) (A : File) r plt, Parses F A → A.header.machine = 62 → A.DynConsistent →
    A.GnuHashOk →
    (Silmaril.Elf.Link.DynElf.Elf.lookupDef (dynInfoOf A) r.toDyn plt).run (blobRead F) =
      (A.lookupDef r plt).map (Option.map Def.toDyn)

def Task.needed_rd : Prop :=
  ∀ (F : Blob) (A : File) ns, Parses F A → A.header.machine = 62 →
    (Silmaril.Elf.Link.DynElf.Elf.needed (dynInfoOf A)).run (blobRead F) = some ns → ns = A.needed.map toDynName

def Task.relas_rd : Prop :=
  ∀ (F : Blob) (A : File) a j, Parses F A → A.header.machine = 62 → A.DynConsistent →
    (Silmaril.Elf.Link.DynElf.Elf.relas (dynInfoOf A)).run (blobRead F) = some (a, j) →
    (A.relocs .dynamic).map relocKey = (a ++ j).map fun r => (r.off, r.kind, r.sym, some r.addend)

/-! ## `ElfBind` -/

def Task.bound_iff : Prop :=
  ∀ (F : Blob) (A : File) (s : Sel) v, Parses F A → A.header.machine = 62 → A.DynConsistent →
    A.GnuHashOk →
    (Silmaril.Elf.Link.ElfBind.Bound F s.toBind v ↔ ∃ d, A.select s = some (some d) ∧ d.value = v ∧ d.ifunc = false)

def Task.codeAt_iff : Prop :=
  ∀ (F : Blob) (A : File) v code, Parses F A → A.header.machine = 62 →
    (Silmaril.Elf.Link.ElfBind.CodeAt F v code ↔ CodeAt F v code)

/-- (`e_phentsize = 56` is needed: a file with no program headers and another `e_phentsize`,
an `ET_REL` for instance, parses with `phdrs = []`, so the API's `Placement` holds vacuously for
the right `e_type`, while `DynElf.Elf.phdrs` fails on it and `ElfBind.Placement` does not.) -/
def Task.placement_iff : Prop :=
  ∀ (F : Blob) (A : File) (base : Word), Parses F A → A.header.machine = 62 →
    A.header.programEntrySize = 56 →
    (Silmaril.Elf.Link.ElfBind.Placement F base ↔ Placement F base.toNat)

/-! ## Loading models -/

/-- Under lazy binding the loader also writes `GOT[1]` and `GOT[2]` (`DT_PLTGOT + 8`, `+ 16`,
`elf_machine_runtime_setup`): they miss every read-only `PT_LOAD`. -/
def NoLazyGotRo (A : File) : Prop :=
  ∀ p, A.dynTag 3 = some p → ∀ q ∈ [p + 8, p + 16], ∀ ph ∈ A.loads, ph.flags / 2 % 2 = 0 →
    q + 8 ≤ ph.virtualAddress ∨ ph.virtualAddress + ph.memorySize ≤ q

/-- **`ExeLoaded` ⊑ `RoLoaded`**: the loader relation for an executable places its read-only
segments, when no loader write touches them (`NoTextRel`, and `NoLazyGotRo` under lazy
binding) and the file is placed at the base (`ElfBind.Placement`: `p_filesz ≤ p_memsz`, below
`2^47`).

Corrected from the skeleton's statement, which had only `NoTextRel` and was not provable: the
lazily written `GOT[1]`/`GOT[2]` are no relocation, a segment with `p_filesz > p_memsz` has file
bytes `ExeLoaded` does not constrain, and `RoLoaded`'s zero-length reads need the bound of
`Placement`. PROVED from `Task.dynInfo_rd` and `Task.relas_rd` (`Exe.roLoaded_task`); the
`DynElf`-level form (`Exe.roLoaded_of_exeLoaded`, under the decidable `Exe.NoTextRelD`) is
proved outright. -/
def Task.roLoaded_of_exeLoaded : Prop :=
  ∀ (F : Blob) (A : File) fs b bs ifn lazy res (mem : Memory), Parses F A → A.header.machine = 62 →
    A.isDynamic → A.DynConsistent → NoTextRel A → (lazy = true → NoLazyGotRo A) →
    Silmaril.Elf.Link.ElfBind.Placement F b →
    Silmaril.Elf.Link.Dyn.ExeLoaded (F :: fs) (b :: bs) ifn lazy res mem → Silmaril.Elf.Link.ElfBind.RoLoaded F b mem

/-! ## Trust: checking an emitted parse -/

/-- **A parse checker**: a decision procedure on a file and a candidate AST (the parse builder's
direct decoders over pieces), with its soundness. A row proved through a checker names it. -/
structure Checker where
  name : String
  check : Blob → File → Bool
  sound : ∀ F A, check F A = true → Parses F A

/-- The parse builder's goal: a checker that the kernel runs on libc (2 MB) within budget. -/
def Task.check_sound : Prop := Nonempty Checker

end Silmaril.Elf.Bridge
