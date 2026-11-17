module

public import Silmaril.Elf.Image.Defs
public import Silmaril.Process.Memory

/-! # ELF adapters for loaded code and data (`Silmaril.Elf.Load`)

ELF-only facts that a statement about a function of a file needs next to `CodeAt`, each read
from the file through the parse specification:

| name | statement |
|---|---|
| `ReadOnlyAt F v bytes` | the first readable, non-writable `PT_LOAD` mapping `[v, v + n)` holds `bytes` from the file (as `CodeAt` for code; constant tables, strings) |
| `File.loadRanges A`, `LoadRangesAre F rs` | the image: every `PT_LOAD` as `(p_vaddr, p_memsz)` |
| `baseName`, `File.definesFn`, `File.definesName` | presence by name in `.symtab` and `.dynsym`, every version (`name@VER` and `name@@VER` in `.symtab` count as `name`) |
| `PresentFn F n`, `AbsentName F n` | some table defines a function (`STT_FUNC`, `STT_GNU_IFUNC`) named `n`; no table defines any symbol named `n` |
| `ImageLoaded F A base mem` | `mem` holds the image of `F` at load base `base` wherever no dynamic relocation writes: file bytes for file-backed bytes, zeros for zero fill |

`Image.Untouched` (no dynamic relocation writes a range, by the width each relocation type
writes) is the relocation side, and `Thms.loaded_of_segBytes` the bridge: in a memory with the
image loaded, an untouched range of a segment holds the file's bytes at `base + v`.

**What `ImageLoaded` is not.** It is a property of a memory, and nothing here says a loader
produced it: neither `Placement F base` (which only says which bases a statement covers) nor
anything else in this module runs ld.so. A statement about a process takes `ImageLoaded` as a
hypothesis, or derives it from a loading model (`Silmaril.Elf.Link.ElfBind.RoLoaded`,
`Dyn.Loader.ExeLoaded`). Bytes a relocation writes are left unconstrained, so a relocated image
(any relocation values) satisfies it.

**What the relocation widths cover.** `Image.Untouched` is relative to the relocation *records*
(`File.relocs .dynamic`, `RELR` expanded) and the bytes each record's type writes. For
`R_X86_64_COPY` the width is the destination symbol's `st_size` in this file: ld.so copies
`min(st_size of the definition, st_size here)` bytes, so this is an upper bound whatever the
definition resolves to. It says nothing about other writes during loading or start-up:
`IRELATIVE` resolvers and constructors run code (which may write anything), `PT_GNU_RELRO` and
`mprotect` change permissions, and a lazy `JUMP_SLOT` is written later (at its own offset, which
the width covers). A statement that memory equals the file bytes after a real load takes these as
assumptions (`ImageLoaded`); nothing here proves loader non-interference.

**Overlapping segments.** The parse does not reject overlapping `PT_LOAD`s. `ReadOnlyAt` takes the
*first* read-only segment mapping the range; it does not show that no writable segment maps the
same addresses. `Image.Unambiguous A v n` (decidable) says every byte of the range has exactly one
origin; combine the two to exclude overlap. `ImageLoaded` asks every origin of a byte to hold, so
on a file whose overlapping segments disagree it is unsatisfiable and a statement conditional on
it is vacuous there. Its satisfiability (that a memory loading the image exists) is not proved
here; for a file whose load ranges are all `Unambiguous` (checked for the leaf-arith sample,
`Asm.Example.LeafArith.image_unambiguous`) the origins cannot disagree.

**Versioned lookup.** `Silmaril.Elf.Lookup` (`Sel.dyn ⟨name, weak, ver⟩`) is ld.so's
`do_lookup_x` through the GNU hash table, with glibc's `check_match` (`File.checkMatch`):

* the symbol must be defined (or `STT_TLS`, or `SHN_ABS`), not undefined for a PLT reference, of
  type `NOTYPE`, `OBJECT`, `FUNC`, `COMMON`, `TLS` or `GNU_IFUNC`, with the reference's name;
* **a versioned reference** `ver = some v` matches a definition whose version (`versym & 0x7fff`,
  through `.gnu.version_d`) is `v` (hash and name), and otherwise only a definition that has no
  version hash, is not hidden (`versym & 0x8000` clear), when `v` itself is not hidden;
* **an unversioned reference** `ver = none` matches a definition of version index 0, 1 or 2 (local,
  global, the base version); a definition of a later version makes the lookup **refuse** (`none`:
  glibc's `num_versions` fallback, which accepts the default `@@` version, is not modelled), so no
  fact is stated rather than a wrong one;
* an object without `DT_GNU_HASH` is refused too.

The definition a lookup returns (`Def`) records the index, value, size, `IFUNC` and `SHN_ABS`, not
the symbol type: `LookupFn` adds that the entry is a function. Presence by name (`definesFn`,
`definesName`) ignores versions entirely.
-/

@[expose] public section

namespace Silmaril.Elf.Load

open Silmaril.Formats.ELF (ProgramHeader NameBytes)
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.Elf.Image
open Silmaril.X86.Link (Blob)

/-! ## Read-only data -/

/-- `ph` is a readable (`PF_R`), non-writable `PT_LOAD` mapping `[v, v + len)` from the file. -/
def roSeg (v len : Nat) (ph : ProgramHeader) : Bool :=
  ph.kind == PT_LOAD && ph.flags / 2 % 2 == 0 && ph.flags / 4 % 2 == 1 &&
    decide (ph.virtualAddress ≤ v) && decide (v + len ≤ ph.virtualAddress + ph.fileSize)

/-- **`F` holds `bytes` read-only at `v`**: the first readable, non-writable `PT_LOAD` mapping the
range maps them from the file (as `CodeAt`, which asks for an executable segment). -/
def ReadOnlyAt (F : Blob) (v : Nat) (bytes : List (BitVec 8)) : Prop :=
  ∃ A, Parses F A ∧ ∃ ph, A.phdrs.find? (roSeg v bytes.length) = some ph ∧
    blobRead F (ph.offset + (v - ph.virtualAddress)) bytes.length = some (Blob.valueLE bytes)

/-! ## The image -/

/-- **The image of `A`**: every `PT_LOAD` as `(p_vaddr, p_memsz)`, in program-header order. -/
def _root_.Silmaril.Elf.File.loadRanges (A : File) : List (Nat × Nat) :=
  A.loads.map fun ph => (ph.virtualAddress, ph.memorySize)

/-- **The image of `F` is `rs`.** -/
def LoadRangesAre (F : Blob) (rs : List (Nat × Nat)) : Prop :=
  ∃ A, Parses F A ∧ A.loadRanges = rs

/-! ## Presence by name -/

/-- A symbol name without its version suffix (`name@VER`, `name@@VER` as `.symtab` spells
versioned definitions). -/
def baseName (n : NameBytes) : NameBytes := n.takeWhile (· != 0x40)

/-- Some table (`.symtab`, `.dynsym`) **defines a function** named `n` (any version):
`st_shndx ≠ SHN_UNDEF`, `STT_FUNC` or `STT_GNU_IFUNC`. -/
def _root_.Silmaril.Elf.File.definesFn (A : File) (n : NameBytes) : Bool :=
  [Table.symtab, Table.dynsym].any fun t => (A.symbols t).any fun s =>
    baseName s.name == n && s.raw.sectionIndex != 0 && (s.kind == 2 || s.kind == 10)

/-- Some table **defines any symbol** named `n` (any version, any type). -/
def _root_.Silmaril.Elf.File.definesName (A : File) (n : NameBytes) : Bool :=
  [Table.symtab, Table.dynsym].any fun t => (A.symbols t).any fun s =>
    baseName s.name == n && s.raw.sectionIndex != 0

/-- **`F` defines a function named `n`** in some symbol table, in some version. -/
def PresentFn (F : Blob) (n : NameBytes) : Prop := ∃ A, Parses F A ∧ A.definesFn n = true

/-- **`F` defines no symbol named `n`**, in no table and no version (an API version gap). -/
def AbsentName (F : Blob) (n : NameBytes) : Prop := ∃ A, Parses F A ∧ A.definesName n = false

/-- `.symtab` entry or `.dynsym` entry `i` is a function (`STT_FUNC` or `STT_GNU_IFUNC`). -/
def _root_.Silmaril.Elf.File.funcAt (A : File) (t : Table) (i : Nat) : Bool :=
  match (A.symbols t)[i]? with
  | some s => s.kind == 2 || s.kind == 10
  | none => false

/-- The table a selector's definition index refers to (`.fn` falls back to `.symtab` only when
the dynamic lookup finds nothing; its index is then a `.symtab` index). -/
def selTable : Sel → Table
  | .dyn _ => .dynsym
  | .sym _ => .symtab
  | .fn _ => .dynsym

/-- **The lookup `sel` finds the function `d`**: it finds `d`, and the symbol entry it found is
a function (`STT_FUNC`, `STT_GNU_IFUNC`). ld.so's `.dynsym` lookup also accepts `STT_OBJECT`,
`STT_NOTYPE`, `STT_COMMON` and `STT_TLS` definitions, so for `.dyn` this is a separate fact; for
`.sym` it follows from the lookup (`Thms.lookupFn_sym`). -/
def LookupFn (F : Blob) (sel : Sel) (d : Def) : Prop :=
  Lookup F sel (some d) ∧ ∃ A, Parses F A ∧ A.funcAt (selTable sel) d.index = true

/-! ## A memory holding the loaded image -/

/-- **`mem` holds the image of `F` (parse `A`) loaded at `base`**, wherever no dynamic relocation
writes: at `base + u`, the file byte for every file-backed byte `u` of a `PT_LOAD`, and zero for
every zero-filled one (module doc: a property of a memory, not a loader run). -/
def ImageLoaded (F : Blob) (A : File) (base : Nat) (mem : Silmaril.Process.Memory) : Prop :=
  ∀ u i o, Untouched A u 1 →
    ((i, Origin.file o) ∈ A.origins u → mem.bytes.get? (base + u) = some (Blob.byteAt F.n o)) ∧
    ((i, Origin.zeroFill) ∈ A.origins u → mem.bytes.get? (base + u) = some 0)

end Silmaril.Elf.Load
