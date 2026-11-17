module

public import Silmaril.Elf.Facts.Defs
public import Silmaril.Elf.Staged.Defs

/-! # File offsets, virtual addresses, load addresses and zero fill (`Silmaril.Elf.Image`)

Four address spaces meet in an ELF file, and a statement must say which one it is about:

| space | what it indexes | where it comes from |
|---|---|---|
| file offset | the bytes of the file (`blobRead F o w`) | `p_offset`, `sh_offset` |
| virtual address | the link-time image (`p_vaddr`, `st_value`, `e_entry`) | the file's metadata |
| load address | memory after loading at a base | `base + v` for `ET_DYN`, `v` for `ET_EXEC` (`Placement`) |
| zero fill | addresses in `[p_vaddr + p_filesz, p_vaddr + p_memsz)` (`.bss`) | no file byte at all |

* `segOrigin ph v`: where the byte at virtual address `v` comes from in one segment: a file
  offset (`Origin.file o`), zero fill (`Origin.zeroFill`), or nothing (`none`, not mapped by it).
* `File.origins A v`: **every** `PT_LOAD` that maps `v`, by program-header index. The parse does not
  reject overlapping segments, so this is a list: `[]` (unmapped), one entry, or several
  (`File.resolve`: `unmapped | unique | ambiguous`). Nothing here picks one silently; the first-match
  conventions of `CodeAt` (`List.find?`) and of `Staged.Layout.offsetOf` are related to it by
  theorems (`Thms`), and agree with it exactly when the mapping is unique.
* `MapsFile A i v len o`: program header `i` is a `PT_LOAD` that maps the `len` bytes at `v` from
  the file bytes at offset `o` (all of them file-backed: none zero fill).
* `FileBytes F o bytes`: the file holds `bytes` at offset `o` — a statement about the file, not
  about memory.
* `SegBytes F A i v o bytes`: both: segment `i` of the parse `A` maps `bytes`, which the file holds
  at `o`, to `v`.
* `SecBytes F A k v o bytes`: the same through section `k` (`sh_addr`, `sh_offset`), the only
  relation a relocatable object (`ET_REL`, no program headers) has.
* `Untouched A v len`: no dynamic relocation writes into `[v, v + len)`, each relocation by the
  number of bytes its type writes (`File.relocWidth`: the x86-64 psABI field widths, 16 for
  `R_X86_64_TLSDESC`, the symbol's size for `R_X86_64_COPY`). A relocation whose width is not
  known (another machine, an unlisted type, a `COPY` whose symbol cannot be read) makes every range
  touched: nothing is assumed about it. Without `Untouched`, memory after loading need not hold
  the file bytes: the loader patches relocated words. Statements about loaded memory take it (or a
  loading model, `Silmaril.Elf.Link.ElfBind`) as a hypothesis.

Not modelled: page granularity (the loader maps whole pages, so bytes outside `[p_offset,
p_offset + p_filesz)` on the same page are visible in memory; nothing here claims anything about
them), `p_filesz > p_memsz` (treated as mapping the file bytes; `Placement` excludes it), and
permissions beyond the read/execute bits `CodeAt` already checks.
-/

@[expose] public section

namespace Silmaril.Elf.Image

open Silmaril.Formats.ELF (ProgramHeader)
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.X86.Link (Blob)

/-- `EM_X86_64`, the machine whose relocation widths are known here. -/
def EM_X86_64_MACHINE : Nat := 62

/-- Where a byte of a loaded segment comes from. -/
inductive Origin where
  /-- The file byte at this offset. -/
  | file (off : Nat)
  /-- Zero fill: past `p_filesz`, before `p_memsz`. No file byte. -/
  | zeroFill
  deriving DecidableEq, Repr

/-- **Where the byte at virtual address `v` comes from in segment `ph`**, if `ph` maps it. -/
def segOrigin (ph : ProgramHeader) (v : Nat) : Option Origin :=
  if ph.kind = PT_LOAD ∧ ph.virtualAddress ≤ v then
    if v < ph.virtualAddress + ph.fileSize then some (.file (ph.offset + (v - ph.virtualAddress)))
    else if v < ph.virtualAddress + ph.memorySize then some .zeroFill
    else none
  else none

/-- **Every segment that maps `v`**, by program-header index, with the origin each gives. -/
def _root_.Silmaril.Elf.File.origins (A : File) (v : Nat) : List (Nat × Origin) :=
  A.phdrs.zipIdx.filterMap fun (ph, i) => (segOrigin ph v).map ((i, ·))

/-- How a virtual address resolves. -/
inductive Resolution where
  /-- No `PT_LOAD` maps it. -/
  | unmapped
  /-- Exactly one does: program header `i`, with origin `o`. -/
  | unique (i : Nat) (o : Origin)
  /-- Several do (overlapping segments): every one of them, in program-header order. -/
  | ambiguous (hits : List (Nat × Origin))
  deriving DecidableEq, Repr

/-- **How `v` resolves in `A`.** -/
def _root_.Silmaril.Elf.File.resolve (A : File) (v : Nat) : Resolution :=
  match A.origins v with
  | [] => .unmapped
  | [(i, o)] => .unique i o
  | hs => .ambiguous hs

/-- **Program header `i` maps the `len` bytes at virtual address `v` from file offset `o`**,
every one of them file-backed. -/
def MapsFile (A : File) (i v len o : Nat) : Prop :=
  ∃ ph, A.phdrs[i]? = some ph ∧ ph.kind = PT_LOAD ∧ ph.virtualAddress ≤ v ∧
    v + len ≤ ph.virtualAddress + ph.fileSize ∧ o = ph.offset + (v - ph.virtualAddress)

/-- **The file holds `bytes` at offset `o`** (a fact about the file, not about memory). -/
def FileBytes (F : Blob) (o : Nat) (bytes : List (BitVec 8)) : Prop :=
  blobRead F o bytes.length = some (Blob.valueLE bytes)

/-- **Segment `i` of `A` maps `bytes`, which `F` holds at offset `o`, to virtual address `v`.** -/
def SegBytes (F : Blob) (A : File) (i v o : Nat) (bytes : List (BitVec 8)) : Prop :=
  MapsFile A i v bytes.length o ∧ FileBytes F o bytes

/-- **Section `k` of `A` holds the `len` bytes at address `v` in the file at offset `o`**: it is not
`SHT_NOBITS`, `[v, v + len)` lies in `[sh_addr, sh_addr + sh_size)`, and `o = sh_offset + (v -
sh_addr)`. For `ET_REL`, `sh_addr = 0` and `v` is an offset in the section; this is the only
address relation such a file has (it has no `PT_LOAD`). -/
def SecMapsFile (A : File) (k v len o : Nat) : Prop :=
  ∃ s, A.sections[k]? = some s ∧ s.header.kind ≠ SHT_NOBITS ∧ s.header.address ≤ v ∧
    v + len ≤ s.header.address + s.header.size ∧ o = s.header.offset + (v - s.header.address)

/-- **Section `k` of `A` holds `bytes`, which `F` holds at offset `o`, at address `v`.** -/
def SecBytes (F : Blob) (A : File) (k v o : Nat) (bytes : List (BitVec 8)) : Prop :=
  SecMapsFile A k v bytes.length o ∧ FileBytes F o bytes

/-- **Every byte of `[v, v + len)` resolves uniquely.** -/
def Unambiguous (A : File) (v len : Nat) : Prop :=
  ∀ k, k < len → (A.origins (v + k)).length = 1

instance (A : File) (v len : Nat) : Decidable (Unambiguous A v len) :=
  inferInstanceAs (Decidable (∀ k, k < len → _))

/-- The bytes an x86-64 relocation of type `k` writes (System V AMD64 psABI, Tables 4.10 and the
TLS supplement), when it is a fixed width. `R_X86_64_COPY` (5) is not: see `File.relocWidth`. -/
def x86RelocWidth : Nat → Option Nat
  | 0 => some 0            -- NONE
  | 1 | 6 | 7 | 8 => some 8 -- 64, GLOB_DAT, JUMP_SLOT, RELATIVE
  | 2 | 3 | 4 | 9 | 10 | 11 => some 4 -- PC32, GOT32, PLT32, GOTPCREL, 32, 32S
  | 12 | 13 => some 2      -- 16, PC16
  | 14 | 15 => some 1      -- 8, PC8
  | 16 | 17 | 18 => some 8 -- DTPMOD64, DTPOFF64, TPOFF64
  | 19 | 20 | 21 | 22 | 23 => some 4 -- TLSGD, TLSLD, DTPOFF32, GOTTPOFF, TPOFF32
  | 24 | 25 => some 8      -- PC64, GOTOFF64
  | 26 => some 4           -- GOTPC32
  | 32 => some 4 | 33 => some 8 -- SIZE32, SIZE64
  | 34 => some 4           -- GOTPC32_TLSDESC
  | 35 => some 0           -- TLSDESC_CALL (a marker)
  | 36 => some 16          -- TLSDESC (two words)
  | 37 | 38 => some 8      -- IRELATIVE, RELATIVE64
  | 41 | 42 => some 4      -- GOTPCRELX, REX_GOTPCRELX
  | _ => none

/-- **The bytes the dynamic relocation `r` of `A` writes**, in the footprint model: the x86-64
width of its type, and for `R_X86_64_COPY` the size of its `.dynsym` symbol (the destination in
this file). `none` for any other machine.

`COPY` copies from the definition a lookup resolves in another object. glibc's x86-64
`elf_machine_rela` copies `MIN (sym->st_size, refsym->st_size)` bytes (definition, destination)
and musl copies the destination's `st_size`, so the destination size bounds both. That bound is an
assumption about the loader, not a fact of this file: a loader that copies the definition's size
is outside the supported domain. -/
def _root_.Silmaril.Elf.File.relocWidth (A : File) (r : File.Reloc) : Option Nat :=
  if A.header.machine ≠ EM_X86_64_MACHINE then none
  else if r.kind = 5 then (A.dynsyms[r.symbol]?).map (·.raw.size)
  else x86RelocWidth r.kind

/-- `[o, o + w)` and `[v, v + len)` are disjoint. -/
def Misses (o w v len : Nat) : Bool := decide (o + w ≤ v) || decide (v + len ≤ o)

/-- **No dynamic relocation writes into `[v, v + len)`**, in the footprint model: every relocation
record has a known width (`File.relocWidth`) and its footprint misses the range. A relocation of
unknown width touches every range. This is a fact about the file's relocation records; it says
something about memory after loading only through a loading relation that assumes the loader
writes no more than these footprints (`Load.ImageLoaded`). -/
def Untouched (A : File) (v len : Nat) : Prop :=
  ∀ r ∈ A.relocs .dynamic, ∃ w, A.relocWidth r = some w ∧ Misses r.offset w v len = true

instance (A : File) (v len : Nat) : Decidable (Untouched A v len) :=
  inferInstanceAs (Decidable (∀ r ∈ A.relocs .dynamic, _))

/-- The load address of virtual address `v` at base `base` (`Placement F base` says which bases a
statement covers: `0` for `ET_EXEC`). -/
def loadAddr (base v : Nat) : Nat := base + v

end Silmaril.Elf.Image
