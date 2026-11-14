module

public import Silmaril.Process.CLI.Input

/-! # The program-header table of a static `ET_EXEC` image

A statically linked musl (or glibc) executable finds its own program headers at
startup through the auxiliary vector: `AT_PHDR` (address), `AT_PHENT` (entry size)
and `AT_PHNUM` (count). musl's `static_init_tls` scans them for `PT_TLS` and copies
the TLS initializer it names. If the loader relation let `AT_PHDR`/`AT_PHNUM` point
anywhere, a launch could feed startup a forged table (erebor-lean #70). This module
derives the table from the image's own file bytes, so a launch can be required to
name exactly it.

`Image.headerTable?` reads the ELF header from the start of the **first** segment's
file bytes. `StaticHeaders image t` then checks, decidably, that

* the table has at least one entry, lies inside those file bytes, and its mapped
  span does not wrap the address space; the first segment is readable and its file
  bytes fit in its memory size;
* its `PT_LOAD` entries are exactly the image's segments, in order (address, memory
  size, file size, permissions), and the first one is at file offset `0`: so the
  first segment really is the start of the file and the table bytes are the file's;
* a `PT_PHDR` entry, if any, names the table's own address and size (musl computes
  its load base from it);
* every `PT_TLS` entry is sane (`TlsOk`): `p_filesz ≤ p_memsz ≤ 2^32`, a power-of-two
  alignment of at most `2^32`, no wrap, and an initializer that lies inside the file
  bytes of one of the image's segments (provenance).

`Image.StaticTable image t` is both. Linux computes `AT_PHDR` the same way for these
images (`fs/binfmt_elf.c`, `load_elf_binary`: the `PT_LOAD` containing `e_phoff`,
here the one at file offset `0`, plus `e_phoff`).

**Trust.** The field offsets are those of the System V gABI (`Elf64_Ehdr`,
`Elf64_Phdr`). An image whose first segment is not the start of its file is outside
this profile (`headerTable? = none`): it has no static launch.
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.Process

/-- The little-endian value of a byte list. -/
def leNat : List Byte → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * leNat rest

/-- The `width`-byte little-endian field at `offset`. -/
def leField (bytes : List Byte) (offset width : Nat) : Nat :=
  leNat ((bytes.drop offset).take width)

namespace Elf

/-- `\x7fELF`. -/
def magic : List Byte := [0x7f, 0x45, 0x4c, 0x46]
def classElf64 : Nat := 2
def dataLsb : Nat := 1
def typeExec : Nat := 2
def machineX86_64 : Nat := 62
def ptLoad : Nat := 1
def ptPhdr : Nat := 6
def ptTls : Nat := 7
/-- `sizeof (Elf64_Phdr)`. -/
def phentSize : Nat := 56
/-- The x86-64 page size, `AT_PAGESZ`. -/
def pageSize : Nat := 4096
/-- The bound on a `PT_TLS` size and alignment in this profile. -/
def tlsLimit : Nat := 2 ^ 32

end Elf

/-- An `Elf64_Phdr`, without `p_paddr`. -/
structure ProgramHeader where
  type : Nat
  flags : Nat
  offset : Nat
  vaddr : Nat
  filesz : Nat
  memsz : Nat
  align : Nat
  deriving DecidableEq, Repr

/-- Decode one 56-byte entry (gABI field offsets 0, 4, 8, 16, 32, 40, 48). -/
def ProgramHeader.parse (bytes : List Byte) : ProgramHeader :=
  ⟨leField bytes 0 4, leField bytes 4 4, leField bytes 8 8, leField bytes 16 8,
    leField bytes 32 8, leField bytes 40 8, leField bytes 48 8⟩

/-- `PF_R = 4`, `PF_W = 2`, `PF_X = 1`. -/
def ProgramHeader.permissions (header : ProgramHeader) : Permissions :=
  ⟨header.flags.testBit 2, header.flags.testBit 1, header.flags.testBit 0⟩

/-- The table as the first segment's file bytes give it. -/
structure HeaderTable where
  /-- The virtual address of the first segment, which starts at file offset `0`. -/
  base : Nat
  /-- The first segment's file bytes (the start of the file). -/
  fileBytes : List Byte
  /-- `e_phoff`. -/
  offset : Nat
  /-- `e_phnum`. -/
  count : Nat
  deriving DecidableEq

namespace HeaderTable

/-- Where the table is mapped: `AT_PHDR`. -/
def address (table : HeaderTable) : Nat := table.base + table.offset

/-- The table's size in bytes: `AT_PHNUM * AT_PHENT`. -/
def size (table : HeaderTable) : Nat := table.count * Elf.phentSize

/-- The table's bytes, from the file. -/
def bytes (table : HeaderTable) : List Byte := (table.fileBytes.drop table.offset).take table.size

/-- The decoded entries. -/
def entries (table : HeaderTable) : List ProgramHeader :=
  (List.range table.count).map fun k =>
    ProgramHeader.parse ((table.bytes.drop (k * Elf.phentSize)).take Elf.phentSize)

end HeaderTable

/-- The ELF header at the start of the first segment, if it is a little-endian
64-bit x86-64 `ET_EXEC` header with 56-byte program-header entries. -/
def Image.headerTable? (image : Image) : Option HeaderTable :=
  match image.segments with
  | [] => none
  | segment :: _ =>
    let b := segment.fileBytes
    if b.take 4 = Elf.magic ∧ leField b 4 1 = Elf.classElf64 ∧ leField b 5 1 = Elf.dataLsb ∧
        leField b 16 2 = Elf.typeExec ∧ leField b 18 2 = Elf.machineX86_64 ∧
        leField b 54 2 = Elf.phentSize then
      some ⟨segment.vaddr, b, leField b 32 8, leField b 56 2⟩
    else none

/-- A `PT_TLS` entry that musl's `static_init_tls` can use without overflow, whose
initializer `[p_vaddr, p_vaddr + p_filesz)` comes from some segment's file bytes. -/
def TlsOk (image : Image) (header : ProgramHeader) : Prop :=
  header.filesz ≤ header.memsz ∧ header.memsz ≤ Elf.tlsLimit ∧
    header.vaddr + header.memsz ≤ addressLimit ∧
    header.align &&& (header.align - 1) = 0 ∧ header.align ≤ Elf.tlsLimit ∧
    ∃ segment ∈ image.segments,
      segment.vaddr ≤ header.vaddr ∧ header.vaddr + header.filesz ≤ segment.vaddr + segment.fileBytes.length

instance (image : Image) (header : ProgramHeader) : Decidable (TlsOk image header) := by
  unfold TlsOk; infer_instance

/-- The shape a `PT_LOAD` entry gives a segment. -/
def ProgramHeader.loadShape (header : ProgramHeader) : Nat × Nat × Nat × Permissions :=
  (header.vaddr, header.memsz, header.filesz, header.permissions)

/-- The shape of an image segment. -/
def Segment.shape (segment : Segment) : Nat × Nat × Nat × Permissions :=
  (segment.vaddr, segment.memSize, segment.fileBytes.length, segment.permissions)

/-- The derived table is the image's own (see the module docstring). -/
def StaticHeaders (image : Image) (table : HeaderTable) : Prop :=
  1 ≤ table.count ∧
  table.offset + table.size ≤ table.fileBytes.length ∧
  (image.segments.head?.map fun s => (s.permissions.read, decide (s.fileBytes.length ≤ s.memSize))) =
    some (true, true) ∧
  table.address + table.size ≤ addressLimit ∧
  ((table.entries.filter fun h => h.type == Elf.ptLoad).map ProgramHeader.loadShape =
    image.segments.map Segment.shape) ∧
  ((table.entries.filter fun h => h.type == Elf.ptLoad).head?.map ProgramHeader.offset = some 0) ∧
  (∀ h ∈ table.entries, h.type = Elf.ptPhdr → h.vaddr = table.address ∧ h.memsz = table.size) ∧
  (∀ h ∈ table.entries, h.type = Elf.ptTls → TlsOk image h)

instance (image : Image) (table : HeaderTable) : Decidable (StaticHeaders image table) := by
  unfold StaticHeaders; infer_instance

/-- `table` is the program-header table of `image`, derived from its bytes and checked. -/
def Image.StaticTable (image : Image) (table : HeaderTable) : Prop :=
  image.headerTable? = some table ∧ StaticHeaders image table

instance (image : Image) (table : HeaderTable) : Decidable (image.StaticTable table) := by
  unfold Image.StaticTable; infer_instance

/-! ## Facts -/

theorem Image.StaticTable.unique {image : Image} {first second : HeaderTable}
    (h₁ : image.StaticTable first) (h₂ : image.StaticTable second) : first = second := by
  have := h₁.1.symm.trans h₂.1
  exact Option.some.inj this

/-- The table is the start of the first segment, which is an image segment. -/
theorem Image.headerTable?_segment {image : Image} {table : HeaderTable}
    (h : image.headerTable? = some table) :
    ∃ segment, image.segments.head? = some segment ∧ segment.vaddr = table.base ∧
      segment.fileBytes = table.fileBytes := by
  unfold Image.headerTable? at h
  split at h
  · exact absurd h (by simp)
  · rename_i segment rest heq
    dsimp only at h
    split at h
    · cases h
      exact ⟨segment, by rw [heq]; rfl, rfl, rfl⟩
    · exact absurd h (by simp)

/-- The table's bytes are the first segment's file bytes at `e_phoff`, in full. -/
theorem HeaderTable.bytes_length {table : HeaderTable}
    (fits : table.offset + table.size ≤ table.fileBytes.length) :
    table.bytes.length = table.size := by
  simp only [HeaderTable.bytes, List.length_take, List.length_drop]
  omega

end Silmaril.Process.CLI
