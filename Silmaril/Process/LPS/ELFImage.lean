module

public import Silmaril.Formats.ELF.Reader
public import Silmaril.Process.LPS.Equivalence

/-! # Checked ELF64 bytes to LPS images

This loader uses the shared ELF64 little-endian readers, rather than trusting
an externally extracted image. Machine and address bounds are policy arguments.
The profile is fixed-address ET_EXEC with no interpreter. PT_LOAD contents are
the exact bounded file slice followed by zero-filled BSS; load segments must be
nonempty, disjoint and within the selected address space. Permissions are the
three ELF PF_R/PF_W/PF_X bits. The program-header table must be file-backed by a
readable load segment; its virtual address is derived from that segment.

These are explicit loading rules, not a proof about Linux's loader. Relocation,
ET_DYN, TLS installation, page-rounded permission sharing, overlapping PT_LOADs
and alternate ABI profiles require separate options. Non-load metadata is not
installed, and PT_INTERP is rejected. The independent ISA entry check is made
by `load`; extraction alone never asserts that instruction decoding succeeds.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.ELFImage

open Silmaril.Formats

structure Policy where
  machine : Nat
  headerFlags : Nat
  taskSize : Nat
  deriving DecidableEq, Repr

def x86Policy : Policy := ⟨62, 0, 0x7ffffffff000⟩

/-- RV64 with no compressed/floating-point ELF flags; other profiles can select
different exact flags and task boundaries without changing extraction. -/
def riscvPolicy (taskSize : Nat := 2 ^ 47) : Policy := ⟨243, 0, taskSize⟩

def loadHeaders (headers : List ELF.ProgramHeader) : List ELF.ProgramHeader :=
  headers.filter (fun header => header.kind == 1)

def permissions (flags : Nat) : String :=
  (if flags / 4 % 2 = 1 then "r" else "") ++
  (if flags / 2 % 2 = 1 then "w" else "") ++
  (if flags % 2 = 1 then "x" else "")

/-- Exact file-backed prefix and zero-filled tail; validity excludes truncation
and the subtraction-underflow case before this becomes an accepted image. -/
def segment (file : ELF.Bytes) (header : ELF.ProgramHeader) : Segment :=
  ⟨header.virtualAddress, header.memorySize, permissions header.flags,
    (file.toList.drop header.offset).take header.fileSize ++
      List.replicate (header.memorySize - header.fileSize) 0⟩

def Disjoint (first second : Segment) : Prop :=
  first.base + first.size ≤ second.base ∨ second.base + second.size ≤ first.base

instance (first second : Segment) : Decidable (Disjoint first second) :=
  inferInstanceAs (Decidable (_ ∨ _))

def HeaderSupported (policy : Policy) (header : ELF.Header)
    (headers : List ELF.ProgramHeader) : Prop :=
  header.machine = policy.machine ∧ header.fileType = 2 ∧ header.version = 1 ∧
    (header.osABI = 0 ∨ header.osABI = 3) ∧ header.abiVersion = 0 ∧
    header.flags = policy.headerFlags ∧ header.headerSize = 64 ∧
    header.programEntrySize = 56 ∧ 0 < header.programCount ∧
    header.programCount = headers.length ∧
    ∀ ph ∈ headers, ph.kind ≠ 3

instance (policy : Policy) (header : ELF.Header) (headers : List ELF.ProgramHeader) :
    Decidable (HeaderSupported policy header headers) := by
  unfold HeaderSupported
  infer_instance

/-- The bit test accepts zero/one or a power-of-two alignment. Congruence is
checked both for the declared alignment and for the Linux 4096-byte page size. -/
def ValidLoad (policy : Policy) (file : ELF.Bytes) (header : ELF.ProgramHeader) : Prop :=
  header.kind = 1 ∧ header.flags < 8 ∧ header.fileSize ≤ header.memorySize ∧
    header.offset + header.fileSize ≤ file.size ∧ 0 < header.memorySize ∧
    header.virtualAddress + header.memorySize ≤ policy.taskSize ∧
    Nat.land header.alignment (header.alignment - 1) = 0 ∧
    (header.alignment ≤ 1 ∨ header.virtualAddress % header.alignment = header.offset % header.alignment) ∧
    header.virtualAddress % 4096 = header.offset % 4096

instance (policy : Policy) (file : ELF.Bytes) (header : ELF.ProgramHeader) :
    Decidable (ValidLoad policy file header) := by
  unfold ValidLoad
  infer_instance

def HoldsPhdrTable (header : ELF.Header) (owner : ELF.ProgramHeader) : Prop :=
  owner.kind = 1 ∧ owner.flags / 4 % 2 = 1 ∧
    owner.offset ≤ header.programOffset ∧
    header.programOffset + header.programEntrySize * header.programCount ≤ owner.offset + owner.fileSize

instance (header : ELF.Header) (owner : ELF.ProgramHeader) :
    Decidable (HoldsPhdrTable header owner) := by
  unfold HoldsPhdrTable
  infer_instance

structure Records where
  header : ELF.Header
  programHeaders : List ELF.ProgramHeader
  phdrOwner : ELF.ProgramHeader
  deriving DecidableEq, Repr

def Records.image (records : Records) (file : ELF.Bytes) : Image :=
  ⟨(loadHeaders records.programHeaders).map (segment file), records.header.entry,
    ⟨records.phdrOwner.virtualAddress + (records.header.programOffset - records.phdrOwner.offset),
      records.header.programEntrySize, records.header.programCount⟩⟩

def RecordsValid (policy : Policy) (file : ELF.Bytes) (records : Records) : Prop :=
  HeaderSupported policy records.header records.programHeaders ∧
    records.phdrOwner ∈ records.programHeaders ∧
    HoldsPhdrTable records.header records.phdrOwner ∧
    loadHeaders records.programHeaders ≠ [] ∧
    (∀ ph ∈ loadHeaders records.programHeaders, ValidLoad policy file ph) ∧
    (records.image file).segments.Pairwise Disjoint

instance (policy : Policy) (file : ELF.Bytes) (records : Records) :
    Decidable (RecordsValid policy file records) := by
  unfold RecordsValid
  infer_instance

/-- Byte-to-record extraction checks the parser output and every layout rule.
No plugin, externally generated AST, or trusted extraction equality is used. -/
def parse (policy : Policy) (file : ELF.Bytes) : Option Records := do
  let header ← ELF.readHeader file
  let headers ← ELF.readProgramHeaders file header
  let owner ← headers.find? (fun ph => decide (HoldsPhdrTable header ph))
  let records := Records.mk header headers owner
  if RecordsValid policy file records then some records else none

def Parsed (policy : Policy) (file : ELF.Bytes) (records : Records) : Prop :=
  ELF.readHeader file = some records.header ∧
    ELF.readProgramHeaders file records.header = some records.programHeaders ∧
    RecordsValid policy file records

theorem parse_sound {policy : Policy} {file : ELF.Bytes} {records : Records}
    (parsed : parse policy file = some records) : Parsed policy file records := by
  simp only [parse, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨header, readHeader, headers, readHeaders, owner, _, checked⟩ := parsed
  split at checked
  · cases checked
    exact ⟨readHeader, readHeaders, by assumption⟩
  · contradiction

theorem segment_file_slice (file : ELF.Bytes) (header : ELF.ProgramHeader) :
    (segment file header).bytes =
      (file.toList.drop header.offset).take header.fileSize ++
        List.replicate (header.memorySize - header.fileSize) 0 := rfl

theorem file_slice_length {file : ELF.Bytes} {header : ELF.ProgramHeader}
    (inside : header.offset + header.fileSize ≤ file.size) :
    ((file.toList.drop header.offset).take header.fileSize).length = header.fileSize := by
  simp only [List.length_take, List.length_drop, Array.length_toList]
  omega

theorem segment_length {policy : Policy} {file : ELF.Bytes} {header : ELF.ProgramHeader}
    (valid : ValidLoad policy file header) :
    (segment file header).bytes.length = header.memorySize := by
  simp only [segment, List.length_append, List.length_replicate, file_slice_length valid.2.2.2.1]
  have fits := valid.2.2.1
  omega

theorem segment_file_byte {file : ELF.Bytes} {header : ELF.ProgramHeader} {index : Nat}
    (inside : header.offset + header.fileSize ≤ file.size) (bound : index < header.fileSize) :
    (segment file header).bytes[index]? = file.toList[header.offset + index]? := by
  change (((file.toList.drop header.offset).take header.fileSize) ++ _)[index]? = _
  rw [List.getElem?_append_left (by rw [file_slice_length inside]; exact bound)]
  simp [List.getElem?_drop, bound]

theorem segment_bss_byte {file : ELF.Bytes} {header : ELF.ProgramHeader} {index : Nat}
    (inside : header.offset + header.fileSize ≤ file.size)
    (lower : header.fileSize ≤ index) (upper : index < header.memorySize) :
    (segment file header).bytes[index]? = some 0 := by
  change (((file.toList.drop header.offset).take header.fileSize) ++ _)[index]? = _
  rw [List.getElem?_append_right (by rw [file_slice_length inside]; exact lower)]
  rw [file_slice_length inside]
  simp only [List.getElem?_replicate]
  rw [ite_eq_left (by omega)]

/-- Every loaded segment comes from an actual PT_LOAD record of these bytes,
with its exact file slice/BSS contents. -/
theorem parsed_segment {policy : Policy} {file : ELF.Bytes} {records : Records}
    (parsed : parse policy file = some records) {loaded : Segment}
    (member : loaded ∈ (records.image file).segments) :
    ∃ ph ∈ records.programHeaders, ValidLoad policy file ph ∧ loaded = segment file ph := by
  obtain ⟨ph, member, shape⟩ := List.mem_map.mp member
  exact ⟨ph, (List.mem_filter.mp member).1,
    (parse_sound parsed).2.2.2.2.2.2.1 ph member, shape.symm⟩

theorem parsed_segments_nonempty {policy : Policy} {file : ELF.Bytes} {records : Records}
    (parsed : parse policy file = some records) : (records.image file).segments ≠ [] := by
  intro empty
  exact (parse_sound parsed).2.2.2.2.2.1 (List.map_eq_nil_iff.mp empty)

theorem parsed_segments_disjoint {policy : Policy} {file : ELF.Bytes} {records : Records}
    (parsed : parse policy file = some records) :
    (records.image file).segments.Pairwise Disjoint := (parse_sound parsed).2.2.2.2.2.2.2

theorem parsed_segment_wellformed {policy : Policy} {file : ELF.Bytes} {records : Records}
    (parsed : parse policy file = some records) {loaded : Segment}
    (member : loaded ∈ (records.image file).segments) :
    loaded.bytes.length = loaded.size ∧ 0 < loaded.size ∧
      loaded.base + loaded.size ≤ policy.taskSize := by
  obtain ⟨ph, _, valid, rfl⟩ := parsed_segment parsed member
  exact ⟨segment_length valid, valid.2.2.2.2.1, valid.2.2.2.2.2.1⟩

theorem parsed_phdr_owner_mem {policy : Policy} {file : ELF.Bytes} {records : Records}
    (parsed : parse policy file = some records) :
    segment file records.phdrOwner ∈ (records.image file).segments := by
  have valid := (parse_sound parsed).2.2
  apply List.mem_map.mpr
  exact ⟨records.phdrOwner, List.mem_filter.mpr
    ⟨valid.2.1, by simp [valid.2.2.1.1]⟩, rfl⟩

/-- The whole table, not merely its first byte, lies in its selected loaded
segment. This is the extent needed to transport the byte theorem to memory. -/
theorem parsed_phdr_extent {policy : Policy} {file : ELF.Bytes} {records : Records}
    (parsed : parse policy file = some records) :
    records.header.programOffset - records.phdrOwner.offset +
      records.header.programEntrySize * records.header.programCount ≤ records.phdrOwner.memorySize := by
  have valid := (parse_sound parsed).2.2
  have ownerLoad : records.phdrOwner ∈ loadHeaders records.programHeaders :=
    List.mem_filter.mpr ⟨valid.2.1, by simp [valid.2.2.1.1]⟩
  have fits := (valid.2.2.2.2.1 _ ownerLoad).2.2.1
  have starts := valid.2.2.1.2.2.1
  have ends := valid.2.2.1.2.2.2
  omega

/-- The file bytes occupying the derived AT_PHDR address agree with the input
program-header table, byte by byte, inside the designated load segment. -/
theorem parsed_phdr_byte {policy : Policy} {file : ELF.Bytes} {records : Records}
    (parsed : parse policy file = some records) {index : Nat}
    (bound : index < records.header.programEntrySize * records.header.programCount) :
    (segment file records.phdrOwner).bytes[records.header.programOffset - records.phdrOwner.offset + index]? =
      file.toList[records.header.programOffset + index]? := by
  have valid := (parse_sound parsed).2.2
  have ownerLoad : records.phdrOwner ∈ loadHeaders records.programHeaders := by
    exact List.mem_filter.mpr ⟨valid.2.1, by simp [valid.2.2.1.1]⟩
  have fileBound := (valid.2.2.2.2.1 _ ownerLoad).2.2.2.1
  have starts := valid.2.2.1.2.2.1
  have ends := valid.2.2.1.2.2.2
  rw [segment_file_byte fileBound (by omega)]
  congr 1
  omega

instance (isa : UserIsa) (image : Image) : Decidable (ImageWf isa image) := by
  unfold ImageWf
  infer_instance

/-- A loader option with the existing LPS anti-vacuity checks: entry decoding,
readable program headers, and a satisfiable break. -/
def load (isa : UserIsa) (policy : Policy) (file : ELF.Bytes) : Option Image := do
  let records ← parse policy file
  let image := records.image file
  if ImageWf isa image then some image else none

theorem load_imageWf {isa : UserIsa} {policy : Policy} {file : ELF.Bytes} {image : Image}
    (loaded : load isa policy file = some image) : ImageWf isa image := by
  simp only [load, bind, Option.bind_eq_some_iff] at loaded
  obtain ⟨records, _, checked⟩ := loaded
  split at checked
  · cases checked
    assumption
  · contradiction

theorem load_correspondence {isa : UserIsa} {policy : Policy} {file : ELF.Bytes} {image : Image}
    (loaded : load isa policy file = some image) :
    ∃ records, parse policy file = some records ∧ image = records.image file := by
  simp only [load, bind, Option.bind_eq_some_iff] at loaded
  obtain ⟨records, parsed, checked⟩ := loaded
  split at checked
  · cases checked
    exact ⟨records, parsed, rfl⟩
  · contradiction

end Silmaril.Process.LPS.ELFImage
