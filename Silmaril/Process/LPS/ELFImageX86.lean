module

public import Silmaril.Process.LPS.ELFImage
public import Silmaril.Process.LPS.Machines.X86Launch

/-! # Byte-bound native x86 launch snapshots

This additive bridge derives the existing x86 `Snapshot` from the checked
ELF64 reader. Accepted snapshots satisfy the existing structural launch checks
and LPS anti-vacuity checks. Theorems about input bytes remain about those
bytes: parsed AST records and loaded segment data are not trusted assertions.
The fixed ET_EXEC loading scope is documented in `ELFImage`.

Acceptance does not supply a valid stack/entry choice for every image: a high
load segment can leave insufficient stack space. That obligation remains the
existing `ValidEntry` predicate. `UserIsa` has no architecture tag, so callers
must select an intended x86 ISA option; the machine ID check alone cannot
certify that an arbitrary supplied ISA is an x86 semantics.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.ELFImage

open Silmaril.Formats
open Machines

def Records.x86Snapshot (records : Records) (file : ELF.Bytes) : X86Launch.Snapshot :=
  ⟨records.header, records.programHeaders, records.image file⟩

theorem segment_header_matches {file : ELF.Bytes} {ph : ELF.ProgramHeader}
    (kind : ph.kind = 1) (fits : ph.fileSize ≤ ph.memorySize) :
    X86Launch.ProgramHeaderMatches ph (segment file ph) := by
  by_cases read : ph.flags / 4 % 2 = 1 <;>
    by_cases write : ph.flags / 2 % 2 = 1 <;>
      by_cases execute : ph.flags % 2 = 1 <;>
        simp [X86Launch.ProgramHeaderMatches, segment, permissions, Segment.readable,
          Segment.writable, Segment.executable, kind, fits, read, write, execute]

theorem parsed_header_matches {file : ELF.Bytes} {records : Records}
    (parsed : parse x86Policy file = some records) :
    X86Launch.HeaderMatches (records.x86Snapshot file) := by
  have valid := (parse_sound parsed).2.2
  rcases valid.1 with ⟨machine, fileType, version, abi, abiVersion, flags,
    headerSize, programEntrySize, positive, count, noInterpreter⟩
  exact ⟨machine, fileType, version, abi, abiVersion, flags, headerSize,
    programEntrySize, positive, count, rfl, programEntrySize, rfl, noInterpreter⟩

theorem parsed_loadLayout_matches {file : ELF.Bytes} {records : Records}
    (parsed : parse x86Policy file = some records) :
    X86Launch.LoadLayoutMatches (records.x86Snapshot file) := by
  constructor
  · intro loaded member
    obtain ⟨ph, phMember, valid, shape⟩ := parsed_segment parsed member
    subst loaded
    exact ⟨ph, phMember, segment_header_matches valid.1 valid.2.2.1⟩
  · intro ph member kind
    have inLoads : ph ∈ loadHeaders records.programHeaders :=
      List.mem_filter.mpr ⟨member, by simp [kind]⟩
    have valid := (parse_sound parsed).2.2.2.2.2.2.1 ph inLoads
    exact ⟨segment file ph, List.mem_map.mpr ⟨ph, inLoads, rfl⟩,
      segment_header_matches kind valid.2.2.1⟩

/-- The generic byte loader's checked layout and ISA wellformedness checks
establish the existing x86 snapshot predicate, rather than assuming it. -/
theorem parsed_imageWf_validSnapshot {isa : UserIsa} {file : ELF.Bytes} {records : Records}
    (parsed : parse x86Policy file = some records) (wf : ImageWf isa (records.image file)) :
    X86Launch.ValidSnapshot isa (records.x86Snapshot file) := by
  refine ⟨parsed_header_matches parsed, parsed_loadLayout_matches parsed, ?_,
    parsed_segments_disjoint parsed, wf.1, ?_⟩
  · intro loaded member
    obtain ⟨ph, _, valid, shape⟩ := parsed_segment parsed member
    subst loaded
    refine ⟨segment_length valid, valid.2.2.2.2.1, ?_⟩
    have bound := valid.2.2.2.2.2.1
    change ph.virtualAddress + ph.memorySize ≤ 0x7ffffffff000 at bound
    change (ph.virtualAddress : Int) + ph.memorySize ≤ 0x7ffffffff000
    exact_mod_cast bound
  · have read := wf.2.1
    simp only [imagePhdrsReadable, Bool.and_eq_true] at read
    exact read.2

/-- A checked native x86 snapshot from the actual file bytes. The ISA remains
explicit, so canonical, Wire and oracle options can share byte extraction.
The caller selects an intended x86 ISA; `UserIsa` does not enforce that type. -/
def loadX86 (isa : UserIsa) (file : ELF.Bytes) : Option X86Launch.Snapshot := do
  let records ← parse x86Policy file
  if ImageWf isa (records.image file) then some (records.x86Snapshot file) else none

theorem loadX86_none_of_entry_denied {isa : UserIsa} {file : ELF.Bytes} {records : Records}
    (parsed : parse x86Policy file = some records)
    (denied : isa.entryFetchable (records.image file).segments (records.image file).initPc = false) :
    loadX86 isa file = none := by
  have notWf : ¬ ImageWf isa (records.image file) := by
    intro wf
    exact Bool.false_ne_true (denied.symm.trans wf.1)
  rw [loadX86, parsed]
  change (if ImageWf isa (records.image file) then _ else none) = none
  rw [ite_eq_right notWf]

theorem loadX86_correspondence {isa : UserIsa} {file : ELF.Bytes} {snapshot : X86Launch.Snapshot}
    (loaded : loadX86 isa file = some snapshot) :
    ∃ records, parse x86Policy file = some records ∧ snapshot = records.x86Snapshot file ∧
      ImageWf isa (records.image file) := by
  simp only [loadX86, bind, Option.bind_eq_some_iff] at loaded
  obtain ⟨records, parsed, checked⟩ := loaded
  split at checked
  · cases checked
    exact ⟨records, parsed, rfl, by assumption⟩
  · contradiction

theorem loadX86_validSnapshot {isa : UserIsa} {file : ELF.Bytes} {snapshot : X86Launch.Snapshot}
    (loaded : loadX86 isa file = some snapshot) : X86Launch.ValidSnapshot isa snapshot := by
  obtain ⟨records, parsed, rfl, wf⟩ := loadX86_correspondence loaded
  exact parsed_imageWf_validSnapshot parsed wf

theorem loadX86_imageWf {isa : UserIsa} {file : ELF.Bytes} {snapshot : X86Launch.Snapshot}
    (loaded : loadX86 isa file = some snapshot) : ImageWf isa snapshot.image := by
  obtain ⟨_, _, rfl, wf⟩ := loadX86_correspondence loaded
  exact wf

theorem loadX86_header_from_bytes {isa : UserIsa} {file : ELF.Bytes} {snapshot : X86Launch.Snapshot}
    (loaded : loadX86 isa file = some snapshot) : ELF.readHeader file = some snapshot.header := by
  obtain ⟨_, parsed, rfl, _⟩ := loadX86_correspondence loaded
  exact (parse_sound parsed).1

theorem loadX86_programHeaders_from_bytes {isa : UserIsa} {file : ELF.Bytes} {snapshot : X86Launch.Snapshot}
    (loaded : loadX86 isa file = some snapshot) :
    ELF.readProgramHeaders file snapshot.header = some snapshot.programHeaders := by
  obtain ⟨_, parsed, rfl, _⟩ := loadX86_correspondence loaded
  exact (parse_sound parsed).2.1

end Silmaril.Process.LPS.ELFImage
