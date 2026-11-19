module

public import Silmaril.Proofs.Elf.Abi.ZlibMatrix.Common
public import Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc.Thms

/-! # The zlib library matrix, `Libz131Gcc`: the file facts of the rows

Each one a kernel read on the file's kernel bytes, or a computation on the parse it gives. -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.ZlibLibz131Gcc
open Silmaril.Elf.Abi
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib (zProto wProto)
open Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz131Gcc
open Silmaril.Elf.Abi.ZlibMatrix (hdr zlib129 bind frame)
open Silmaril.Elf.Abi.ZlibMatrix.Libz131Gcc
open Silmaril.Proofs.Elf.Abi.ZlibMatrix

abbrev A0 : File := L.assemble bodies ld

theorem image_eq : image = A0.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize) := by
  decide +kernel

/-- The read-only data `PT_LOAD` holds `rodata`. -/
theorem crcData_mapped : ∀ d ∈ crcData, MappedAt F d.1.toNat d.2 := by
  intro d hd
  simp only [crcData, List.mem_singleton] at hd
  subst hd
  exact ⟨_, parses, ph2, by decide +kernel, sub_kbytes K.wf_true K.toByteArray_eq _ _ _ (by decide +kernel)⟩

theorem crcData_untouched : ∀ d ∈ crcData, missesAllB A0 8 d.1.toNat d.2.length = true := by
  intro d hd
  simp only [crcData, List.mem_singleton] at hd
  subst hd
  decide +kernel

/-- The file is x86-64, and every dynamic relocation is 8 bytes (`GLOB_DAT`, `JUMP_SLOT`,
`RELATIVE`). -/
theorem machine_x86_64 : A0.header.machine = EM_X86_64 := by decide +kernel

theorem reloc_width : widthsB A0 8 = true := by
  decide +kernel

theorem reloc_kinds : (A0.relocs .dynamic).all (fun r => [6, 7, 8].contains r.kind) = true := by
  decide +kernel

theorem crc32z_code : CodeOf F (.dynsym (some zlib129)) "crc32_z" crc32zCode :=
  codeOf parses _ _ _ 26 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    crcData_mapped image_eq

theorem crc32z_untouched : Untouched F crc32zCode :=
  untouched_of parses reloc_width (by decide +kernel) crcData_untouched

theorem crc32z_declared : Declares sysvInt hdr "crc32_z" zProto := declares_of_sig (by decide +kernel)

theorem adler32z_code : CodeOf F (.dynsym (some zlib129)) "adler32_z" adler32zCode :=
  codeOf parses _ _ _ 38 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    (fun _ h => nomatch h) image_eq

theorem adler32z_untouched : Untouched F adler32zCode :=
  untouched_of parses reloc_width (by decide +kernel) (fun _ h => nomatch h)

theorem adler32z_declared : Declares sysvInt hdr "adler32_z" zProto := declares_of_sig (by decide +kernel)

/-- The file is `ET_DYN` and admits the load base `0`. -/
theorem placement_zero_ok : Placement F 0 :=
  ⟨_, parses, .inr ⟨by decide +kernel, rfl⟩, fun ph h => by revert ph; decide +kernel⟩

theorem coverage_check : coverage.check sysvInt hdr = true := by decide +kernel

theorem excluded_ok : ∀ e ∈ coverage.excluded,
    (match e.2 with
      | .absent _ => absentB A0 e.1
      | .unclaimed _ => presentB A0 e.1
      | _ => false) = true := by
  decide +kernel

theorem crc32z_of (h : Task.crc32z) : silmaril.elf.abi.zlib_libz_1_3_1_gcc.crc32_z :=
  row crc32z_code crc32z_untouched placement_zero_ok h

theorem adler32z_of (h : Task.adler32z) : silmaril.elf.abi.zlib_libz_1_3_1_gcc.adler32_z :=
  row adler32z_code adler32z_untouched placement_zero_ok h

theorem header_of (h0 : Task.crc32z) (h1 : Task.adler32z) :
    silmaril.elf.abi.zlib_libz_1_3_1_gcc.zlib_h := by
  refine ⟨by decide, coverage_check, fun _ _ h => absent_of parses (excluded_ok _ h),
    fun _ _ h => present_of parses (excluded_ok _ h), fun f hf => ?_⟩
  simp only [coverage, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨_, rfl, crc32z_of h0⟩
  · exact ⟨_, rfl, adler32z_of h1⟩

end Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz131Gcc

end
