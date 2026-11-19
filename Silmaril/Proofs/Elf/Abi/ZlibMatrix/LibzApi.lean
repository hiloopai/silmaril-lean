module

public import Silmaril.Proofs.Elf.Abi.ZlibMatrix.Common
public import Silmaril.Elf.Staged.Pinned.ZlibLibz.Thms
public import Silmaril.Elf.Abi.ZlibLibz.Thms
public import Silmaril.Elf.Abi.ZlibMatrix.Api.Defs

/-! # The zlib.h checksum excerpt in Ubuntu's `libz.so.1.3`: the file facts of the rows -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.ZlibLibz
open Silmaril.Elf.Abi
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib.Api
open Silmaril.Machine.Abi.Conformance.ZlibApi
open Silmaril.Machine.Abi.Conformance.ZlibLibz (crcData image)
open Silmaril.Elf.Abi.ZlibLibz (hdr frame)
open Silmaril.Elf.Abi.ZlibMatrix.Api
open Silmaril.Proofs.Elf.Abi.ZlibMatrix

abbrev A0 : File := L.assemble bodies ld

theorem image_eq : image = A0.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize) := by
  decide +kernel

theorem crcData_mapped : ∀ d ∈ crcData, MappedAt F d.1.toNat d.2 := by
  intro d hd
  simp only [Silmaril.Machine.Abi.Conformance.ZlibLibz.crcData, List.mem_singleton] at hd
  subst hd
  exact ⟨_, parses, ph2, by decide +kernel, sub_kbytes K.wf_true K.toByteArray_eq _ _ _ (by decide +kernel)⟩

theorem crcData_untouched : ∀ d ∈ crcData, missesAllB A0 8 d.1.toNat d.2.length = true := by
  intro d hd
  simp only [Silmaril.Machine.Abi.Conformance.ZlibLibz.crcData, List.mem_singleton] at hd
  subst hd
  decide +kernel

theorem machine_x86_64 : A0.header.machine = EM_X86_64 := by decide +kernel

theorem reloc_width : widthsB A0 8 = true := by
  decide +kernel

theorem crc32Combine_code : CodeOf F (.dynsym (some zlib122)) "crc32_combine" crc32CombineCode :=
  codeOf parses _ _ _ 116 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    crcData_mapped image_eq

theorem crc32Combine_untouched : Untouched F crc32CombineCode :=
  untouched_of parses reloc_width (by decide +kernel) crcData_untouched

theorem crc32Combine_declared : Declares sysvInt hdr "crc32_combine" combineProto := declares_of_sig (by decide +kernel)

theorem crc32Combine_of (h : Task.crc32Combine) : silmaril.elf.abi.zlib_libz.crc32_combine :=
  row crc32Combine_code crc32Combine_untouched Silmaril.Elf.Abi.ZlibLibz.placement_zero h

theorem adler32Combine_code : CodeOf F (.dynsym (some zlib122)) "adler32_combine" adler32CombineCode :=
  codeOf parses _ _ _ 91 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    (fun _ h => nomatch h) image_eq

theorem adler32Combine_untouched : Untouched F adler32CombineCode :=
  untouched_of parses reloc_width (by decide +kernel) (fun _ h => nomatch h)

theorem adler32Combine_declared : Declares sysvInt hdr "adler32_combine" combineProto := declares_of_sig (by decide +kernel)

theorem adler32Combine_of (h : Task.adler32Combine) : silmaril.elf.abi.zlib_libz.adler32_combine :=
  row adler32Combine_code adler32Combine_untouched Silmaril.Elf.Abi.ZlibLibz.placement_zero h

theorem crc32CombineGen_code : CodeOf F (.dynsym (some zlib1212)) "crc32_combine_gen" crc32CombineGenCode :=
  codeOf parses _ _ _ 25 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    crcData_mapped image_eq

theorem crc32CombineGen_untouched : Untouched F crc32CombineGenCode :=
  untouched_of parses reloc_width (by decide +kernel) crcData_untouched

theorem crc32CombineGen_declared : Declares sysvInt hdr "crc32_combine_gen" genProto := declares_of_sig (by decide +kernel)

theorem crc32CombineGen_of (h : Task.crc32CombineGen) : silmaril.elf.abi.zlib_libz.crc32_combine_gen :=
  row crc32CombineGen_code crc32CombineGen_untouched Silmaril.Elf.Abi.ZlibLibz.placement_zero h

theorem crc32CombineOp_code : CodeOf F (.dynsym (some zlib1212)) "crc32_combine_op" crc32CombineOpCode :=
  codeOf parses _ _ _ 55 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    (fun _ h => nomatch h) image_eq

theorem crc32CombineOp_untouched : Untouched F crc32CombineOpCode :=
  untouched_of parses reloc_width (by decide +kernel) (fun _ h => nomatch h)

theorem crc32CombineOp_declared : Declares sysvInt hdr "crc32_combine_op" opProto := declares_of_sig (by decide +kernel)

theorem crc32CombineOp_of (h : Task.crc32CombineOp) : silmaril.elf.abi.zlib_libz.crc32_combine_op :=
  row crc32CombineOp_code crc32CombineOp_untouched Silmaril.Elf.Abi.ZlibLibz.placement_zero h

theorem getCrcTable_code : CodeOf F (.dynsym none) "get_crc_table" getCrcTableCode :=
  codeOf parses _ _ _ 84 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    crcData_mapped image_eq

theorem getCrcTable_untouched : Untouched F getCrcTableCode :=
  untouched_of parses reloc_width (by decide +kernel) crcData_untouched

theorem getCrcTable_declared : Declares sysvInt hdr "get_crc_table" ptrProto := declares_of_sig (by decide +kernel)

theorem getCrcTable_of (h : Task.getCrcTable) : silmaril.elf.abi.zlib_libz.get_crc_table :=
  row getCrcTable_code getCrcTable_untouched Silmaril.Elf.Abi.ZlibLibz.placement_zero h

theorem zlibVersion_code : CodeOf F (.dynsym none) "zlibVersion" zlibVersionCode :=
  codeOf parses _ _ _ 96 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    crcData_mapped image_eq

theorem zlibVersion_untouched : Untouched F zlibVersionCode :=
  untouched_of parses reloc_width (by decide +kernel) crcData_untouched

theorem zlibVersion_declared : Declares sysvInt hdr "zlibVersion" ptrProto := declares_of_sig (by decide +kernel)

theorem zlibVersion_of (h : Task.zlibVersion) : silmaril.elf.abi.zlib_libz.zlib_version :=
  row zlibVersion_code zlibVersion_untouched Silmaril.Elf.Abi.ZlibLibz.placement_zero h

theorem zlibCompileFlags_code : CodeOf F (.dynsym (some zlib1202)) "zlibCompileFlags" zlibCompileFlagsCode :=
  codeOf parses _ _ _ 70 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    (fun _ h => nomatch h) image_eq

theorem zlibCompileFlags_untouched : Untouched F zlibCompileFlagsCode :=
  untouched_of parses reloc_width (by decide +kernel) (fun _ h => nomatch h)

theorem zlibCompileFlags_declared : Declares sysvInt hdr "zlibCompileFlags" flagsProto := declares_of_sig (by decide +kernel)

theorem zlibCompileFlags_of (h : Task.zlibCompileFlags) : silmaril.elf.abi.zlib_libz.zlib_compile_flags :=
  row zlibCompileFlags_code zlibCompileFlags_untouched Silmaril.Elf.Abi.ZlibLibz.placement_zero h

theorem coverage_check : coverage.check sysvInt hdr = true := by decide +kernel

theorem coverage_complete : coverage.complete = true ∧ coverage.available = true := by decide

/-- **Complete header satisfaction, from the eleven tasks**: every declaration claimed and
conforming at every load base, nothing excluded. -/
theorem header_complete_of (h0 : Silmaril.Elf.Abi.ZlibLibz.Task.crc32z) (h1 : Silmaril.Elf.Abi.ZlibLibz.Task.crc32) (h2 : Silmaril.Elf.Abi.ZlibLibz.Task.adler32z) (h3 : Silmaril.Elf.Abi.ZlibLibz.Task.adler32) (g0 : Task.crc32Combine) (g1 : Task.adler32Combine) (g2 : Task.crc32CombineGen) (g3 : Task.crc32CombineOp) (g4 : Task.getCrcTable) (g5 : Task.zlibVersion) (g6 : Task.zlibCompileFlags) :
    silmaril.elf.abi.zlib_libz.zlib_h_complete := by
  have hconf : ∀ f ∈ coverage.claimed, ∃ i, impl f = some i ∧
      AbiConforms sysvInt (Silmaril.Machine.Abi.Conformance.Mach.ofInt Silmaril.X86.Open9.isa) i.mode hdr f i.proto F (bind f) i.code i.frame i.spec := by
    intro f hf
    simp only [coverage, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, Silmaril.Elf.Abi.ZlibLibz.crc32z_of h0⟩
    · exact ⟨_, rfl, Silmaril.Elf.Abi.ZlibLibz.crc32_of h1⟩
    · exact ⟨_, rfl, Silmaril.Elf.Abi.ZlibLibz.adler32z_of h2⟩
    · exact ⟨_, rfl, Silmaril.Elf.Abi.ZlibLibz.adler32_of h3⟩
    · exact ⟨_, rfl, crc32Combine_of g0⟩
    · exact ⟨_, rfl, adler32Combine_of g1⟩
    · exact ⟨_, rfl, crc32CombineGen_of g2⟩
    · exact ⟨_, rfl, crc32CombineOp_of g3⟩
    · exact ⟨_, rfl, getCrcTable_of g4⟩
    · exact ⟨_, rfl, zlibVersion_of g5⟩
    · exact ⟨_, rfl, zlibCompileFlags_of g6⟩
  have htot : ∀ f ∈ coverage.claimed, ∃ i, impl f = some i ∧ i.mode = .total := by
    intro f hf
    simp only [coverage, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
  have hnone : ∀ f why, (f, Exclusion.absent why) ∈ coverage.excluded → Absent F f := by
    intro f why h; simp [coverage] at h
  have hnone' : ∀ f why, (f, Exclusion.unclaimed why) ∈ coverage.excluded → Present F f := by
    intro f why h; simp [coverage] at h
  exact ⟨⟨⟨by decide, coverage_check, hnone, hnone', hconf⟩, by decide, htot⟩, by decide⟩

end Silmaril.Proofs.Elf.Abi.ZlibMatrix.LibzApi

end
