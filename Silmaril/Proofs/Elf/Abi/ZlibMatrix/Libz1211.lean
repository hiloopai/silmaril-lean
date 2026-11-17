module

public import Silmaril.Proofs.Elf.Abi.ZlibMatrix.Common
public import Silmaril.Elf.Staged.Pinned.ZlibLibz1211.Thms

/-! # The zlib library matrix, `Libz1211`: the file facts of the rows

Each one a kernel read on the file's kernel bytes, or a computation on the parse it gives. -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.ZlibLibz1211
open Silmaril.Elf.Abi
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib (zProto wProto)
open Silmaril.Machine.Abi.Conformance.ZlibMatrix.Libz1211
open Silmaril.Elf.Abi.ZlibMatrix (hdr zlib129 bind frame)
open Silmaril.Elf.Abi.ZlibMatrix.Libz1211
open Silmaril.Proofs.Elf.Abi.ZlibMatrix

abbrev A0 : File := L.assemble bodies ld

theorem image_eq : image = A0.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize) := by
  decide +kernel

/-- The file is x86-64, and every dynamic relocation is 8 bytes (`GLOB_DAT`, `JUMP_SLOT`,
`RELATIVE`). -/
theorem machine_x86_64 : A0.header.machine = EM_X86_64 := by decide +kernel

theorem reloc_width : widthsB A0 8 = true := by
  decide +kernel

theorem reloc_kinds : (A0.relocs .dynamic).all (fun r => [6, 7, 8].contains r.kind) = true := by
  decide +kernel

theorem adler32z_code : CodeOf F (.dynsym (some zlib129)) "adler32_z" adler32zCode :=
  codeOf parses _ _ _ 37 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    (fun _ h => nomatch h) image_eq

theorem adler32z_untouched : Untouched F adler32zCode :=
  untouched_of parses reloc_width (by decide +kernel) (fun _ h => nomatch h)

theorem adler32z_declared : Declares sysvInt hdr "adler32_z" zProto := declares_of_sig (by decide +kernel)

theorem adler32_code : CodeOf F (.dynsym none) "adler32" adler32Code :=
  codeOf parses _ _ _ 44 rfl (by decide +kernel) (by decide +kernel)
    (codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide +kernel) (by decide +kernel))
    (fun _ h => nomatch h) image_eq

theorem adler32_untouched : Untouched F adler32Code :=
  untouched_of parses reloc_width (by decide +kernel) (fun _ h => nomatch h)

theorem adler32_declared : Declares sysvInt hdr "adler32" wProto := declares_of_sig (by decide +kernel)

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

/-- **`crc32_z` is an IFUNC here**: ld.so's versioned lookup finds an `STT_GNU_IFUNC`
definition, so no code is the file's `crc32_z`. -/
theorem crc32z_ifunc (c : Code) : ¬ CodeOf F (.dynsym (some zlib129)) "crc32_z" c :=
  not_codeOf_ifunc parses (d := ⟨25, 30176, 12, true, false⟩) (by decide +kernel) rfl c

theorem adler32z_of (h : Task.adler32z) : silmaril.elf.abi.zlib_libz_1_2_11.adler32_z :=
  row adler32z_code adler32z_untouched placement_zero_ok h

theorem adler32_of (h : Task.adler32) : silmaril.elf.abi.zlib_libz_1_2_11.adler32 :=
  row adler32_code adler32_untouched placement_zero_ok h

theorem header_of (h0 : Task.adler32z) (h1 : Task.adler32) :
    silmaril.elf.abi.zlib_libz_1_2_11.zlib_h := by
  refine ⟨by decide, coverage_check, fun _ _ h => absent_of parses (excluded_ok _ h),
    fun _ _ h => present_of parses (excluded_ok _ h), fun f hf => ?_⟩
  simp only [coverage, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨_, rfl, adler32z_of h0⟩
  · exact ⟨_, rfl, adler32_of h1⟩

end Silmaril.Proofs.Elf.Abi.ZlibMatrix.Libz1211

end
