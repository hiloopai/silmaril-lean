module

public import Silmaril.Elf.Abi.ZlibLibz.Defs
public import Silmaril.Proofs.Elf.Abi.ZlibLibz
public import Silmaril.Proofs.Elf.Abi.ZlibRows

/-! # libz.so.1.3 rows: everything but the conformance -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.ZlibLibzRows

open Silmaril.Elf Silmaril.Elf.Abi Silmaril.Elf.Abi.ZlibLibz
open Silmaril.Elf.Staged.Pinned.ZlibLibz (F parses)
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib (zProto wProto)
open Silmaril.Proofs.Elf.Abi.ZlibLibz (A0)
open Silmaril.Proofs.Elf.Abi.ZlibRows (declares_of_sig)

theorem crc32z_declared : Declares sysvInt hdr "crc32_z" zProto := declares_of_sig (by decide +kernel)
theorem crc32_declared : Declares sysvInt hdr "crc32" wProto := declares_of_sig (by decide +kernel)
theorem adler32z_declared : Declares sysvInt hdr "adler32_z" zProto := declares_of_sig (by decide +kernel)
theorem adler32_declared : Declares sysvInt hdr "adler32" wProto := declares_of_sig (by decide +kernel)

theorem coverage_check : coverage.check sysvInt hdr = true := by decide +kernel

/-- Some table defines a function named `f` (the core's `File.definesFn`). -/
def presentB (f : String) : Bool := A0.definesFn (nameOf f)

theorem present_of {f : String} (h : presentB f = true) : Present F f := ⟨_, parses, h⟩

theorem excluded_ok : ∀ e ∈ coverage.excluded,
    (match e.2 with
      | .unclaimed _ => presentB e.1
      | _ => false) = true := by
  decide +kernel

/-- A row from its file facts and its open conformance at every admitted base. -/
theorem row {M : Mach} {f : String} {p : Silmaril.Machine.Abi.SystemV.Proto} {b : Binding} {c : Code}
    {frame : Nat} {S : CallSpec sysvInt.V p} (hc : CodeOf F b f c) (hu : Untouched F c)
    (h : ∀ base, Placement F base → Conforms sysvInt M .total hdr f p (c.rebase base) frame S) :
    AbiConforms sysvInt M .total hdr f p F b c frame S :=
  ⟨hc, hu, ⟨0, Silmaril.Proofs.Elf.Abi.ZlibLibz.placement_zero_ok⟩, h⟩

theorem crc32z_of (h : Task.crc32z) : silmaril.elf.abi.zlib_libz.crc32_z :=
  row Silmaril.Proofs.Elf.Abi.ZlibLibz.crc32z_code Silmaril.Proofs.Elf.Abi.ZlibLibz.crc32z_untouched h
theorem crc32_of (h : Task.crc32) : silmaril.elf.abi.zlib_libz.crc32 :=
  row Silmaril.Proofs.Elf.Abi.ZlibLibz.crc32_code Silmaril.Proofs.Elf.Abi.ZlibLibz.crc32_untouched h
theorem adler32z_of (h : Task.adler32z) : silmaril.elf.abi.zlib_libz.adler32_z :=
  row Silmaril.Proofs.Elf.Abi.ZlibLibz.adler32z_code Silmaril.Proofs.Elf.Abi.ZlibLibz.adler32z_untouched h
theorem adler32_of (h : Task.adler32) : silmaril.elf.abi.zlib_libz.adler32 :=
  row Silmaril.Proofs.Elf.Abi.ZlibLibz.adler32_code Silmaril.Proofs.Elf.Abi.ZlibLibz.adler32_untouched h

theorem header_of (h1 : Task.crc32z) (h2 : Task.crc32) (h3 : Task.adler32z) (h4 : Task.adler32) :
    silmaril.elf.abi.zlib_libz.zlib_h := by
  refine ⟨by decide, coverage_check, fun _ _ h => ?_, fun _ _ h => present_of (excluded_ok _ h),
    fun f hf => ?_⟩
  · simp [coverage] at h
  · simp only [coverage, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, crc32z_of h1⟩
    · exact ⟨_, rfl, crc32_of h2⟩
    · exact ⟨_, rfl, adler32z_of h3⟩
    · exact ⟨_, rfl, adler32_of h4⟩

end Silmaril.Proofs.Elf.Abi.ZlibLibzRows

end
