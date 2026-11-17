module

public import Silmaril.Elf.Abi.Zlib.Defs
public import Silmaril.Proofs.Elf.Abi.Zlib
public import Silmaril.Proofs.Elf.Abi.LeafArith

/-! # zlib-checksums rows: everything but the conformance -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.ZlibRows

open Silmaril.Elf Silmaril.Elf.Abi Silmaril.Elf.Abi.Zlib
open Silmaril.Elf.Staged.Pinned.ZlibChecksums (F L bodies ld parses)
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Zlib
open Silmaril.Proofs.Elf.Abi.Zlib (A0)

/-- `Declares` from the decidable comparison of lowered signatures. -/
theorem declares_of_sig {hdr : HeaderSrc} {f : String} {p : Silmaril.Machine.Abi.SystemV.Proto}
    (h : (hdr.proto? f).bind (fun cp => (sysvInt.lower cp).toOption.map (·.signature)) = some p.signature) :
    Declares sysvInt hdr f p := by
  cases hp : hdr.proto? f with
  | none => rw [hp] at h; cases h
  | some cp =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    cases hl : sysvInt.lower cp with
    | error e => rw [hl] at h; cases h
    | ok q =>
      rw [hl] at h
      have hs : q.signature = p.signature := Option.some.inj h
      have : q = p := by cases q; cases p; simp only at hs; subst hs; rfl
      exact ⟨cp, hp, this ▸ hl⟩

theorem crc32z_declared : Declares sysvInt hdr "crc32_z" zProto := declares_of_sig (by decide +kernel)
theorem crc32_declared : Declares sysvInt hdr "crc32" wProto := declares_of_sig (by decide +kernel)
theorem adler32z_declared : Declares sysvInt hdr "adler32_z" zProto := declares_of_sig (by decide +kernel)
theorem adler32_declared : Declares sysvInt hdr "adler32" wProto := declares_of_sig (by decide +kernel)

theorem coverage_check : coverage.check sysvInt hdr = true := by decide +kernel

def absentB (f : String) : Bool :=
  [Table.symtab, Table.dynsym].all fun t =>
    (A0.symbols t).all fun s => s.name != nameOf f || s.raw.sectionIndex == 0

def presentB (f : String) : Bool :=
  [Table.symtab, Table.dynsym].any fun t =>
    (A0.symbols t).any fun s => s.name == nameOf f && s.raw.sectionIndex != 0 &&
      (s.kind == 2 || s.kind == 10)

theorem absent_of {f : String} (h : absentB f = true) : Absent F f := by
  refine ⟨_, parses, fun t s hs hn => ?_⟩
  simp only [absentB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  cases t
  · exact (h.1 s hs).resolve_left (by simpa using hn)
  · exact (h.2 s hs).resolve_left (by simpa using hn)

theorem present_of {f : String} (h : presentB f = true) : Present F f := by
  simp only [presentB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with ⟨s, hs, ⟨hn, hi⟩, hk⟩ | ⟨s, hs, ⟨hn, hi⟩, hk⟩
  · exact ⟨_, parses, .symtab, s, hs, hn, hi, by simpa using hk⟩
  · exact ⟨_, parses, .dynsym, s, hs, hn, hi, by simpa using hk⟩

theorem excluded_ok : ∀ e ∈ coverage.excluded,
    (match e.2 with
      | .absent _ => absentB e.1
      | .unclaimed _ => presentB e.1
      | _ => true) = true := by
  decide +kernel

/-- A row from its file facts and its conformance at base `0`. -/
theorem row {M : Mach} {f : String} {p : Silmaril.Machine.Abi.SystemV.Proto} {c : Code} {frame : Nat}
    {S : CallSpec sysvInt.V p} (hc : CodeOf F .symtab f c) (h : Conforms sysvInt M .total hdr f p c frame S) :
    AbiConforms sysvInt M .total hdr f p F .symtab c frame S :=
  ⟨hc, Silmaril.Proofs.Elf.Abi.Zlib.untouched c, ⟨0, Silmaril.Proofs.Elf.Abi.Zlib.placement_zero_ok⟩,
    fun b hb => by
      rw [Silmaril.Proofs.Elf.Abi.Zlib.placement_zero hb, Silmaril.Proofs.Elf.Abi.LeafArith.rebase_zero]
      exact h⟩

theorem crc32z_of (h : Task.crc32z) : silmaril.elf.abi.zlib_checksums.crc32_z :=
  row Silmaril.Proofs.Elf.Abi.Zlib.crc32z_code h
theorem crc32_of (h : Task.crc32) : silmaril.elf.abi.zlib_checksums.crc32 :=
  row Silmaril.Proofs.Elf.Abi.Zlib.crc32_code h
theorem adler32z_of (h : Task.adler32z) : silmaril.elf.abi.zlib_checksums.adler32_z :=
  row Silmaril.Proofs.Elf.Abi.Zlib.adler32z_code h
theorem adler32_of (h : Task.adler32) : silmaril.elf.abi.zlib_checksums.adler32 :=
  row Silmaril.Proofs.Elf.Abi.Zlib.adler32_code h

theorem header_of (h1 : Task.crc32z) (h2 : Task.crc32) (h3 : Task.adler32z) (h4 : Task.adler32) :
    silmaril.elf.abi.zlib_checksums.zlib_h := by
  refine ⟨by decide, coverage_check, fun _ _ h => absent_of (excluded_ok _ h),
    fun _ _ h => present_of (excluded_ok _ h), fun f hf => ?_⟩
  simp only [coverage, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, row Silmaril.Proofs.Elf.Abi.Zlib.crc32z_code h1⟩
  · exact ⟨_, rfl, row Silmaril.Proofs.Elf.Abi.Zlib.crc32_code h2⟩
  · exact ⟨_, rfl, row Silmaril.Proofs.Elf.Abi.Zlib.adler32z_code h3⟩
  · exact ⟨_, rfl, row Silmaril.Proofs.Elf.Abi.Zlib.adler32_code h4⟩

end Silmaril.Proofs.Elf.Abi.ZlibRows

end
