module

public import Silmaril.Proofs.Elf.BindEq.Phdrs
public import Silmaril.Elf.Bridge.Thms
public import Silmaril.Elf.Facts.Thms

/-! # `CodeAt` and `Placement` are `ElfBind`'s

PROVED (standard axioms): `codeAt_iff` (`Task.codeAt_iff`) and `placement_iff`
(`Task.placement_iff`, which needs `e_phentsize = 56`: see `Silmaril.Elf.Bridge.Defs`), from
`phdrs_rd`; with them, `directCall_of_roLoaded` holds outright (`directCall_of_roLoaded'`). -/

@[expose] public section

namespace Silmaril.Proofs.Elf.BindEq

open Silmaril.Elf
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Link.ElfBind (isLoad isRo isExec)
open Silmaril.X86.Link (Blob)
open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)

theorem codeSeg_dyn (v len : Nat) :
    (fun ph => isLoad ph && isRo ph && isExec ph && decide (ph.vaddr ≤ v) &&
      decide (v + len ≤ ph.vaddr + ph.filesz)) ∘ Bridge.phdrToDyn = codeSeg v len := rfl

/-- **`Task.codeAt_iff`.** -/
theorem codeAt_iff : Bridge.Task.codeAt_iff := by
  intro F A v code hA _hx
  constructor
  · intro h
    unfold Silmaril.Elf.Link.ElfBind.CodeAt Silmaril.Elf.Link.ElfBind.codeRead at h
    by_cases he : A.header.programEntrySize = 56
    · rw [run_bind_of _ (phdrs_rd hA _hx he), List.find?_map, codeSeg_dyn] at h
      cases hf : A.phdrs.find? (codeSeg v code.length) with
      | none => rw [hf] at h; cases h
      | some ph =>
        rw [hf] at h
        refine ⟨A, hA, ph, hf, ?_⟩
        have := h
        rw [show (Option.map Bridge.phdrToDyn (some ph)) = some (Bridge.phdrToDyn ph) from rfl] at this
        change (Rd.le (ph.offset + (v - ph.virtualAddress)) code.length).run (blobRead F) = _ at this
        rwa [run_le] at this
    · rw [bind_eq, Rd.run_bind, phdrs_rd_none hA he] at h
      cases h
  · rintro ⟨B, hB, ph, hf, hr⟩
    cases parses_unique hA hB
    have hne : A.phdrs ≠ [] := by intro h0; rw [h0] at hf; cases hf
    have he := phentsize_of_phdrs hA hne
    unfold Silmaril.Elf.Link.ElfBind.CodeAt Silmaril.Elf.Link.ElfBind.codeRead
    rw [run_bind_of _ (phdrs_rd hA _hx he), List.find?_map, codeSeg_dyn, hf]
    change (Rd.le (ph.offset + (v - ph.virtualAddress)) code.length).run (blobRead F) = _
    rw [run_le]
    exact hr

theorem word_zero_iff (base : Word) : base = 0 ↔ base.toNat = 0 :=
  ⟨fun h => by simp [h], fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩

/-- **`Task.placement_iff`.** -/
theorem placement_iff : Bridge.Task.placement_iff := by
  intro F A base hA hx he
  have hph := phdrs_rd hA hx he
  have het := etype_rd hA
  constructor
  · rintro ⟨t, phs, ht, hphs, hty, hall⟩
    rw [het] at ht; cases ht
    unfold Silmaril.Elf.Link.ElfBind.phdrsOf at hphs
    rw [hph] at hphs; cases hphs
    refine ⟨A, hA, ?_, ?_⟩
    · rcases hty with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, (word_zero_iff base).1 h2⟩
      · exact .inr ⟨h1, h2⟩
    · intro ph hm
      rw [File.loads, List.mem_filter] at hm
      exact hall (Bridge.phdrToDyn ph) (List.mem_map_of_mem hm.1) hm.2
  · rintro ⟨B, hB, hty, hall⟩
    cases parses_unique hA hB
    refine ⟨A.header.fileType, A.phdrs.map Bridge.phdrToDyn, het, hph, ?_, ?_⟩
    · rcases hty with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, (word_zero_iff base).2 h2⟩
      · exact .inr ⟨h1, h2⟩
    · intro d hd hl
      obtain ⟨ph, hm, rfl⟩ := List.mem_map.1 hd
      exact hall ph (List.mem_filter.2 ⟨hm, hl⟩)

/-- **Direct call ⊑ `RoLoaded`**, outright: in memory where the read-only segments of `F` are
loaded at `base`, the code a `CodeAt` fact names is fetchable at `base + v`. -/
theorem directCall_of_roLoaded' {F : Blob} {A : File} (hA : Parses F A) (hx : A.header.machine = 62)
    (he : A.header.programEntrySize = 56) {base : Word} {mem : Memory} {v : Nat}
    {code : List Byte} (hcode : CodeAt F v code) (hplace : Placement F base.toNat)
    (hl : Silmaril.Elf.Link.ElfBind.RoLoaded F base mem) :
    mem.fetchBytes (base + BitVec.ofNat 64 v).toNat code.length = some code ∧
      (base + BitVec.ofNat 64 v).toNat = base.toNat + v :=
  Bridge.directCall_of_roLoaded codeAt_iff placement_iff hA hx he hcode hplace hl

/-- A `Binds` row and a placement give the code at `base + v` (the premise of a direct-call
specification). -/
theorem directCall_of_binds {F : Blob} {A : File} (hA : Parses F A) (hx : A.header.machine = 62)
    (he : A.header.programEntrySize = 56) {sel : Sel} {base : Word} {mem : Memory} {v : Nat}
    {code : List Byte} (hb : Binds F sel v code) (hplace : Placement F base.toNat)
    (hl : Silmaril.Elf.Link.ElfBind.RoLoaded F base mem) :
    mem.fetchBytes (base + BitVec.ofNat 64 v).toNat code.length = some code ∧
      (base + BitVec.ofNat 64 v).toNat = base.toNat + v :=
  directCall_of_roLoaded' hA hx he hb.2 hplace hl

end Silmaril.Proofs.Elf.BindEq
