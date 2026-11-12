module

public import Silmaril.Elf.Link.ElfBind.Defs
public import Silmaril.Elf.Link.Dyn.Elf.Thms

/-! # Unpacking `CodeAt` (valid, not yet in Isar style; re-exported by `ElfBind.Thms`) -/

@[expose] public section

namespace Silmaril.Elf.Link.ElfBind

open Silmaril.Elf.Link.DynElf
open Silmaril.X86 (Word Byte)
open Silmaril.X86.Link (Blob)

/-- **What `CodeAt` read**: a read-only executable `PT_LOAD` mapping `[v, v + len)`, and the
value of its file bytes there. -/
theorem codeAt_elim {F : Blob} {v : Nat} {code : List Byte} (h : CodeAt F v code) :
    ∃ phs ph, phdrsOf F = some phs ∧ ph ∈ phs ∧ isLoad ph = true ∧ isRo ph = true ∧
      isExec ph = true ∧ ph.vaddr ≤ v ∧ v + code.length ≤ ph.vaddr + ph.filesz ∧
      blobRead F (ph.off + (v - ph.vaddr)) code.length = some (Blob.valueLE code) := by
  unfold CodeAt codeRead at h
  change ((DynElf.Elf.phdrs).bind _).run _ = _ at h
  rw [Rd.run_bind] at h
  cases hp : DynElf.Elf.phdrs.run (blobRead F) with
  | none => rw [hp] at h; cases h
  | some phs =>
    rw [hp, Option.bind_some] at h
    change ((Rd.ofOption _).bind _).run _ = _ at h
    rw [Rd.run_bind] at h
    cases hf : List.find? (fun ph => isLoad ph && isRo ph && isExec ph &&
        decide (ph.vaddr ≤ v) && decide (v + code.length ≤ ph.vaddr + ph.filesz)) phs with
    | none => rw [hf] at h; cases h
    | some ph =>
      rw [hf] at h
      have hc := List.find?_some hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨hl, hr⟩, hx⟩, hv⟩, hw⟩ := hc
      refine ⟨phs, ph, hp, List.mem_of_find?_eq_some hf, hl, hr, hx, hv, hw, ?_⟩
      change (Rd.read _ _ Rd.pure).run _ = _ at h
      cases e : blobRead F (ph.off + (v - ph.vaddr)) code.length with
      | none => rw [Rd.run_read_none _ e] at h; cases h
      | some n => rw [Rd.run_read_some _ e] at h; exact h

end Silmaril.Elf.Link.ElfBind
