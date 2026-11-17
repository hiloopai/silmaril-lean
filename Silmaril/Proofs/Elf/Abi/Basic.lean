module

public import Silmaril.Elf.Abi.Defs
import Silmaril.Elf.Index.Thms

/-! # ABI conformance of an ELF function: generic proofs -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi

open Silmaril.Elf
open Silmaril.X86.Link (Blob)

/-- A file maps at most one byte list of each length at an address. -/
theorem codeAt_unique {F : Blob} {v : Nat} {xs ys : List (BitVec 8)} (hx : CodeAt F v xs)
    (hy : CodeAt F v ys) (hl : xs.length = ys.length) : xs = ys := by
  obtain ⟨A, hA, ph, hf, hr⟩ := hx
  obtain ⟨B, hB, ph', hf', hr'⟩ := hy
  have : A = B := Option.some.inj (hA.symm.trans hB)
  subst this
  rw [← hl, hf] at hf'
  cases hf'
  rw [← hl, hr] at hr'
  exact Silmaril.Elf.valueLE_inj hl (Option.some.inj hr')

open Silmaril.Elf.Abi
open Silmaril.Machine.Abi.Conformance (Code)

/-- What `Untouched` gives for one relocation of the file: a known width whose footprint misses
the code, and a type that is neither `COPY` nor `IRELATIVE`. -/
theorem untouched_reloc {F : Blob} {c : Code} {A : File} {r : File.Reloc} (h : Untouched F c)
    (hA : Parses F A) (hr : r ∈ A.relocs .dynamic) :
    (∃ w, A.relocWidth r = some w ∧ Silmaril.Elf.Image.Misses r.offset w c.base.toNat c.bytes.length = true) ∧
      r.kind ≠ R_X86_64_COPY ∧ r.kind ≠ R_X86_64_IRELATIVE := by
  obtain ⟨B, hB, hc, -, hk⟩ := h
  cases (Option.some.inj (hA.symm.trans hB) : A = B)
  exact ⟨hc r hr, hk r hr⟩

theorem not_untouched_of_width {F : Blob} {c : Code} {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hk : A.relocWidth r = none) : ¬ Untouched F c := by
  intro h
  obtain ⟨⟨w, hw, -⟩, -⟩ := untouched_reloc h hA hr
  rw [hk] at hw
  cases hw

theorem not_untouched_kind {F : Blob} {c : Code} {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hk : r.kind = R_X86_64_COPY ∨ r.kind = R_X86_64_IRELATIVE) :
    ¬ Untouched F c := by
  intro h
  obtain ⟨-, h5, h37⟩ := untouched_reloc h hA hr
  rcases hk with hk | hk
  · exact h5 hk
  · exact h37 hk

/-- A `TLSDESC` relocation (16 bytes) 12 bytes below the code touches its first 4 bytes: refused
on an x86-64 file (and on any other machine, where its width is unknown). -/
theorem not_untouched_tlsdesc {F : Blob} {c : Code} {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hk : r.kind = 36) (ho : r.offset + 12 = c.base.toNat)
    (hn : 0 < c.bytes.length) : ¬ Untouched F c := by
  intro h
  obtain ⟨⟨w, hw, hm⟩, -⟩ := untouched_reloc h hA hr
  unfold File.relocWidth at hw
  split at hw
  · cases hw
  · rw [hk] at hw
    simp only [show (36 : Nat) = 5 ↔ False by decide, ite_false, Silmaril.Elf.Image.x86RelocWidth,
      Option.some.injEq] at hw
    subst hw
    simp only [Silmaril.Elf.Image.Misses, Bool.or_eq_true, decide_eq_true_eq] at hm
    omega

theorem not_untouched_machine {F : Blob} {c : Code} {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hm : A.header.machine ≠ Silmaril.Elf.Image.EM_X86_64_MACHINE) :
    ¬ Untouched F c :=
  not_untouched_of_width hA hr (by unfold File.relocWidth; exact ite_eq_left hm)

/-- A file with no dynamic relocation touches nothing. -/
theorem untouched_of_norelocs {F : Blob} {c : Code} {A : File} (hA : Parses F A)
    (h : A.relocs .dynamic = []) : Untouched F c :=
  ⟨A, hA, fun r hr => by simp [h] at hr, fun _ _ r hr => by simp [h] at hr, fun r hr => by simp [h] at hr⟩

/-- A defined function is a defined name. -/
theorem definesName_of_definesFn {A : File} {n : Silmaril.Formats.ELF.NameBytes}
    (h : A.definesFn n = true) : A.definesName n = true := by
  simp only [File.definesFn, File.definesName, List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨t, ht, s, hs, ⟨hn, hi⟩, -⟩ := h
  exact ⟨t, ht, s, hs, hn, hi⟩

end Silmaril.Proofs.Elf.Abi

end
