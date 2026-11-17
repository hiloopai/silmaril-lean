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

/-- What `Untouched` gives for one relocation of the file. -/
theorem untouched_reloc {F : Blob} {c : Code} {A : File} {r : File.Reloc} (h : Untouched F c)
    (hA : Parses F A) (hr : r ∈ A.relocs .dynamic) :
    A.header.machine = EM_X86_64 ∧ ∃ w, relocWidth r.kind = some w ∧
      Misses r.offset w c.base.toNat c.bytes.length := by
  obtain ⟨B, hB, hm, hall⟩ := h
  cases (Option.some.inj (hA.symm.trans hB) : A = B)
  obtain ⟨w, hw, hc, -⟩ := hall r hr
  exact ⟨hm, w, hw, hc⟩

theorem not_untouched_of_width {F : Blob} {c : Code} {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hk : relocWidth r.kind = none) : ¬ Untouched F c := by
  intro h
  obtain ⟨-, w, hw, -⟩ := untouched_reloc h hA hr
  rw [hk] at hw
  cases hw

theorem not_untouched_tlsdesc {F : Blob} {c : Code} {A : File} {r : File.Reloc} (hA : Parses F A)
    (hr : r ∈ A.relocs .dynamic) (hk : r.kind = 36) (ho : r.offset + 12 = c.base.toNat)
    (hn : 0 < c.bytes.length) : ¬ Untouched F c := by
  intro h
  obtain ⟨-, w, hw, hm⟩ := untouched_reloc h hA hr
  rw [hk] at hw
  cases hw
  unfold Misses at hm
  omega

theorem not_untouched_machine {F : Blob} {c : Code} {A : File} (hA : Parses F A)
    (hm : A.header.machine ≠ EM_X86_64) : ¬ Untouched F c := by
  rintro ⟨B, hB, hB62, -⟩
  cases (Option.some.inj (hA.symm.trans hB) : A = B)
  exact hm hB62

end Silmaril.Proofs.Elf.Abi

end
