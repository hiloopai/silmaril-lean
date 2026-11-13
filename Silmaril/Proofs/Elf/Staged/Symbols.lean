module

public import Silmaril.Elf.Staged.Symbols.Defs
public import Silmaril.Elf.Link.Dyn.Elf.Thms

/-! # Symbol indexes: soundness of the checks and of the lookups (standard axioms) -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Staged.Symbols

open Silmaril.Elf.Staged.Symbols
open Silmaril.Formats.ELF (NameBytes)
open Silmaril.Elf.Check (Src Sub)
open Silmaril.Elf.Link.DynElf (Rd)
open Silmaril.X86.Link (Blob)

theorem nameCmp_eq : ∀ {a b : NameBytes}, nameCmp a b = .eq → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [nameCmp] at h
  | _ :: _, [], h => by simp [nameCmp] at h
  | a :: as, b :: bs, h => by
    simp only [nameCmp] at h
    split at h
    · cases h
    · split at h
      · cases h
      · have hab : a = b := BitVec.eq_of_toNat_eq (by omega)
        rw [hab, nameCmp_eq h]

theorem mem_of_getElem? {α : Type} {xs : Array α} {k : Nat} {e : α} (h : xs[k]? = some e) :
    e ∈ xs.toList := by
  rw [Array.getElem?_eq_some_iff] at h
  obtain ⟨hk, rfl⟩ := h
  exact Array.getElem_mem_toList hk

theorem byName_go (x : ByName) (n : NameBytes) {i : Nat} :
    ∀ (fuel lo hi : Nat), x.go n fuel lo hi = some i → (n, i) ∈ x.entries.toList
  | 0, _, _, h => by simp [ByName.go] at h
  | fuel + 1, lo, hi, h => by
    simp only [ByName.go] at h
    split at h
    · split at h
      · cases h
      · rename_i m j he
        split at h
        · rename_i hc
          cases h
          rw [← nameCmp_eq hc]
          exact mem_of_getElem? he
        · exact byName_go x n fuel _ _ h
        · exact byName_go x n fuel _ _ h
    · cases h

theorem byName_find {x : ByName} {n : NameBytes} {i : Nat} (h : x.find n = some i) :
    (n, i) ∈ x.entries.toList :=
  byName_go x n 64 0 _ h

theorem byAddr_find {x : ByAddr} {v i : Nat} (h : x.find v = some i) :
    ∃ e ∈ x.entries.toList, e.1 ≤ v ∧ v < e.1 + e.2.1 ∧ e.2.2 = i := by
  unfold ByAddr.find at h
  split at h
  · rename_i a z j he
    split at h
    · rename_i hv
      cases h
      obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.mp he
      exact ⟨_, mem_of_getElem? hk, hv.1, hv.2, rfl⟩
    · cases h
  · cases h

theorem byNameOk_sound {r : Src} {F : Blob} (hs : Sub r F) {x : ByName}
    (h : byNameOk r x = true) : x.sorted = true ∧ x.Sound F := by
  simp only [byNameOk, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun e he => ?_⟩
  have := h.2 e he
  simp only [decide_eq_true_eq] at this
  obtain ⟨hi, hm⟩ := this
  split at hm
  · rename_i s hr
    exact ⟨s, ⟨hi, Rd.run_mono hs _ _ hr⟩, (beq_iff_eq.mp hm)⟩
  · cases hm

theorem byAddrOk_sound {r : Src} {F : Blob} (hs : Sub r F) {x : ByAddr}
    (h : byAddrOk r x = true) : x.sorted = true ∧ x.Sound F := by
  simp only [byAddrOk, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun e he => ?_⟩
  have := h.2 e he
  simp only [decide_eq_true_eq] at this
  obtain ⟨hi, hm⟩ := this
  split at hm
  · rename_i s hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    exact ⟨s, ⟨hi, Rd.run_mono hs _ _ hr⟩, hm.1, hm.2⟩
  · cases hm

end Silmaril.Proofs.Elf.Staged.Symbols
