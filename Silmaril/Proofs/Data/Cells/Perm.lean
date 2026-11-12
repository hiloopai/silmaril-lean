module

public import Silmaril.Proofs.Data.Cells.Check

/-!
# Cells: the update rule up to permutation

`Frag.holds_update_perm`: the old fragment (with fresh slots `X`) is a permutation of the
store slots `M` followed by the kept cells `R`; the stores have the slots' shapes. Then every
cell of the new fragment that is a store, or a kept old cell, holds after the stores. Instance
proofs state the permutation (`List.perm_iff_count`) and the membership facts only.
-/

@[expose] public section

namespace Silmaril.Data

theorem Frag.Sep.pairwise : ∀ {f : Frag}, f.Sep → f.Pairwise Cell.Apart
  | [], _ => List.Pairwise.nil
  | _ :: _, h => by
    obtain ⟨hf, hc⟩ := Frag.sep_cons.1 h
    exact List.Pairwise.cons hc (Frag.Sep.pairwise hf)

/-- Apartness of two (address, width) shapes. -/
def shapeApart (x y : Nat × Nat) : Prop :=
  ∀ a, x.1 ≤ a → a < x.1 + x.2 → y.1 ≤ a → a < y.1 + y.2 → False

theorem Frag.holds_update_perm {v : MemView} {f X M R st f' : Frag}
    (hS : Frag.Sep (f ++ X)) (hP : (f ++ X).Perm (M ++ R)) (hf : f.Holds v)
    (hshape : st.map (fun d => (d.addr, d.width)) = M.map (fun e => (e.addr, e.width)))
    (hfit : ∀ d ∈ st, d.val < 256 ^ d.width ∧ ∀ i < d.width, v.writable (d.addr + i) = true)
    (hf' : ∀ c ∈ f', c ∈ st ∨ (c ∈ R ∧ c ∈ f)) : f'.Holds (v.storeAll st) := by
  have hMR : Frag.Sep (M ++ R) := Frag.sep_of_perm hS hP
  obtain ⟨hM, -, hap⟩ := Frag.sep_append.1 hMR
  have hslot : ∀ d ∈ st, ∃ e ∈ M, e.addr = d.addr ∧ e.width = d.width := by
    intro d hd
    have : (d.addr, d.width) ∈ M.map (fun e => (e.addr, e.width)) := by
      rw [← hshape]; exact List.mem_map.2 ⟨d, hd, rfl⟩
    obtain ⟨e, he, hee⟩ := List.mem_map.1 this
    exact ⟨e, he, (Prod.mk.inj hee).1, (Prod.mk.inj hee).2⟩
  have hpw : st.Pairwise Cell.Apart := by
    have h1 : (M.map (fun e => (e.addr, e.width))).Pairwise shapeApart :=
      List.pairwise_map.2 (hM.pairwise.imp fun h => h)
    rw [← hshape] at h1
    exact (List.pairwise_map.1 h1).imp fun h => h
  intro c hc
  refine Cell.holds_storeAll (fun d hd => hfit d hd) hpw ?_
  rcases hf' c hc with h | ⟨hR, hcf⟩
  · exact .inl h
  · refine .inr ⟨hf c hcf, fun d hd => ?_⟩
    obtain ⟨e, he, h1, h2⟩ := hslot d hd
    exact ((hap e he c hR).of_eq h1.symm h2.symm rfl rfl).symm

end Silmaril.Data
