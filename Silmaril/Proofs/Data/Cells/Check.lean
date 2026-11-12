module

public import Silmaril.Proofs.Data.Cells.Store

/-!
# Cells: the executable separation check is sound
-/

@[expose] public section

namespace Silmaril.Data

theorem Frag.sep_of_perm {f g : Frag} (h : f.Sep) (hp : f.Perm g) : g.Sep :=
  (hp.flatMap_right _).nodup_iff.1 h

theorem Frag.sepSortedB_sound : ∀ {l : List Cell}, l.Pairwise (fun c d => c.addr ≤ d.addr) →
    Frag.sepSortedB l = true → Frag.Sep l
  | [], _, _ => List.nodup_nil
  | [c], _, _ => by
    simp only [Frag.Sep, Frag.bytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.nodup_range'
  | c :: d :: rest, hs, h => by
    simp only [Frag.sepSortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    have hs' := List.pairwise_cons.1 hs
    have ih := Frag.sepSortedB_sound hs'.2 h.2
    refine Frag.sep_cons.2 ⟨ih, fun e he a h1 h2 h3 h4 => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · omega
    · have := (List.pairwise_cons.1 hs'.2).1 e he
      omega

theorem Frag.sep_of_sepB {f : Frag} (h : Frag.sepB f = true) : f.Sep := by
  unfold Frag.sepB at h
  refine Frag.sep_of_perm (Frag.sepSortedB_sound ?_ h) (List.mergeSort_perm _ _)
  have := List.pairwise_mergeSort (le := fun c d : Cell => decide (c.addr ≤ d.addr))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) f
  exact this.imp fun h => by simpa using h

end Silmaril.Data
