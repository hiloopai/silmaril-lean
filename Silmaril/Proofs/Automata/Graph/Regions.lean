module

public import Silmaril.Automata.Graph.Defs

/-!
# Region trees: proofs

Coarsening preserves the flattening; the header of a single-entry region dominates the region.
-/

@[expose] public section

namespace Silmaril.Proofs.Automata.Graph

open Silmaril.Machine.Graph Silmaril.Automata.Graph

theorem flattenList_append (xs ys : List RTree) :
    RTree.flatten.flattenList (xs ++ ys) =
      RTree.flatten.flattenList xs ++ RTree.flatten.flattenList ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [RTree.flatten.flattenList, ih, List.append_assoc]

theorem dissolve_flatten {t t' : RTree} (h : RTree.Dissolve t t') : t.flatten = t'.flatten := by
  induction h with
  | here pre post cs =>
    simp [RTree.flatten, flattenList_append, RTree.flatten.flattenList, List.append_assoc]
  | inside pre post _ ih =>
    simp [RTree.flatten, flattenList_append, RTree.flatten.flattenList, ih]

theorem coarsens_flatten {t t' : RTree} (h : RTree.Coarsens t t') : t.flatten = t'.flatten := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (dissolve_flatten h)

/-- A chain whose head is outside `S` and whose last element is inside `S` crosses into `S`. -/
theorem crosses {g : Digraph} {S : List Nat} {h : Nat}
    (hS : ∀ x y, g.Edge x y → x ∉ S → y ∈ S → y = h) :
    ∀ (ls : List Nat) (x : Nat), List.IsChain g.Edge (x :: ls) → x ∉ S →
      (∃ y ∈ ls, y ∈ S) → h ∈ ls
  | [], _, _, _, ⟨y, hy, _⟩ => by simp at hy
  | y :: ys, x, hc, hx, hex => by
    have hxy : g.Edge x y := (List.isChain_cons_cons.mp hc).1
    by_cases hy : y ∈ S
    · rw [hS x y hxy hx hy]; exact List.mem_cons_self
    · have hrest : List.IsChain g.Edge (y :: ys) := (List.isChain_cons_cons.mp hc).2
      obtain ⟨z, hz, hzS⟩ := hex
      rcases List.mem_cons.mp hz with rfl | hz
      · exact absurd hzS hy
      · exact List.mem_cons_of_mem _ (crosses hS ys y hrest hy ⟨z, hz, hzS⟩)

/-- **The header of a single-entry region dominates its nodes**, when the region does not
contain the entry or is headed by it. -/
theorem header_dominates {g : Digraph} {S : List Nat} {h b : Nat} (hS : SingleEntry g S h)
    (hent : g.entry ∈ S → h = g.entry) (hb : b ∈ S) : g.Dominates h b := by
  intro ls hp
  obtain ⟨hhead, hlast, hchain⟩ := hp
  by_cases he : g.entry ∈ S
  · rw [hent he]
    cases ls with
    | nil => simp at hhead
    | cons x xs => simp at hhead; rw [hhead]; exact List.mem_cons_self
  · cases ls with
    | nil => simp at hhead
    | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      have hbl : b ∈ g.entry :: xs := List.mem_of_getLast? hlast
      rcases List.mem_cons.mp hbl with rfl | hbx
      · exact absurd hb he
      · exact List.mem_cons_of_mem _ (crosses hS.2 xs _ hchain he ⟨b, hbx, hb⟩)

end Silmaril.Proofs.Automata.Graph
