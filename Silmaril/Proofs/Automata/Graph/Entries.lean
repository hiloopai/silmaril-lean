module

public import Silmaril.Automata.Graph.Defs

/-!
# Multiple entries through a synthetic root: proofs
-/

@[expose] public section

namespace Silmaril.Proofs.Automata.Graph

open Silmaril.Machine.Graph Silmaril.Automata.Graph

variable {g : Digraph} {E : List Nat}

theorem withRoot_edge_old {x y : Nat} (hx : x ≠ g.size) :
    (withRoot g E).Edge x y ↔ g.Edge x y := by
  simp only [Digraph.Edge, Digraph.step, withRoot, hx, ↓reduceIte, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, decide_eq_true (Nat.lt_succ_of_lt h2)⟩

theorem withRoot_edge_root {y : Nat} : (withRoot g E).Edge g.size y ↔ y ∈ inRange g E := by
  simp only [Digraph.Edge, Digraph.step, withRoot, ↓reduceIte, List.mem_filter, inRange,
    decide_eq_true_eq]
  constructor
  · rintro ⟨h, -⟩; exact h
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, decide_eq_true (Nat.lt_succ_of_lt h2)⟩

theorem withRoot_edge_lt {x y : Nat} (h : (withRoot g E).Edge x y) : y < g.size := by
  by_cases hx : x = g.size
  · subst hx
    have := (withRoot_edge_root.mp h)
    simp only [inRange, List.mem_filter, decide_eq_true_eq] at this
    exact this.2
  · exact Digraph.lt_size_of_edge ((withRoot_edge_old hx).mp h)

/-- A `g`-chain from an in-range node stays in range and is a chain of `withRoot g E`. -/
theorem chain_to_root : ∀ (ls : List Nat) (x : Nat), x < g.size → List.IsChain g.Edge (x :: ls) →
    List.IsChain (withRoot g E).Edge (x :: ls) ∧ ∀ y ∈ x :: ls, y < g.size
  | [], x, hx, _ => ⟨.singleton x, by simpa using hx⟩
  | y :: ys, x, hx, hc => by
    have hxy := (List.isChain_cons_cons.mp hc).1
    have hy := Digraph.lt_size_of_edge hxy
    obtain ⟨ih1, ih2⟩ := chain_to_root ys y hy (List.isChain_cons_cons.mp hc).2
    refine ⟨List.isChain_cons_cons.mpr ⟨(withRoot_edge_old (by omega)).mpr hxy, ih1⟩, ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact ih2 z hz

/-- A `withRoot` chain whose head is an old node is a `g`-chain. -/
theorem chain_of_root : ∀ (ls : List Nat) (x : Nat), x < g.size →
    List.IsChain (withRoot g E).Edge (x :: ls) → List.IsChain g.Edge (x :: ls)
  | [], x, _, _ => .singleton x
  | y :: ys, x, hx, hc => by
    have hxy := (List.isChain_cons_cons.mp hc).1
    exact List.isChain_cons_cons.mpr ⟨(withRoot_edge_old (by omega)).mp hxy,
      chain_of_root ys y (withRoot_edge_lt hxy) (List.isChain_cons_cons.mp hc).2⟩

theorem withRoot_dominates_iff {a b : Nat} (ha : a < g.size) (hb : b < g.size) :
    (withRoot g E).Dominates a b ↔ SetDominates g E a b := by
  constructor
  · intro hd e he ls hp
    obtain ⟨hhead, hlast, hchain⟩ := hp
    cases ls with
    | nil => simp at hhead
    | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      have heS : x < g.size := by
        simp only [inRange, List.mem_filter, decide_eq_true_eq] at he; exact he.2
      obtain ⟨hc, -⟩ := chain_to_root (E := E) xs x heS hchain
      have hp' : (withRoot g E).Path (withRoot g E).entry b (g.size :: x :: xs) := by
        refine ⟨rfl, ?_, List.isChain_cons_cons.mpr ⟨withRoot_edge_root.mpr he, hc⟩⟩
        simpa [List.getLast?_cons] using hlast
      have := hd _ hp'
      rcases List.mem_cons.mp this with h | h
      · omega
      · exact h
  · intro hs ls hp
    obtain ⟨hhead, hlast, hchain⟩ := hp
    cases ls with
    | nil => simp at hhead
    | cons r rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      change r = g.size at hhead
      subst hhead
      cases rest with
      | nil => simp at hlast; omega
      | cons e xs =>
        have hre := (List.isChain_cons_cons.mp hchain).1
        have he := withRoot_edge_root.mp hre
        have heS := withRoot_edge_lt hre
        have hc := chain_of_root xs e heS (List.isChain_cons_cons.mp hchain).2
        have hp' : g.Path e b (e :: xs) := ⟨rfl, by simpa [List.getLast?_cons] using hlast, hc⟩
        exact List.mem_cons_of_mem _ (hs e he _ hp')

end Silmaril.Proofs.Automata.Graph
