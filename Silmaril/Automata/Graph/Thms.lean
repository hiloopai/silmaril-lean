module

public import Silmaril.Automata.Graph.Defs
import Silmaril.Proofs.Automata.Graph.Dominators
import Silmaril.Proofs.Automata.Graph.Regions
import Silmaril.Proofs.Automata.Graph.Entries
import Silmaril.Proofs.Automata.Graph.Machine

@[expose] public section

/-!
# Rooted graphs: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Automata/Graph/`):

* **dominator trees**: `domExact_iff` (a tree is exact iff it agrees with `idom` on reachable
  nodes, so exactness is `Decidable`), `idom_exact` (the immediate-dominator tree is exact), `exact_eq_idom` and
  `exact_unique` (an exact tree *is* the immediate-dominator tree on reachable nodes, so exact
  trees are unique there), `idom_sound`, `starTree_sound` and `sound_not_unique` (sound trees are not
  unique: a concrete graph where the starTree and the immediate-dominator tree differ);
* **multiple entries**: `withRoot_dominates_iff`: for nodes of `g`, dominance in `withRoot g E`
  is exactly dominance for the entry set `E`;
* **region trees**: `Dissolve.flatten_eq`, `Coarsens.flatten_eq` (coarsening keeps the nodes and
  their order) and `bracketings_not_unique` (two different trees with one flattening);
  `header_dominates` (the header of a single-entry region dominates its nodes);
* **machines**: `NMachine.reachable_iff`, `DMachine.reachable_iff`: a state's node is reachable
  in the machine's graph iff the state is reachable in the machine (all labels).
-/

namespace Silmaril.Automata.Graph

open Silmaril.Machine.Graph

theorem idom_exact (g : Digraph) : DomExact g g.idom := Silmaril.Proofs.Automata.Graph.idom_exact g

theorem idom_sound (g : Digraph) : DomSound g g.idom := Silmaril.Proofs.Automata.Graph.idom_sound g

theorem exact_eq_idom {g : Digraph} {p : Parent} (hp : DomExact g p) {b : Nat}
    (hb : g.Reachable b) : p b = g.idom b :=
  Silmaril.Proofs.Automata.Graph.exact_eq_idom hp hb

theorem exact_unique {g : Digraph} {p q : Parent} (hp : DomExact g p) (hq : DomExact g q)
    {b : Nat} (hb : g.Reachable b) : p b = q b :=
  Silmaril.Proofs.Automata.Graph.exact_unique hp hq hb

theorem domExact_iff {g : Digraph} {p : Parent} :
    DomExact g p ↔ ∀ b, g.Reachable b → p b = g.idom b :=
  Silmaril.Proofs.Automata.Graph.domExact_iff

/-- The exact-tree problem is decidable: compare with `idom` on the finitely many nodes. -/
instance (g : Digraph) (p : Parent) : Decidable (DomExact g p) :=
  decidable_of_iff (∀ b ∈ g.nodes, g.Reachable b → p b = g.idom b) (by
    rw [domExact_iff]
    exact ⟨fun h b hb => h b (Digraph.mem_nodes_of_reachable hb) hb, fun h b _ hb => h b hb⟩)

theorem starTree_sound (g : Digraph) : DomSound g (starTree g) := Silmaril.Proofs.Automata.Graph.starTree_sound g

/-- The chain `0 → 1 → 2`. -/
def chain3 : Digraph := ⟨3, fun n => if n < 2 then [n + 1] else [], 0⟩

/-- **Sound dominator trees are not unique**: on `0 → 1 → 2`, the starTree (parent of `2` is `0`) and
the immediate-dominator tree (parent of `2` is `1`) are both sound. -/
theorem sound_not_unique : ∃ g p q, DomSound g p ∧ DomSound g q ∧
    ∃ b, g.Reachable b ∧ p b ≠ q b := by
  refine ⟨chain3, starTree chain3, chain3.idom, starTree_sound _, idom_sound _, 2, ?r, ?_⟩
  case r => exact ⟨[0, 1, 2], rfl, rfl, by decide⟩
  have h1 : chain3.idom 2 = some 1 := by decide
  have hr : chain3.Reachable 2 ∧ (2 : Nat) ≠ chain3.entry := ⟨⟨[0, 1, 2], rfl, rfl, by decide⟩, by decide⟩
  have h2 : starTree chain3 2 = some 0 := by
    simp only [starTree, hr]; rfl
  rw [h1, h2]; decide

theorem withRoot_dominates_iff {g : Digraph} {E : List Nat} {a b : Nat} (ha : a < g.size)
    (hb : b < g.size) : (withRoot g E).Dominates a b ↔ SetDominates g E a b :=
  Silmaril.Proofs.Automata.Graph.withRoot_dominates_iff ha hb

theorem RTree.Dissolve.flatten_eq {t t' : RTree} (h : RTree.Dissolve t t') :
    t.flatten = t'.flatten :=
  Silmaril.Proofs.Automata.Graph.dissolve_flatten h

theorem RTree.Coarsens.flatten_eq {t t' : RTree} (h : RTree.Coarsens t t') :
    t.flatten = t'.flatten :=
  Silmaril.Proofs.Automata.Graph.coarsens_flatten h

/-- **Bracketings are not unique**: `((0 1) 2)` and `(0 (1 2))` flatten to `[0, 1, 2]`, and both
coarsen to the flat `(0 1 2)`. -/
theorem bracketings_not_unique :
    let t₁ := RTree.group [.group [.leaf 0, .leaf 1], .leaf 2]
    let t₂ := RTree.group [.leaf 0, .group [.leaf 1, .leaf 2]]
    let flat := RTree.group [.leaf 0, .leaf 1, .leaf 2]
    t₁.flatten = t₂.flatten ∧ RTree.Coarsens t₁ flat ∧ RTree.Coarsens t₂ flat := by
  refine ⟨rfl, Relation.ReflTransGen.single ?_, Relation.ReflTransGen.single ?_⟩
  · exact RTree.Dissolve.here [] [.leaf 2] [.leaf 0, .leaf 1]
  · exact RTree.Dissolve.here [.leaf 0] [] [.leaf 1, .leaf 2]

theorem header_dominates {g : Digraph} {S : List Nat} {h b : Nat} (hS : SingleEntry g S h)
    (hent : g.entry ∈ S → h = g.entry) (hb : b ∈ S) : g.Dominates h b :=
  Silmaril.Proofs.Automata.Graph.header_dominates hS hent hb

variable {S L : Type} [FinNamed S] [FinNamed L] [DecidableEq S]

theorem NMachine.reachable_iff (M : NMachine S L) (init t : S) :
    (M.toDigraph init).Reachable (stateIndex t) ↔ ReachVia M.toLTS (fun _ => True) init t :=
  Silmaril.Proofs.Automata.Graph.machine_reachable_iff M init t

theorem DMachine.reachable_iff (M : DMachine S L) (init t : S) :
    (M.toDigraph init).Reachable (stateIndex t) ↔ ReachVia M.toLTS (fun _ => True) init t :=
  Silmaril.Proofs.Automata.Graph.dmachine_reachable_iff M init t

end Silmaril.Automata.Graph
