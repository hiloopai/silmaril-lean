module

public import Silmaril.Machine.CBackend.Graph.Dominance.Defs
/-!
# Back edges and natural loops

The two definitions a loop-recovery checker needs, stated once against the
shared `Digraph` so that the eventual λSSA region recovery and the CFG recovered
from machine code use the same notion. A back edge is an edge whose target
dominates its source; the natural loop of a back edge `src → dst` is its header
`dst` together with every node that reaches `src` without passing through `dst`.

Both are decidable, by `Dominance`'s fixpoint and by the same fixpoint run on
the reverse graph.

Not provided: loop nesting forests, irreducibility detection, or any theorem
about natural loops. This file exists so that there is one definition to prove
things about when a pass needs them.
-/

@[expose] public section

namespace Silmaril.Machine.Graph

namespace Digraph

variable {g : Digraph} {src dst x y : Nat}

/-- The graph with every edge reversed, rooted at `root`. -/
def reverse (g : Digraph) (root : Nat) : Digraph where
  size := g.size
  succ x := (List.range g.size).filter fun p => decide (x ∈ g.step p)
  entry := root

@[simp] theorem reverse_size (g : Digraph) (root : Nat) : (g.reverse root).size = g.size := rfl

theorem edge_reverse (g : Digraph) (root : Nat) :
    (g.reverse root).Edge x y ↔ (g.Edge y x ∧ y < g.size ∧ x < g.size) := by
  simp only [Edge, step, reverse, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hy, hx⟩, -⟩
    exact ⟨hx, hy, hx.2⟩
  · rintro ⟨hx, hy, -⟩
    exact ⟨⟨hy, hx⟩, hy⟩

/-- A back edge: an edge whose target dominates its source. -/
def BackEdge (g : Digraph) (src dst : Nat) : Prop := g.Edge src dst ∧ g.Dominates dst src

instance : Decidable (g.BackEdge src dst) := inferInstanceAs (Decidable (_ ∧ _))

/-- The natural loop of the back edge `src → dst`: the header `dst` together
with every node that reaches `src` without passing through `dst`. -/
def naturalLoop (g : Digraph) (src dst : Nat) : List Nat :=
  dst :: (g.reverse src).closure fun x => x != dst

/-- Membership in the natural loop of a back edge. -/
def InNaturalLoop (g : Digraph) (src dst x : Nat) : Prop := x ∈ g.naturalLoop src dst

instance : Decidable (g.InNaturalLoop src dst x) := inferInstanceAs (Decidable (_ ∈ _))

/-- The header of a natural loop belongs to it. -/
theorem inNaturalLoop_header (g : Digraph) (src dst : Nat) :
    g.InNaturalLoop src dst dst := by
  simp [InNaturalLoop, naturalLoop]

end Digraph

end Silmaril.Machine.Graph
