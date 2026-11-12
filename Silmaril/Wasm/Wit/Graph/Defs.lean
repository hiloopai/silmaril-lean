module

/-!
# Acyclicity of finite dependency graphs

WIT requires several dependency graphs to be acyclic: `use` between interfaces, the
references between type definitions and `include` between worlds. This module gives
the specification and a checker, generic in the node type.

* `Ranked deps nodes r`: along every edge `a → b` (`b ∈ deps a`) between nodes, the
  rank decreases; `Acyclic deps nodes := ∃ r, Ranked deps nodes r`.
* `kahn deps nodes`: Kahn's algorithm by layers. A node is ready when none of its
  dependencies is still pending; each round removes the ready nodes; the graph is
  acyclic when every node is removed. `krank` is the round in which a node goes.

`Silmaril.Wasm.Wit.Graph.Thms` proves `kahn deps nodes = true ↔ Acyclic deps nodes`,
with `krank` as the witness, bounded by the number of nodes.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Graph

variable {α : Type} [DecidableEq α] (deps : α → List α)

/-- Ranks that decrease along the edges between `nodes`. -/
def Ranked (nodes : List α) (r : α → Nat) : Prop :=
  ∀ a ∈ nodes, ∀ b ∈ deps a, b ∈ nodes → r b < r a

/-- The graph restricted to `nodes` is acyclic. -/
def Acyclic (nodes : List α) : Prop := ∃ r, Ranked deps nodes r

/-- `a` has no dependency among the pending nodes `rest`. -/
def ready (rest : List α) (a : α) : Bool := (deps a).all fun b => !rest.contains b

/-- The nodes still pending after one round. -/
def nextRound (rest : List α) : List α := rest.filter fun a => !ready deps rest a

theorem nextRound_lt {rest : List α} (h : rest.any (ready deps rest) = true) :
    (nextRound deps rest).length < rest.length := by
  obtain ⟨a, ha, hr⟩ := List.any_eq_true.mp h
  exact List.length_filter_lt_length_iff_exists.mpr ⟨a, ha, by simp [hr]⟩

/-- Kahn's algorithm: remove the ready nodes round by round; succeed when nothing
remains. -/
def kahn (rest : List α) : Bool :=
  if _h : rest.any (ready deps rest) then kahn (nextRound deps rest) else rest.isEmpty
termination_by rest.length
decreasing_by exact nextRound_lt deps _h

/-- The round in which `kahn` removes a node. -/
def krank (rest : List α) (a : α) : Nat :=
  if h : rest.any (ready deps rest) then
    if ready deps rest a then 0 else krank (nextRound deps rest) a + 1
  else 0
termination_by rest.length
decreasing_by exact nextRound_lt deps h

end Silmaril.Wasm.Wit.Graph
