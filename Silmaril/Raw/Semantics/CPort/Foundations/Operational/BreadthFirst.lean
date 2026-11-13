module

public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Relation

/-! # Finite-branching FIFO exploration

One step pops the oldest node and appends its finitely many children. A complete
frontier is processed before any of its children. This scheduling utility is
independent of terms, inference rules, and the predicates used to prune nodes.
-/

@[expose] public section

namespace Silmaril.Operational.BreadthFirst

variable {α : Type*}

/-- The visited prefix and the remaining FIFO queue after at most `fuel` pops. -/
def advance (children : α → List α) : Nat → List α → List α × List α
  | 0, pending => ([], pending)
  | _ + 1, [] => ([], [])
  | fuel + 1, node :: pending =>
    let result := advance children fuel (pending ++ children node)
    (node :: result.1, result.2)

@[simp] theorem advance_zero (children : α → List α) (pending : List α) :
    advance children 0 pending = ([], pending) := rfl

@[simp] theorem advance_nil (children : α → List α) (fuel : Nat) :
    advance children fuel [] = ([], []) := by cases fuel <;> rfl

/-- Children added by earlier pops never overtake an existing queue prefix. -/
theorem advance_prefix (children : α → List α) (leading trailing : List α) :
    advance children leading.length (leading ++ trailing) =
      (leading, trailing ++ leading.flatMap children) := by
  induction leading generalizing trailing with
  | nil => simp
  | cons node leading ih =>
    simp only [List.length_cons, List.cons_append, advance]
    rw [List.append_assoc, ih]
    simp [List.flatMap_cons, List.append_assoc]

/-- Splitting a fuel budget preserves the exact queue order and visit order. -/
theorem advance_add (children : α → List α) (first second : Nat) (pending : List α) :
    advance children (first + second) pending =
      let left := advance children first pending
      let right := advance children second left.2
      (left.1 ++ right.1, right.2) := by
  induction first generalizing pending with
  | zero => simp
  | succ first ih =>
    cases pending with
    | nil => simp
    | cons node pending =>
      rw [Nat.succ_add]
      simp only [advance]
      rw [ih]
      simp

/-- The nodes at a fixed depth, with duplicates and source order retained. -/
def frontier (children : α → List α) (initial : List α) : Nat → List α
  | 0 => initial
  | depth + 1 => (frontier children initial depth).flatMap children

/-- Number of queue pops needed to finish all strictly earlier frontiers. -/
def before (children : α → List α) (initial : List α) : Nat → Nat
  | 0 => 0
  | depth + 1 => before children initial depth + (frontier children initial depth).length

/-- The exact accumulated visit order before a frontier. -/
def earlier (children : α → List α) (initial : List α) : Nat → List α
  | 0 => []
  | depth + 1 => earlier children initial depth ++ frontier children initial depth

theorem advance_before (children : α → List α) (initial : List α) (depth : Nat) :
    advance children (before children initial depth) initial =
      (earlier children initial depth, frontier children initial depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [before, advance_add, ih]
    have entire := advance_prefix children (frontier children initial depth) []
    simp only [List.append_nil, List.nil_append] at entire
    simp only [entire, earlier, frontier]

/-- Every node in any finite frontier is visited after finitely many FIFO pops. -/
theorem frontier_eventually_visited (children : α → List α) (initial : List α)
    {depth : Nat} {node : α} (member : node ∈ frontier children initial depth) :
    ∃ fuel, node ∈ (advance children fuel initial).1 := by
  refine ⟨before children initial (depth + 1), ?_⟩
  rw [advance_before]
  exact List.mem_append_right _ member

inductive Reachable (children : α → List α) (initial : List α) : α → Prop where
  | root {node} (member : node ∈ initial) : Reachable children initial node
  | child {parent node} (parentReachable : Reachable children initial parent)
      (member : node ∈ children parent) : Reachable children initial node

/-- Finite reachability equals membership in some breadth-first frontier. -/
theorem reachable_iff_frontier (children : α → List α) (initial : List α) (node : α) :
    Reachable children initial node ↔ ∃ depth, node ∈ frontier children initial depth := by
  constructor
  · intro reachable
    induction reachable with
    | root member => exact ⟨0, member⟩
    | @child parent node _ member ih =>
      obtain ⟨depth, present⟩ := ih
      exact ⟨depth + 1, List.mem_flatMap.mpr ⟨parent, present, member⟩⟩
  · rintro ⟨depth, member⟩
    induction depth generalizing node with
    | zero => exact .root member
    | succ depth ih =>
      obtain ⟨parent, present, child⟩ := List.mem_flatMap.mp member
      exact .child (ih parent present) child

/-- Finite branching suffices for FIFO fairness; no finiteness or termination
assumption is imposed on the entire reachable graph. -/
theorem reachable_eventually_visited (children : α → List α) (initial : List α)
    {node : α} (reachable : Reachable children initial node) :
    ∃ fuel, node ∈ (advance children fuel initial).1 := by
  obtain ⟨depth, member⟩ := (reachable_iff_frontier children initial node).mp reachable
  exact frontier_eventually_visited children initial member

end Silmaril.Operational.BreadthFirst
