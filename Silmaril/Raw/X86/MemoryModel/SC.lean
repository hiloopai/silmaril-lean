-- Word-granular memory models from an earlier Silmaril development; namespaces
-- `Silmaril.Memory{,.SC,.TSO}` kept. Re-exported by `Silmaril.X86.MemoryModel.Tso`.
module

public import Silmaril.Raw.X86.MemoryModel.Execution
public import Mathlib.Logic.Function.Basic

/-!
# Sequentially consistent memory

Each observable access takes effect atomically in one shared heap. A concurrent
execution interleaves thread traces while preserving each thread's program
order. The model has no hidden propagation transitions. This is Lamport's SC
interleaving model, for total homogeneous heaps without allocation or faults.
-/

@[expose] public section

namespace Silmaril.Memory.SC

universe u v w

abbrev Heap (Addr : Type u) (Val : Type u) := Addr → Val
variable {Tid : Type v} {Addr Val : Type u} [DecidableEq Addr]

/-- Observable atomic steps, including the returned load value. -/
inductive Step : Heap Addr Val → Event Tid Addr Val → Heap Addr Val → Prop
  | load (h : Heap Addr Val) (t : Tid) (a : Addr) : Step h (.load t a (h a)) h
  | store (h : Heap Addr Val) (t : Tid) (a : Addr) (v : Val) :
      Step h (.store t a v) (Function.update h a v)
  | fence (h : Heap Addr Val) (t : Tid) : Step h (.fence t) h

/-- Every SC event has at most one successor. -/
theorem Step.deterministic {h h₁ h₂ : Heap Addr Val} {e : Event Tid Addr Val}
    (one : Step h e h₁) (two : Step h e h₂) : h₁ = h₂ := by
  cases one <;> cases two <;> rfl

/-- A store cannot change a different location. -/
theorem store_frame {a b : Addr} (hne : b ≠ a) (h : Heap Addr Val) (v : Val) :
    Function.update h a v b = h b := Function.update_of_ne hne _ _

/-- Executable validation of a candidate trace's load results. -/
def run [DecidableEq Val] (h : Heap Addr Val) : List (Event Tid Addr Val) → Option (Heap Addr Val)
  | [] => some h
  | .load _ a v :: es => if h a = v then run h es else none
  | .store _ a v :: es => run (Function.update h a v) es
  | .fence _ :: es => run h es

/-- The trace validator accepts precisely the operational executions. -/
theorem run_eq_some_iff [DecidableEq Val] {h h' : Heap Addr Val} {es : List (Event Tid Addr Val)} :
    run h es = some h' ↔ Execution Step h es h' := by
  induction es generalizing h with
  | nil => simp only [run, Option.some.injEq]; constructor
           · rintro rfl; exact .nil _
           · intro e; cases e; rfl
  | cons e es ih =>
      cases e with
      | load t a v =>
          by_cases hv : h a = v
          · subst v
            simp only [run, ↓reduceIte, ih]
            exact ⟨fun e => .cons (.load h t a) e, fun e => by cases e with | cons h e => cases h; exact e⟩
          · simp only [run, hv, ↓reduceIte, reduceCtorEq, false_iff]
            intro e
            cases e with
            | cons h _ => cases h; exact hv rfl
      | store t a v =>
          simp only [run, ih]
          exact ⟨fun e => .cons (.store h t a v) e, fun e => by cases e with | cons h e => cases h; exact e⟩
      | fence t =>
          simp only [run, ih]
          exact ⟨fun e => .cons (.fence h t) e, fun e => by cases e with | cons h e => cases h; exact e⟩

namespace Litmus

abbrev E := Event Bool Bool Nat

def initial : Heap Bool Nat := fun _ => 0

def sbLeft : List E := [.store false false 1, .load false true 0]
def sbRight : List E := [.store true true 1, .load true false 0]

/-- Every program-order-preserving SC interleaving forbids the store-buffering
outcome in which both loads read the initial zero. -/
theorem store_buffering_forbidden : ¬ Concurrent Step initial sbLeft sbRight := by
  rintro ⟨trace, sched, final, exec⟩
  have accepted := run_eq_some_iff.mpr exec
  simp only [sbLeft, sbRight, shuffles, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at sched
  rcases sched with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [run, initial, Function.update] at accepted

end Litmus
end Silmaril.Memory.SC
