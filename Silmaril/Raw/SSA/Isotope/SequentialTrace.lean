module

public import Mathlib.Data.List.Basic

/-! # Finite chronological traces over an arbitrary state

Every step retains its actual input and output state. In particular, a trace
can thread shared allocations and pending asynchronous operations as well as
global memory.
-/

@[expose] public section
universe u v w
namespace Silmaril.Isotope

inductive SequentialTrace {Action : Type u} {State : Type v}
    (execute : Action → State → State → Prop) : List Action → State → State → Prop where
  | nil (state : State) : SequentialTrace execute [] state state
  | cons {action : Action} {actions : List Action} {before middle after : State}
      (head : execute action before middle) (tail : SequentialTrace execute actions middle after) :
      SequentialTrace execute (action :: actions) before after

namespace SequentialTrace
variable {Action : Type u} {State : Type v} {Other : Type w}

theorem append {execute : Action → State → State → Prop} {left right : List Action}
    {before middle after : State} (first : SequentialTrace execute left before middle)
    (second : SequentialTrace execute right middle after) :
    SequentialTrace execute (left ++ right) before after := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head (ih second)

theorem append_iff {execute : Action → State → State → Prop} {left right : List Action}
    {before after : State} : SequentialTrace execute (left ++ right) before after ↔
      ∃ middle, SequentialTrace execute left before middle ∧ SequentialTrace execute right middle after := by
  constructor
  · intro trace
    induction left generalizing before with
    | nil => exact ⟨before, .nil _, trace⟩
    | cons action left ih =>
      cases trace with
      | cons head tail =>
        obtain ⟨middle, first, second⟩ := ih tail
        exact ⟨middle, .cons head first, second⟩
  · rintro ⟨middle, first, second⟩
    exact first.append second

/-- Grouping adjacent events into source phases preserves all intermediate
machine states; no phase is replaced by an assumed summary transition. -/
theorem flatMap_iff {execute : Action → State → State → Prop} {expand : Other → List Action}
    {actions : List Other} {before after : State} :
    SequentialTrace execute (actions.flatMap expand) before after ↔
      SequentialTrace (fun action => SequentialTrace execute (expand action)) actions before after := by
  induction actions generalizing before with
  | nil => constructor <;> intro h <;> cases h <;> exact .nil _
  | cons action actions ih =>
    constructor
    · intro trace
      obtain ⟨middle, first, rest⟩ := append_iff.mp trace
      exact .cons first (ih.mp rest)
    · intro trace
      cases trace with
      | cons first rest => exact first.append (ih.mpr rest)

theorem map_actions_iff {execute : Action → State → State → Prop} {action : Other → Action}
    {actions : List Other} {before after : State} :
    SequentialTrace execute (actions.map action) before after ↔
      SequentialTrace (fun index => execute (action index)) actions before after := by
  induction actions generalizing before with
  | nil => constructor <;> intro h <;> cases h <;> exact .nil _
  | cons index indices ih =>
    constructor
    · intro trace; cases trace with
      | cons head tail => exact .cons head (ih.mp tail)
    · intro trace; cases trace with
      | cons head tail => exact .cons head (ih.mpr tail)

/-- Every state in a finite indexed trace, including both endpoints. This
extracts states from the actual transitions and is useful for loop builders. -/
theorem range'_states {execute : Nat → State → State → Prop} {start count : Nat} {before after : State}
    (trace : SequentialTrace execute (List.range' start count) before after) :
    ∃ state : Nat → State, state 0 = before ∧ state count = after ∧
      ∀ index < count, execute (start + index) (state index) (state (index + 1)) := by
  induction count generalizing start before with
  | zero =>
    cases trace
    exact ⟨fun _ => after, rfl, rfl, by omega⟩
  | succ count ih =>
    rw [List.range'_succ] at trace
    cases trace with
    | cons head tail =>
      obtain ⟨state, first, last, steps⟩ := ih tail
      refine ⟨fun index => match index with | 0 => before | i + 1 => state i, rfl, last, ?_⟩
      intro index bound
      cases index with
      | zero => simpa only [Nat.add_zero, first] using head
      | succ index => simpa only [Nat.add_assoc, Nat.add_comm 1 index] using steps index (by omega)

theorem range_states {execute : Nat → State → State → Prop} {count : Nat} {before after : State}
    (trace : SequentialTrace execute (List.range count) before after) :
    ∃ state : Nat → State, state 0 = before ∧ state count = after ∧
      ∀ index < count, execute index (state index) (state (index + 1)) := by
  rw [List.range_eq_range'] at trace
  simpa only [Nat.zero_add] using range'_states trace

theorem deterministic {execute : Action → State → State → Prop}
    (step : ∀ action {before a b}, execute action before a → execute action before b → a = b)
    {actions : List Action} {before a b : State}
    (first : SequentialTrace execute actions before a) (second : SequentialTrace execute actions before b) :
    a = b := by
  induction first generalizing b with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons head' tail' =>
      obtain rfl := step _ head head'
      exact ih tail'

/-- Preserve a state predicate through the actual transitions. The step rule
only needs to cover actions occurring in this trace. -/
theorem preserves {execute : Action → State → State → Prop} {actions : List Action} {before after : State}
    (trace : SequentialTrace execute actions before after) (invariant : State → Prop)
    (step : ∀ action ∈ actions, ∀ first last, execute action first last → invariant first → invariant last)
    (initial : invariant before) : invariant after := by
  induction trace with
  | nil => exact initial
  | @cons action actions first middle last head tail ih =>
    exact ih (fun a ha => step a (List.mem_cons_of_mem _ ha))
      (step action (List.mem_cons_self ..) first middle head initial)

theorem map {execute : Action → State → State → Prop} {target : Action → Other → Other → Prop}
    (state : State → Other)
    (step : ∀ action before after, execute action before after → target action (state before) (state after))
    {actions : List Action} {before after : State} (trace : SequentialTrace execute actions before after) :
    SequentialTrace target actions (state before) (state after) := by
  induction trace with
  | nil => exact .nil _
  | cons head tail ih => exact .cons (step _ _ _ head) ih

theorem exists_of_invariant {execute : Action → State → State → Prop}
    (actions : List Action) (invariant : State → Prop)
    (step : ∀ action ∈ actions, ∀ before, invariant before →
      ∃ after, execute action before after ∧ invariant after)
    (before : State) (initial : invariant before) :
    ∃ after, SequentialTrace execute actions before after ∧ invariant after := by
  induction actions generalizing before with
  | nil => exact ⟨before, .nil _, initial⟩
  | cons action actions ih =>
    obtain ⟨middle, head, preserved⟩ := step action (by simp) before initial
    obtain ⟨after, tail, final⟩ := ih (fun action h => step action (by simp [h])) middle preserved
    exact ⟨after, .cons head tail, final⟩

end SequentialTrace
end Silmaril.Isotope
