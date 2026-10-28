module

public import Silmaril.Machine.Trace

/-! # Leads-to with a safety invariant (VERIFIED)

`Leads step Ok Goal x evs`: from `x`, having observed `evs`, every execution of `step` keeps
`Ok` at each state it visits and can always move, until it reaches a state satisfying `Goal`.
It is inductive, so every path reaches `Goal` after finitely many steps. This is the cut-point
interface between the segments of the `sha256` end-to-end proof
(`Problems.Sha256Cli.Segments`): each segment proves `Leads` from one cut predicate to the
next, and `Leads.trans` composes them.

Everything in this file is proved; no `sorry`, no new axiom.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

universe u v

/-- Every execution from `x` keeps `Ok` and can move until it reaches `Goal`. -/
inductive Leads {X : Type u} {E : Type v} (step : X → List E → X → Prop)
    (Ok Goal : X → List E → Prop) : X → List E → Prop where
  | done {x : X} {evs : List E} : Goal x evs → Leads step Ok Goal x evs
  | step {x : X} {evs : List E} : Ok x evs → (∃ e y, step x e y) →
      (∀ e y, step x e y → Leads step Ok Goal y (evs ++ e)) → Leads step Ok Goal x evs

namespace Leads

variable {X : Type u} {E : Type v} {step : X → List E → X → Prop}
  {Ok Goal Goal' : X → List E → Prop}

/-- Composition at a cut point. -/
theorem trans {x : X} {evs : List E} (h : Leads step Ok Goal x evs)
    (k : ∀ y es, Goal y es → Leads step Ok Goal' y es) : Leads step Ok Goal' x evs := by
  induction h with
  | done g => exact k _ _ g
  | step ok progress _ ih => exact .step ok progress ih

/-- A weaker invariant. -/
theorem mono_ok {Ok' : X → List E → Prop} {x : X} {evs : List E} (h : Leads step Ok Goal x evs)
    (weaker : ∀ y es, Ok y es → Ok' y es) : Leads step Ok' Goal x evs := by
  induction h with
  | done g => exact .done g
  | step ok progress _ ih => exact .step (weaker _ _ ok) progress ih

/-- `Leads` is preserved along any finite run, provided goal states are final. -/
theorem after_runs {x y : X} {evs es : List E} (h : Leads step Ok Goal x evs)
    (final : ∀ z zs, Goal z zs → ∀ e w, ¬ step z e w)
    (run : Machine.Trace.Runs step x es y) : Leads step Ok Goal y (evs ++ es) := by
  induction h generalizing y es with
  | done g =>
    cases run with
    | refl => simpa using Leads.done g
    | cons s _ => exact absurd s (final _ _ g _ _)
  | step ok progress next ih =>
    cases run with
    | refl => simpa using Leads.step ok progress next
    | cons s rest => simpa [List.append_assoc] using ih _ _ s rest

/-- The current state satisfies the invariant or the goal. -/
theorem now {x : X} {evs : List E} (h : Leads step Ok Goal x evs) : Ok x evs ∨ Goal x evs := by
  cases h with
  | done g => exact .inr g
  | step ok _ _ => exact .inl ok

/-- Along any finite run, either `Ok` holds or a (final) goal state has been reached. -/
theorem runs {x y : X} {evs es : List E} (h : Leads step Ok Goal x evs)
    (final : ∀ z zs, Goal z zs → ∀ e w, ¬ step z e w)
    (run : Machine.Trace.Runs step x es y) : Ok y (evs ++ es) ∨ Goal y (evs ++ es) :=
  (h.after_runs final run).now

/-- A reachable state that is not a goal can move. -/
theorem progress {x y : X} {evs es : List E} (h : Leads step Ok Goal x evs)
    (final : ∀ z zs, Goal z zs → ∀ e w, ¬ step z e w)
    (run : Machine.Trace.Runs step x es y) (notGoal : ¬ Goal y (evs ++ es)) :
    ∃ e w, step y e w := by
  cases h.after_runs final run with
  | done g => exact absurd g notGoal
  | step _ moves _ => exact moves

/-- No infinite execution. -/
theorem not_diverges {x : X} {evs : List E} (h : Leads step Ok Goal x evs)
    (final : ∀ z zs, Goal z zs → ∀ e w, ¬ step z e w) : ¬ Machine.Trace.Diverges step x := by
  induction h with
  | @done x _ g =>
    rintro ⟨trace, first, next⟩
    obtain ⟨e, s⟩ := next 0
    rw [first] at s
    exact final _ _ g _ _ s
  | @step x _ _ _ _ ih =>
    rintro ⟨trace, first, next⟩
    obtain ⟨e, s⟩ := next 0
    rw [first] at s
    exact ih e _ s ⟨fun n => trace (n + 1), rfl, fun n => next (n + 1)⟩

end Leads

end Silmaril.Process.LPS.Problems.Sha256Cli
