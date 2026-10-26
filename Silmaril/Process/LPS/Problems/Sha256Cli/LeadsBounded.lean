module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Leads

/-! # `Leads` from an invariant, progress and a bound on run length (VERIFIED)

`Leads step Ok Goal x evs` is inductive. Segment proofs by verification conditions or by
refinement usually establish its three ingredients separately:

* **safety**: along every run from `x`, `Ok` or `Goal` holds (an inductive invariant, or a
  trace refinement into a reference machine);
* **progress**: every reachable state that is not a goal can move (nothing stuck: no fault, no
  unmodelled instruction, a kernel reply exists);
* **a bound**: no run from `x` has more than `N` steps (a ranking function, or the liveness
  budget of `Sys.LiveRel`).

`leads_of_bounded` assembles them into `Leads`; with `goal_final` the goal states must be
final. `RunsN` is `Machine.Trace.Runs` with its number of steps.

No `sorry`, no new axiom.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

universe u v

/-- Runs with their number of steps. -/
inductive RunsN {X : Type u} {E : Type v} (step : X → List E → X → Prop) :
    Nat → X → List E → X → Prop where
  | refl (x : X) : RunsN step 0 x [] x
  | cons {n : Nat} {x y z : X} {e es : List E} :
      step x e y → RunsN step n y es z → RunsN step (n + 1) x (e ++ es) z

theorem RunsN.runs {X : Type u} {E : Type v} {step : X → List E → X → Prop} {n : Nat} {x y : X}
    {es : List E} (r : RunsN step n x es y) : Machine.Trace.Runs step x es y := by
  induction r with
  | refl x => exact .refl x
  | cons s _ ih => exact .cons s ih

/-- **`Leads` from safety, progress and a bound.** If along every run from `x` (after the
history `h`) the invariant or the goal holds, every reachable non-goal state can move, and no
run has more than `N` steps, then `Leads step Ok Goal x h`. -/
theorem leads_of_bounded {X : Type u} {E : Type v} {step : X → List E → X → Prop}
    {Ok Goal : X → List E → Prop} (N : Nat) :
    ∀ (x : X) (h : List E),
      (∀ n es y, RunsN step n x es y → n ≤ N) →
      (∀ es y, Machine.Trace.Runs step x es y → Ok y (h ++ es) ∨ Goal y (h ++ es)) →
      (∀ es y, Machine.Trace.Runs step x es y → ¬ Goal y (h ++ es) → ∃ e z, step y e z) →
      Leads step Ok Goal x h := by
  induction N with
  | zero =>
    intro x h bound safe progress
    rcases safe [] x (.refl x) with ok | goal
    · by_cases g : Goal x h
      · exact .done g
      · obtain ⟨e, z, s⟩ := progress [] x (.refl x) (by simpa using g)
        have := bound 1 e z (by simpa using RunsN.cons s (.refl z))
        omega
    · exact .done (by simpa using goal)
  | succ N ih =>
    intro x h bound safe progress
    by_cases g : Goal x h
    · exact .done g
    · rcases safe [] x (.refl x) with ok | goal
      · refine .step (by simpa using ok) (progress [] x (.refl x) (by simpa using g)) ?_
        intro e y s
        apply ih y (h ++ e)
        · intro n es z r
          have := bound (n + 1) (e ++ es) z (.cons s r)
          omega
        · intro es z r
          simpa [List.append_assoc] using safe (e ++ es) z (.cons s r)
        · intro es z r notGoal
          exact progress (e ++ es) z (.cons s r) (by simpa [List.append_assoc] using notGoal)
      · exact absurd (by simpa using goal) g

/-- The converse direction for final goals: `Leads` gives safety and progress (the bound is
`Leads.not_diverges`, a well-foundedness statement). -/
theorem leads_safety_progress {X : Type u} {E : Type v} {step : X → List E → X → Prop}
    {Ok Goal : X → List E → Prop} {x : X} {h : List E} (leads : Leads step Ok Goal x h)
    (final : ∀ z zs, Goal z zs → ∀ e w, ¬ step z e w) :
    (∀ es y, Machine.Trace.Runs step x es y → Ok y (h ++ es) ∨ Goal y (h ++ es)) ∧
      (∀ es y, Machine.Trace.Runs step x es y → ¬ Goal y (h ++ es) → ∃ e z, step y e z) :=
  ⟨fun _ _ run => leads.runs final run, fun _ _ run notGoal => leads.progress final run notGoal⟩

end Silmaril.Process.LPS.Problems.Sha256Cli
