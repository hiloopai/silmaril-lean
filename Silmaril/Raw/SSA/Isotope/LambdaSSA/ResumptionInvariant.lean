module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ResumptionWorld

/-! # Relational invariants of actual instruction schedules

A world assertion may relate both controls, their captured continuations and
the current shared state. Per-CTA assertions below also see current shared
state, so another CTA's step must preserve them by interference reasoning.

Ghost lifting records a witness alongside every actual scheduler transition.
It neither adds machine steps nor assumes that a future evaluation succeeds.
All results concern supplied finite runs; they provide no progress or fairness.
-/

@[expose] public section
universe u v w x y
namespace Silmaril.Isotope.LambdaSSA.Resumption.World
open Semantics
variable {CTA : Type x} {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : CTA → Φ → Value α → σ → Value α → σ → Prop}

/-- An arbitrary relational predicate, preserved by every actual scheduled
step. Unlike the product `Satisfies`, it may relate all controls to shared state. -/
def Invariant (instr : CTA → Φ → Value α → σ → Value α → σ → Prop)
    (assertion : World CTA α Φ σ → Prop) : Prop :=
  ∀ cta before after, Step instr cta before after → assertion before → assertion after

theorem Run.preserves_world {schedule : List CTA} {before after : World CTA α Φ σ}
    (run : Run instr schedule before after) (assertion : World CTA α Φ σ → Prop)
    (advance : ∀ cta ∈ schedule, ∀ first last, Step instr cta first last → assertion first → assertion last)
    (initial : assertion before) : assertion after :=
  SequentialTrace.preserves run assertion advance initial

theorem Invariant.run {assertion : World CTA α Φ σ → Prop}
    (closed : Invariant instr assertion) {schedule : List CTA} {before after : World CTA α Φ σ}
    (run : Run instr schedule before after) (initial : assertion before) : assertion after :=
  run.preserves_world assertion (fun cta _ => closed cta) initial

/-- An invariant holds at the actual intermediate world of any prefix. The
two subruns are extracted from the supplied chronological execution. -/
theorem Invariant.prefix {assertion : World CTA α Φ σ → Prop}
    (closed : Invariant instr assertion) {front suffix : List CTA} {before after : World CTA α Φ σ}
    (run : Run instr (front ++ suffix) before after) (initial : assertion before) :
    ∃ middle, Run instr front before middle ∧ assertion middle ∧ Run instr suffix middle after := by
  obtain ⟨middle, first, last⟩ := SequentialTrace.append_iff.mp run
  exact ⟨middle, first, closed.run first initial, last⟩

theorem Invariant.and {first second : World CTA α Φ σ → Prop}
    (one : Invariant instr first) (two : Invariant instr second) :
    Invariant instr (fun world => first world ∧ second world) :=
  fun cta before after step initial => ⟨one cta before after step initial.1, two cta before after step initial.2⟩

/-- Every local assertion is evaluated against the *current* shared state.
For instance it may describe the data referenced by a suspended request. -/
def Relational (world : World CTA α Φ σ) (shared : σ → Prop)
    (assertion : CTA → Control α Φ → σ → Prop) : Prop :=
  shared world.shared ∧ ∀ cta, assertion cta (world.control cta) world.shared

theorem Relational.mono {world : World CTA α Φ σ}
    {shared shared' : σ → Prop} {assertion assertion' : CTA → Control α Φ → σ → Prop}
    (holds : world.Relational shared assertion)
    (global : ∀ state, shared state → shared' state)
    (localRule : ∀ cta control state, shared state → assertion cta control state → assertion' cta control state) :
    world.Relational shared' assertion' :=
  ⟨global _ holds.1, fun cta => localRule cta _ _ holds.1 (holds.2 cta)⟩

/-- Recover the earlier static product only when the assertion truly ignores
shared state; relational clients do not receive free interference closure. -/
theorem relational_static (world : World CTA α Φ σ) (shared : σ → Prop)
    (assertion : CTA → Control α Φ → Prop) :
    world.Relational shared (fun cta control _ => assertion cta control) ↔ world.Satisfies shared assertion :=
  Iff.rfl

/-- Extract per-CTA results only at controls actually shown to be terminal.
The local extraction may use both current shared facts and its control relation. -/
theorem Relational.terminal {world : World CTA α Φ σ} {shared : σ → Prop}
    {assertion : CTA → Control α Φ → σ → Prop}
    (holds : world.Relational shared assertion)
    (terminal : CTA → Control α Φ → Prop) (post : CTA → σ → Prop)
    (stopped : ∀ cta, terminal cta (world.control cta))
    (extract : ∀ cta control state, shared state → assertion cta control state →
      terminal cta control → post cta state) :
    shared world.shared ∧ ∀ cta, post cta world.shared :=
  ⟨holds.1, fun cta => extract cta _ _ holds.1 (holds.2 cta) (stopped cta)⟩

section Ghost
variable {Ghost : Type y}

/-- A ghost update annotates one existing scheduler step. It never changes
the source instruction relation or forgets either actual machine endpoint. -/
def GhostStep (instr : CTA → Φ → Value α → σ → Value α → σ → Prop)
    (update : CTA → Ghost → World CTA α Φ σ → Ghost → World CTA α Φ σ → Prop)
    (cta : CTA) (before after : Ghost × World CTA α Φ σ) : Prop :=
  Step instr cta before.2 after.2 ∧ update cta before.1 before.2 after.1 after.2

theorem ghost_run_project
    {update : CTA → Ghost → World CTA α Φ σ → Ghost → World CTA α Φ σ → Prop}
    {schedule : List CTA} {before after : Ghost × World CTA α Φ σ}
    (run : SequentialTrace (GhostStep instr update) schedule before after) :
    Run instr schedule before.2 after.2 := by
  induction run with
  | nil => exact .nil _
  | cons head _ ih => exact .cons head.1 ih

/-- Construct an invariant witness at every real step. The update obligation
is local to that step and initial ghost, not a promised successful suffix. -/
theorem Run.lift_ghost
    {update : CTA → Ghost → World CTA α Φ σ → Ghost → World CTA α Φ σ → Prop}
    {schedule : List CTA} {before after : World CTA α Φ σ}
    (run : Run instr schedule before after) (assertion : Ghost → World CTA α Φ σ → Prop)
    (advance : ∀ cta ∈ schedule, ∀ first last ghost, Step instr cta first last → assertion ghost first →
      ∃ next, update cta ghost first next last ∧ assertion next last)
    {ghost : Ghost} (initial : assertion ghost before) :
    ∃ final, SequentialTrace (GhostStep instr update) schedule (ghost, before) (final, after) ∧
      assertion final after := by
  induction run generalizing ghost with
  | nil => exact ⟨ghost, .nil _, initial⟩
  | @cons cta rest before middle after head tail ih =>
      obtain ⟨next, updated, holds⟩ := advance cta (List.mem_cons_self ..) before middle ghost head initial
      obtain ⟨final, remaining, finalHolds⟩ := ih
        (fun actor member => advance actor (List.mem_cons_of_mem _ member)) holds
      exact ⟨final, .cons ⟨head, updated⟩ remaining, finalHolds⟩

end Ghost
end Silmaril.Isotope.LambdaSSA.Resumption.World
