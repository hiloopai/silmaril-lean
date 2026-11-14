module

public import Silmaril.Games.Abstract.Hiding.Defs

/-!
# Startup: phased games and startup-erased observation

A component first *starts* (instantiation: start-function code, import calls
made while starting, environment answers) and then either reports `ready` and
*runs*, or reports `fail r` and stops. `Game.phased S G R` is this game: a play
is a run of startup moves of `S`, optionally followed by `fail r`, or by
`ready` and then moves of `G`. The startup and run projections must be legal
in `S` and `G`. `ready` and `fail` are the component's (Proponent) moves.

Two observations of a model `T : TraceModel (phased S G R)`:

* **startup-sensitive**: `T` itself;
* **startup-erased**: `erased T = hide erase T`, the run moves only. Startup
  moves, `ready` and `fail` are hidden.

`startPart T` is the set of plays of `T` without run moves: what startup does,
including how it ends. `StartupIndep T` says that the run behaviour after a
successful startup does not depend on the startup history.

`Silmaril.Games.Abstract.Startup.Thms` proves that the two observations
determine each other exactly in the following sense: for startup-independent
models, `T = U` iff `startPart T = startPart U` and `erased T = erased U`. It
also gives counterexamples showing that neither hypothesis can be dropped:
erasure forgets startup failure, and it forgets how run behaviour depends on
startup inputs.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

universe u

/-- Moves of a phased game. -/
inductive PMove (S G : Game.{u}) (R : Type u) : Type u
  /-- A startup move. -/
  | start (m : S.Move)
  /-- Startup succeeded. -/
  | ready
  /-- Startup failed with `r`. -/
  | fail (r : R)
  /-- A run move. -/
  | run (m : G.Move)

namespace PMove

variable {S G : Game.{u}} {R : Type u}

/-- The startup move, if any. -/
def startOf : PMove S G R → Option S.Move
  | .start m => some m
  | _ => none

/-- The run move, if any. -/
def runOf : PMove S G R → Option G.Move
  | .run m => some m
  | _ => none

/-- A startup move. -/
def IsStart (x : PMove S G R) : Prop := ∃ m, x = .start m

/-- A run move. -/
def IsRun (x : PMove S G R) : Prop := ∃ m, x = .run m

/-- The shape of a phased play: startup moves, then nothing, `fail r`, or
`ready` followed by run moves. -/
def Shape (p : List (PMove S G R)) : Prop :=
  ∃ a b, p = a ++ b ∧ (∀ x ∈ a, IsStart x) ∧
    (b = [] ∨ (∃ r, b = [.fail r]) ∨ ∃ c, b = .ready :: c ∧ ∀ x ∈ c, IsRun x)

/-- Shapes are closed under prefixes. -/
theorem Shape.of_prefix {p q : List (PMove S G R)} (hq : Shape q) (h : p <+: q) : Shape p := by
  obtain ⟨a, b, rfl, ha, hb⟩ := hq
  obtain ⟨t, ht⟩ := h
  rcases List.append_eq_append_iff.1 ht with ⟨a', h₁, -⟩ | ⟨c', h₁, h₂⟩
  · exact ⟨p, [], by simp, fun x hx => ha x (h₁ ▸ List.mem_append_left _ hx), .inl rfl⟩
  · refine ⟨a, c', h₁, ha, ?_⟩
    rcases hb with rfl | ⟨r, rfl⟩ | ⟨c, rfl, hc⟩
    · obtain rfl : c' = [] := (by simpa using h₂ : c' = [] ∧ t = []).1
      exact .inl rfl
    · rcases c' with _ | ⟨x, _ | ⟨y, c'⟩⟩
      · exact .inl rfl
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h₂
        exact .inr (.inl ⟨r, by rw [h₂.1]⟩)
      · simp at h₂
    · rcases c' with _ | ⟨x, c'⟩
      · exact .inl rfl
      · simp only [List.cons_append, List.cons.injEq] at h₂
        exact .inr (.inr ⟨c', by rw [h₂.1], fun x hx => hc x (h₂.2 ▸ List.mem_append_left _ hx)⟩)

end PMove

/-- The phased game: startup in `S`, then failure with a reason in `R`, or
success followed by a run in `G`. -/
abbrev Game.phased (S G : Game.{u}) (R : Type u) : Game.{u} where
  Move := PMove S G R
  IsO
    | .start m => S.IsO m
    | .run m => G.IsO m
    | _ => False
  Legal := {p | PMove.Shape p ∧ p.filterMap PMove.startOf ∈ S.Legal ∧
    p.filterMap PMove.runOf ∈ G.Legal}
  nil_legal := ⟨⟨[], [], rfl, by simp, .inl rfl⟩, S.nil_legal, G.nil_legal⟩
  legal_of_prefix := fun ⟨h₁, h₂, h₃⟩ h =>
    ⟨h₁.of_prefix h, S.legal_of_prefix h₂ (h.filterMap _), G.legal_of_prefix h₃ (h.filterMap _)⟩

namespace Startup

variable {S G : Game.{u}} {R : Type u}

/-- Startup erasure: keep the run moves, hide the rest. -/
def erase : (Game.phased S G R).PHom G where
  map := PMove.runOf
  legal h := h.2.2
  isO {m n} h ho := by
    cases m <;> simp only [PMove.runOf, reduceCtorEq, Option.some.injEq] at h
    subst h; exact ho

/-- The startup-erased observation. -/
def erased (T : TraceModel (Game.phased S G R)) : TraceModel G := TraceModel.hide erase T

/-- The startup part: the plays without run moves. -/
def startPart (T : TraceModel (Game.phased S G R)) : Set (List (PMove S G R)) :=
  {p | p ∈ T ∧ ∀ x ∈ p, ¬ PMove.IsRun x}

/-- The play: startup moves `a`, then `ready`, then the run moves `g`. -/
def after (a : List (PMove S G R)) (g : List G.Move) : List (PMove S G R) :=
  a ++ PMove.ready :: g.map PMove.run

/-- Run behaviour after a successful startup does not depend on the startup
history. -/
def StartupIndep (T : TraceModel (Game.phased S G R)) : Prop :=
  ∀ (a a' : List (PMove S G R)) (g : List G.Move),
    (∀ x ∈ a, PMove.IsStart x) → (∀ x ∈ a', PMove.IsStart x) →
    a ++ [.ready] ∈ T → a' ++ [.ready] ∈ T →
    (after a g ∈ T ↔ after a' g ∈ T)

end Startup

end Silmaril.Games.Abstract
