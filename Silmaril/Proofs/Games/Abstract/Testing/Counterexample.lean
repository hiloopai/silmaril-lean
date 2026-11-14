module

public import Silmaril.Games.Abstract.Testing.Defs

/-!
# Equal traces, different must-observations

Two pairs of machines over the free game on two Proponent moves `a`, `b`:

* `a.b + a` against `a.b`: equal traces `[]`, `[a]`, `[a, b]`; after `a` the
  first may deadlock and refuse `b`, the second (deterministic) cannot;
* `a` followed by deadlock against `a` followed by silent divergence: equal
  traces `[]`, `[a]`; the first deadlocks and does not diverge after `a`, the
  second diverges and does not deadlock.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.Testing.Counterexample

open Silmaril.Games.Abstract Silmaril.Games.Abstract.Machine

/-- Two moves. -/
inductive Mv | a | b

/-- The free game on `Mv`, every move the component's. -/
def G : Game.{0} := Game.free Mv fun _ => False

/-- Four states. -/
inductive St | s0 | s1 | s2 | s3

/-- `a.b + a`. -/
inductive MayStop : St → Option G.Move → St → Prop
  | a₁ : MayStop .s0 (some Mv.a) .s1
  | b : MayStop .s1 (some Mv.b) .s2
  | a₂ : MayStop .s0 (some Mv.a) .s3

/-- `a.b`. -/
inductive AB : St → Option G.Move → St → Prop
  | a : AB .s0 (some Mv.a) .s1
  | b : AB .s1 (some Mv.b) .s2

/-- `a`, then nothing. -/
inductive Stop : St → Option G.Move → St → Prop
  | a : Stop .s0 (some Mv.a) .s1

/-- `a`, then silent divergence. -/
inductive Spin : St → Option G.Move → St → Prop
  | a : Spin .s0 (some Mv.a) .s1
  | tau : Spin .s1 none .s1

/-- The machine `a.b + a`. -/
def mayStop : Machine G := ⟨St, .s0, MayStop⟩
/-- The machine `a.b`. -/
def ab : Machine G := ⟨St, .s0, AB⟩
/-- The machine that stops after `a`. -/
def stop : Machine G := ⟨St, .s0, Stop⟩
/-- The machine that diverges after `a`. -/
def spin : Machine G := ⟨St, .s0, Spin⟩

theorem ab_lDet : ab.LDet where
  tau_free h := by cases h
  det h h' := by cases h <;> cases h' <;> rfl

/-- The traces of `a.b + a` and `a.b`. -/
def trAB : Set (List G.Move) := {s | s = [] ∨ s = [Mv.a] ∨ s = [Mv.a, Mv.b]}

theorem mayStop_traces : mayStop.traces = trAB := by
  ext s
  constructor
  · rintro ⟨z, h⟩
    rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
    · exact .inl rfl
    · cases h
    · cases h
      · rcases h₁ with _ | ⟨h, _⟩ | ⟨h, h₂⟩
        · exact .inr (.inl rfl)
        · cases h
        · cases h
          rcases h₂ with _ | ⟨h, _⟩ | ⟨h, _⟩
          · exact .inr (.inr rfl)
          · cases h
          · cases h
      · rcases h₁ with _ | ⟨h, _⟩ | ⟨h, _⟩
        · exact .inr (.inl rfl)
        · cases h
        · cases h
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, .nil _⟩
    · exact ⟨_, .vis MayStop.a₁ (.nil _)⟩
    · exact ⟨_, .vis MayStop.a₁ (.vis MayStop.b (.nil _))⟩

theorem ab_traces : ab.traces = trAB := by
  ext s
  constructor
  · rintro ⟨z, h⟩
    rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
    · exact .inl rfl
    · cases h
    · cases h
      rcases h₁ with _ | ⟨h, _⟩ | ⟨h, h₂⟩
      · exact .inr (.inl rfl)
      · cases h
      · cases h
        rcases h₂ with _ | ⟨h, _⟩ | ⟨h, _⟩
        · exact .inr (.inr rfl)
        · cases h
        · cases h
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, .nil _⟩
    · exact ⟨_, .vis AB.a (.nil _)⟩
    · exact ⟨_, .vis AB.a (.vis AB.b (.nil _))⟩

/-- After `a`, `a.b` is in state `s1`. -/
theorem ab_after_a {y : St} (h : ab.Run .s0 [Mv.a] y) : y = .s1 := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
  · cases h
  · cases h
    rcases h₁ with _ | ⟨h, _⟩
    · rfl
    · cases h

theorem mayStop_refuses : mayStop.Refuses [Mv.a] {Mv.b} :=
  ⟨.s3, .vis MayStop.a₂ (.nil _), ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩⟩

theorem ab_not_refuses : ¬ ab.Refuses [Mv.a] {Mv.b} := by
  rintro ⟨y, hy, -, h⟩
  obtain rfl := ab_after_a hy
  exact h Mv.b rfl .s2 AB.b

theorem mayStop_deadlocks : mayStop.Deadlocks [Mv.a] :=
  ⟨.s3, .vis MayStop.a₂ (.nil _), fun _ _ h => by cases h⟩

theorem ab_not_deadlocks : ¬ ab.Deadlocks [Mv.a] := by
  rintro ⟨y, hy, h⟩
  obtain rfl := ab_after_a hy
  exact h _ _ AB.b

/-- `a.b + a` and `a.b`: equal traces, different failures and deadlocks. -/
theorem refusal_counterexample :
    ∃ (G : Game.{0}) (M N : Machine G) (s : List G.Move) (X : Set G.Move),
      M.traces = N.traces ∧ N.LDet ∧ M.Refuses s X ∧ ¬ N.Refuses s X ∧
      M.Deadlocks s ∧ ¬ N.Deadlocks s :=
  ⟨G, mayStop, ab, [Mv.a], {Mv.b}, mayStop_traces.trans ab_traces.symm, ab_lDet,
    mayStop_refuses, ab_not_refuses, mayStop_deadlocks, ab_not_deadlocks⟩

/-! ## Deadlock against divergence -/

/-- From `s1`, `spin` only spins. -/
theorem spin_s1 {x z : spin.State} {t : List G.Move} (h : spin.Run x t z) (hx : x = .s1) :
    t = [] ∧ z = .s1 := by
  induction h with
  | nil => exact ⟨rfl, hx⟩
  | tau h _ ih =>
    subst hx
    cases h
    exact ih rfl
  | vis h _ _ =>
    subst hx
    cases h

theorem stop_s1 {z : St} {t : List G.Move} (h : stop.Run .s1 t z) : t = [] ∧ z = .s1 := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨rfl, rfl⟩
  · cases h
  · cases h

/-- The traces of `stop` and `spin`. -/
def trA : Set (List G.Move) := {s | s = [] ∨ s = [Mv.a]}

theorem stop_traces : stop.traces = trA := by
  ext s
  constructor
  · rintro ⟨z, h⟩
    rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
    · exact .inl rfl
    · cases h
    · cases h
      obtain ⟨rfl, -⟩ := stop_s1 h₁
      exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, .nil _⟩
    · exact ⟨_, .vis Stop.a (.nil _)⟩

theorem spin_traces : spin.traces = trA := by
  ext s
  constructor
  · rintro ⟨z, h⟩
    rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
    · exact .inl rfl
    · cases h
    · cases h
      obtain ⟨rfl, -⟩ := spin_s1 h₁ rfl
      exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, .nil _⟩
    · exact ⟨_, .vis Spin.a (.nil _)⟩

theorem stop_after_a {y : St} (h : stop.Run .s0 [Mv.a] y) : y = .s1 := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
  · cases h
  · cases h
    exact (stop_s1 h₁).2

theorem spin_after_a {y : St} (h : spin.Run .s0 [Mv.a] y) : y = .s1 := by
  rcases h with _ | ⟨h, _⟩ | ⟨h, h₁⟩
  · cases h
  · cases h
    exact (spin_s1 h₁ rfl).2

/-- `a` then deadlock, against `a` then divergence: equal traces; one deadlocks
and does not diverge, the other diverges and does not deadlock. -/
theorem divergence_counterexample :
    ∃ (G : Game.{0}) (M N : Machine G) (s : List G.Move),
      M.traces = N.traces ∧ M.Deadlocks s ∧ ¬ N.Deadlocks s ∧ N.Diverges s ∧ ¬ M.Diverges s := by
  refine ⟨G, stop, spin, [Mv.a], stop_traces.trans spin_traces.symm,
    ⟨.s1, .vis Stop.a (.nil _), fun _ _ h => by cases h⟩, ?_,
    ⟨.s1, .vis Spin.a (.nil _), fun _ => .s1, rfl, fun _ => Spin.tau⟩, ?_⟩
  · rintro ⟨y, hy, h⟩
    obtain rfl := spin_after_a hy
    exact h none .s1 Spin.tau
  · rintro ⟨y, hy, f, hf, h⟩
    obtain rfl := stop_after_a hy
    have := h 0
    rw [hf] at this
    cases this

end Silmaril.Proofs.Games.Abstract.Testing.Counterexample
